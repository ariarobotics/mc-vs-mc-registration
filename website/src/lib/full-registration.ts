import type { PointMatch } from "./point-registration.ts";
export interface PairwiseDiscrepancies {
    count: number;
    gaps: Float64Array;
    roundoff: Float64Array;
}
export interface FullConsistencyGraph {
    count: number;
    edges: Uint32Array;
    edgeCount: number;
    adjacency: Uint32Array[];
    degrees: Uint32Array;
}
export interface CliqueSearchOptions {
    seed?: readonly number[];
    knownMaximum?: number;
    timeBudgetMs?: number;
    maxNodes?: number;
}
export interface BoundedClique {
    indices: number[];
    lowerBound: number;
    upperBound: number;
    certified: boolean;
    nodes: number;
    timedOut: boolean;
}
export function buildPairwiseDiscrepancies(matches: readonly PointMatch[]): PairwiseDiscrepancies {
    for (const match of matches)
        for (const point of [match.source, match.target]) {
            if (point.length !== 3 || !point.every(Number.isFinite))
                throw new Error("Every endpoint must have three finite coordinates");
        }
    const count = matches.length, pairs = count * (count - 1) / 2;
    const gaps = new Float64Array(pairs), roundoff = new Float64Array(pairs);
    let pair = 0;
    for (let a = 0; a < count; a++)
        for (let b = a + 1; b < count; b++) {
            const first = matches[a]!, second = matches[b]!;
            const source = Math.hypot(first.source[0]! - second.source[0]!, first.source[1]! - second.source[1]!, first.source[2]! - second.source[2]!);
            const target = Math.hypot(first.target[0]! - second.target[0]!, first.target[1]! - second.target[1]!, first.target[2]! - second.target[2]!);
            if (!Number.isFinite(source) || !Number.isFinite(target))
                throw new Error("Point distances must be finite");
            gaps[pair] = Math.abs(source - target);
            roundoff[pair++] = 1e-10 * Math.max(1, source, target);
        }
    return { count, gaps, roundoff };
}
export function thresholdGraph(cache: PairwiseDiscrepancies, epsilon: number): FullConsistencyGraph {
    if (!Number.isFinite(epsilon) || epsilon < 0)
        throw new Error("The graph threshold must be finite and nonnegative");
    const { count, gaps, roundoff } = cache, words = Math.ceil(count / 32);
    if (gaps.length !== count * (count - 1) / 2 || roundoff.length !== gaps.length)
        throw new Error("Invalid pairwise discrepancy cache");
    const adjacency = Array.from({ length: count }, () => new Uint32Array(words)), degrees = new Uint32Array(count);
    let pair = 0, edgeCount = 0;
    const epsilonRoundoff = 1e-10 * epsilon;
    for (let a = 0; a < count; a++)
        for (let b = a + 1; b < count; b++, pair++) {
            if (gaps[pair]! > epsilon + Math.max(roundoff[pair]!, epsilonRoundoff))
                continue;
            adjacency[a]![b >>> 5] = adjacency[a]![b >>> 5]! | (1 << (b & 31));
            adjacency[b]![a >>> 5] = adjacency[b]![a >>> 5]! | (1 << (a & 31));
            degrees[a]++;
            degrees[b]++;
            edgeCount++;
        }
    const edges = new Uint32Array(2 * edgeCount);
    let entry = 0;
    for (let a = 0; a < count; a++)
        for (let word = a >>> 5; word < words; word++) {
            let neighbors = adjacency[a]![word]!;
            if (word === (a >>> 5))
                neighbors &= (a & 31) === 31 ? 0 : (0xffffffff << ((a & 31) + 1));
            while (neighbors) {
                const bit = neighbors & -neighbors, b = 32 * word + 31 - Math.clz32(bit);
                edges[entry++] = a;
                edges[entry++] = b;
                neighbors = (neighbors & (neighbors - 1)) >>> 0;
            }
        }
    return { count, edges, edgeCount, adjacency, degrees };
}
export function graphHasEdge(graph: Pick<FullConsistencyGraph, "adjacency">, a: number, b: number): boolean {
    return !!(graph.adjacency[a]?.[b >>> 5] && (graph.adjacency[a]![b >>> 5]! & (1 << (b & 31))));
}
function candidatesFor(count: number): Uint32Array {
    const bits = new Uint32Array(Math.ceil(count / 32)).fill(0xffffffff);
    if (count % 32)
        bits[bits.length - 1] = 2 ** (count % 32) - 1;
    return bits;
}
function firstVertex(bits: Uint32Array): number {
    for (let word = 0; word < bits.length; word++) {
        const value = bits[word]!;
        if (value)
            return 32 * word + 31 - Math.clz32(value & -value);
    }
    return -1;
}
const removeVertex = (bits: Uint32Array, vertex: number): void => { bits[vertex >>> 5] = bits[vertex >>> 5]! & ~(1 << (vertex & 31)); };
const intersect = (bits: Uint32Array, row: Uint32Array): Uint32Array => bits.map((word, i) => word & row[i]!);
export function boundedMaximumClique(graph: FullConsistencyGraph, options: CliqueSearchOptions = {}): BoundedClique {
    const { count, adjacency, degrees } = graph;
    const started = performance.now(), milliseconds = options.timeBudgetMs ?? 20, maximumNodes = options.maxNodes ?? 10000;
    if (!Number.isFinite(milliseconds) || milliseconds < 0 || !Number.isInteger(maximumNodes) || maximumNodes < 0)
        throw new Error("Clique search budgets must be finite and nonnegative");
    const deadline = started + milliseconds;
    let nodes = 0, timedOut = false;
    const expired = (): boolean => {
        if (performance.now() < deadline)
            return false;
        timedOut = true;
        return true;
    };
    const seed = [...new Set(options.seed ?? [])];
    if (seed.some(vertex => !Number.isInteger(vertex) || vertex < 0 || vertex >= count))
        throw new Error("Clique seed contains an invalid vertex");
    for (let a = 0; a < seed.length; a++)
        for (let b = a + 1; b < seed.length; b++) {
            if (!graphHasEdge(graph, seed[a]!, seed[b]!))
                throw new Error("Clique seed is not a clique in the current graph");
        }
    let best = seed.length ? seed : count ? [0] : [];
    const known = options.knownMaximum;
    if (known !== undefined && (!Number.isInteger(known) || known < best.length || known > count))
        throw new Error("The saved maximum-clique bound is invalid");
    let upperBound = count ? Math.min(count, 1 + degrees.reduce((max, value) => Math.max(max, value), 0)) : 0;
    if (known !== undefined)
        upperBound = Math.min(upperBound, known);
    const result = (): BoundedClique => {
        if (known !== undefined && best.length > known)
            throw new Error("The saved maximum-clique bound contradicts the current graph");
        return { indices: [...best].sort((a, b) => a - b), lowerBound: best.length, upperBound, certified: best.length === upperBound, nodes, timedOut };
    };
    if (best.length === upperBound)
        return result();
    if (graph.edgeCount === count * (count - 1) / 2) {
        best = Array.from({ length: count }, (_, vertex) => vertex);
        upperBound = count;
        if (known !== undefined && known < count)
            throw new Error("The saved maximum-clique bound contradicts the current graph");
        return result();
    }
    if (expired())
        return result();
    function colorSort(candidates: Uint32Array): {
        vertices: number[];
        bounds: number[];
    } | undefined {
        const remaining = candidates.slice(), vertices: number[] = [], bounds: number[] = [];
        let color = 0;
        while (firstVertex(remaining) >= 0) {
            color++;
            const available = remaining.slice();
            let vertex: number;
            while ((vertex = firstVertex(available)) >= 0) {
                vertices.push(vertex);
                bounds.push(color);
                removeVertex(remaining, vertex);
                removeVertex(available, vertex);
                const neighbors = adjacency[vertex]!;
                for (let word = 0; word < available.length; word++)
                    available[word] = available[word]! & ~neighbors[word]!;
                if ((vertices.length & 63) === 0 && expired())
                    return;
            }
        }
        return { vertices, bounds };
    }
    const all = candidatesFor(count), rootColors = colorSort(all);
    if (!rootColors)
        return result();
    upperBound = Math.min(upperBound, rootColors.bounds.at(-1) ?? 0);
    if (best.length === upperBound)
        return result();
    const starts = Array.from({ length: count }, (_, vertex) => vertex).sort((a, b) => degrees[b]! - degrees[a]! || a - b).slice(0, 12);
    for (const start of starts) {
        if (expired())
            return result();
        const selected = [start];
        let candidates: Uint32Array = adjacency[start]!.slice();
        while (firstVertex(candidates) >= 0) {
            let next = -1, greatestDegree = -1;
            for (let word = 0; word < candidates.length; word++) {
                let mask = candidates[word]!;
                while (mask) {
                    const vertex = word * 32 + 31 - Math.clz32(mask & -mask);
                    if (degrees[vertex]! > greatestDegree) {
                        next = vertex;
                        greatestDegree = degrees[vertex]!;
                    }
                    mask = (mask & (mask - 1)) >>> 0;
                }
            }
            selected.push(next);
            candidates = intersect(candidates, adjacency[next]!);
            if (selected.length > best.length)
                best = [...selected];
            if (best.length >= upperBound) {
                upperBound = best.length;
                return result();
            }
            if ((selected.length & 15) === 0 && expired())
                return result();
        }
    }
    function expand(selected: number[], candidates: Uint32Array, suppliedColors?: {
        vertices: number[];
        bounds: number[];
    }): boolean {
        if (nodes >= maximumNodes || expired())
            return false;
        nodes++;
        const colored = suppliedColors ?? colorSort(candidates);
        if (!colored)
            return false;
        for (let index = colored.vertices.length - 1; index >= 0; index--) {
            if (selected.length + colored.bounds[index]! <= best.length)
                return true;
            if (expired())
                return false;
            const vertex = colored.vertices[index]!, next = [...selected, vertex];
            if (next.length > best.length)
                best = next;
            if (best.length >= upperBound)
                return true;
            const neighbors = intersect(candidates, adjacency[vertex]!);
            if (firstVertex(neighbors) >= 0 && !expand(next, neighbors))
                return false;
            removeVertex(candidates, vertex);
        }
        return true;
    }
    if (expand([], all, rootColors) || best.length === upperBound)
        upperBound = best.length;
    return result();
}
