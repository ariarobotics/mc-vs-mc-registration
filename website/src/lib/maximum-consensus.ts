import { affineLowerBound, applyTransform, solveMinimax, type MinimaxSolution } from "./rigid-minimax.ts";
import { pointDistance, type Point3 } from "./minimax-geometry.ts";
export interface ConsensusOptions {
    dimension: 2 | 3;
    proper?: boolean;
    initialTransform?: readonly number[];
    maxNodes?: number;
    maxSubsets?: number;
}
export interface RigidConsensus {
    transform: readonly number[];
    indices: number[];
    count: number;
    upperBound: number;
    certified: boolean;
    evaluatedSubsets: number;
}
const subsetCache = new Map<string, MinimaxSolution>();
const bits = (mask: number): number => {
    let count = 0;
    while (mask) {
        mask &= mask - 1;
        count++;
    }
    return count;
};
export function rigidConsensus(source: readonly Point3[], target: readonly Point3[], tau: number, options: ConsensusOptions): RigidConsensus {
    const n = source.length;
    if (n !== target.length || n === 0 || n > 12)
        throw new Error("Consensus requires one to twelve correspondence pairs");
    if (!Number.isFinite(tau) || tau < 0)
        throw new Error("Point tolerance must be finite and nonnegative");
    for (const point of [...source, ...target]) {
        if (point.length !== 3 || !point.every(Number.isFinite))
            throw new Error("Endpoints must contain three finite coordinates");
        if (options.dimension === 2 && Math.abs(point[2]) > 1e-10)
            throw new Error("A planar consensus problem needs planar endpoints");
    }
    const maxNodes = Math.max(0, Math.min(16384, Math.round(options.maxNodes ?? (options.dimension === 2 ? 48 : 24))));
    const maxSubsets = Math.max(0, Math.min(4096, Math.round(options.maxSubsets ?? 64)));
    const magnitude = Math.max(1, ...source.flat().map(Math.abs), ...target.flat().map(Math.abs));
    const roundoff = 2e-10 * magnitude;
    const feasibilityTolerance = 1e-9 * Math.max(1, tau);
    const feasible = (transform: readonly number[]): number[] => source.map((_, i) => i).filter(i => pointDistance(applyTransform(transform, source[i]!), target[i]!) <= tau + feasibilityTolerance);
    let transform: readonly number[] = [1, 0, 0, target[0]![0] - source[0]![0], 0, 1, 0, target[0]![1] - source[0]![1], 0, 0, 1, target[0]![2] - source[0]![2], 0, 0, 0, 1];
    let indices = feasible(transform);
    const inspectPose = (candidate: readonly number[]): void => {
        const inliers = feasible(candidate);
        if (inliers.length > indices.length) {
            indices = inliers;
            transform = candidate;
        }
    };
    const forbidden: number[] = [];
    for (let i = 0; i < n; i++)
        for (let j = i + 1; j < n; j++) {
            const gap = Math.abs(pointDistance(source[i]!, source[j]!) - pointDistance(target[i]!, target[j]!));
            if (gap / 2 > tau + roundoff)
                forbidden.push((1 << i) | (1 << j));
        }
    const inspectAffine = (members: number[], start: number): void => {
        if (members.length >= 3) {
            const mask = members.reduce((value, i) => value | (1 << i), 0);
            if (forbidden.some(obstruction => (mask & obstruction) === obstruction))
                return;
            const lower = affineLowerBound(members.map(i => source[i]!), members.map(i => target[i]!), options.dimension);
            if (lower > tau + roundoff) {
                forbidden.push(mask);
                return;
            }
        }
        if (members.length === options.dimension + 2)
            return;
        for (let i = start; i < n; i++)
            inspectAffine([...members, i], i + 1);
    };
    inspectAffine([], 0);
    const candidates: {
        mask: number;
        count: number;
    }[] = [];
    for (let mask = 1; mask < (1 << n); mask++) {
        const count = bits(mask);
        if (count <= indices.length || forbidden.some(obstruction => (mask & obstruction) === obstruction))
            continue;
        candidates.push({ mask, count });
    }
    candidates.sort((a, b) => b.count - a.count || a.mask - b.mask);
    let unresolved = indices.length, evaluatedSubsets = 0;
    for (const candidate of candidates) {
        if (candidate.count <= indices.length)
            break;
        if (forbidden.some(obstruction => (candidate.mask & obstruction) === obstruction))
            continue;
        if (evaluatedSubsets >= maxSubsets) {
            unresolved = Math.max(unresolved, candidate.count);
            break;
        }
        const members = source.map((_, i) => i).filter(i => candidate.mask & (1 << i));
        const p = members.map(i => source[i]!), q = members.map(i => target[i]!);
        const key = JSON.stringify([options.dimension, !!options.proper, maxNodes, p, q]);
        let result = subsetCache.get(key);
        if (!result) {
            result = solveMinimax(p, q, {
                dimension: options.dimension, allowReflections: !options.proper, maxNodes,
                tolerance: options.dimension === 2 ? .0002 : .0005,
                initialTransform: options.initialTransform,
            });
            if (subsetCache.size >= 512)
                subsetCache.delete(subsetCache.keys().next().value!);
            subsetCache.set(key, result);
        }
        evaluatedSubsets++;
        inspectPose(result.transform);
        if (result.lowerBound > tau + roundoff)
            forbidden.push(candidate.mask);
        else if (result.upperBound > tau + feasibilityTolerance)
            unresolved = Math.max(unresolved, candidate.count);
    }
    const upperBound = Math.max(indices.length, unresolved);
    return { transform, indices, count: indices.length, upperBound, certified: indices.length === upperBound, evaluatedSubsets };
}
