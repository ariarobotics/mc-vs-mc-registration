import { minimumEnclosingBall, pointDistance, pointDot, pointSubtract, type Point3 } from "./minimax-geometry.ts";
import { fitPointPose } from "./point-registration.ts";
export type { Point3 } from "./minimax-geometry.ts";
export interface MinimaxOptions {
    mode?: "translation" | "rigid";
    dimension?: 2 | 3;
    allowReflections?: boolean;
    tolerance?: number;
    maxNodes?: number;
    initialTransform?: readonly number[];
}
export interface MinimaxSolution {
    transform: number[];
    fit: Point3[];
    residuals: number[];
    radius: number;
    lowerBound: number;
    upperBound: number;
    certified: boolean;
    tolerance: number;
    evaluations: number;
    dimension: 2 | 3;
    branch: "proper" | "improper" | "translation";
}
type Matrix = number[];
type Branch = "proper" | "improper";
interface Evaluation {
    matrix: Matrix;
    center: Point3;
    radius: number;
}
interface Data {
    source: readonly Point3[];
    target: readonly Point3[];
    p: Point3[];
    q: Point3[];
    sourceCenter: Point3;
    targetCenter: Point3;
    sourceRadius: number;
    floor: number;
    roundoff: number;
}
const IDENTITY: Matrix = [1, 0, 0, 0, 1, 0, 0, 0, 1];
const vectorNorm = (p: Point3): number => Math.hypot(...p);
const matVec = (r: readonly number[], p: Point3): Point3 => [r[0]! * p[0] + r[1]! * p[1] + r[2]! * p[2], r[3]! * p[0] + r[4]! * p[1] + r[5]! * p[2], r[6]! * p[0] + r[7]! * p[1] + r[8]! * p[2]];
const multiply = (a: readonly number[], b: readonly number[]): Matrix => Array.from({ length: 9 }, (_, i) => {
    const row = Math.floor(i / 3), col = i % 3;
    return a[3 * row]! * b[col]! + a[3 * row + 1]! * b[col + 3]! + a[3 * row + 2]! * b[col + 6]!;
});
const reflectX = (r: readonly number[]): Matrix => r.map((value, i) => i % 3 === 0 ? -value : value);
const planarRotation = (angle: number): Matrix => [Math.cos(angle), -Math.sin(angle), 0, Math.sin(angle), Math.cos(angle), 0, 0, 0, 1];
const determinant = (r: readonly number[]): number => r[0]! * (r[4]! * r[8]! - r[5]! * r[7]!) - r[1]! * (r[3]! * r[8]! - r[5]! * r[6]!) + r[2]! * (r[3]! * r[7]! - r[4]! * r[6]!);
export const applyTransform = (t: readonly number[], p: Point3): Point3 => [t[0]! * p[0] + t[1]! * p[1] + t[2]! * p[2] + t[3]!, t[4]! * p[0] + t[5]! * p[1] + t[6]! * p[2] + t[7]!, t[8]! * p[0] + t[9]! * p[1] + t[10]! * p[2] + t[11]!];
function rotationVector(v: Point3): Matrix {
    const angle = vectorNorm(v);
    if (angle < 1e-15)
        return [...IDENTITY];
    const [x, y, z] = v.map(value => value / angle), c = Math.cos(angle), s = Math.sin(angle), h = 1 - c;
    return [c + x! * x! * h, x! * y! * h - z! * s, x! * z! * h + y! * s, y! * x! * h + z! * s, c + y! * y! * h, y! * z! * h - x! * s, z! * x! * h - y! * s, z! * y! * h + x! * s, c + z! * z! * h];
}
const average = (points: readonly Point3[]): Point3 => points.length ? [0, 1, 2].map(axis => points[0]![axis]! + points.reduce((sum, point) => sum + (point[axis]! - points[0]![axis]!) / points.length, 0)) as unknown as Point3 : [0, 0, 0];
export function affineLowerBound(p: readonly Point3[], q: readonly Point3[], dimension: 2 | 3): number {
    let lower = 0;
    function inspect(indices: number[], coefficients: number[]): void {
        coefficients[coefficients.length - 1] = -coefficients.slice(0, -1).reduce((sum, value) => sum + value, 0);
        const l1 = coefficients.reduce((sum, value) => sum + Math.abs(value), 0);
        if (l1 < 1e-14)
            return;
        const combination = (points: readonly Point3[]): Point3 => [0, 1, 2].map(axis => indices.reduce((sum, index, i) => sum + coefficients[i]! * points[index]![axis]!, 0)) as unknown as Point3;
        lower = Math.max(lower, Math.abs(vectorNorm(combination(p)) - vectorNorm(combination(q))) / l1);
    }
    function circuits(indices: number[], points: readonly Point3[]): void {
        const matrix = [indices.map(() => 1), ...Array.from({ length: dimension }, (_, axis) => indices.map(index => points[index]![axis]!))];
        matrix.forEach(row => { const scale = Math.max(1, ...row.map(Math.abs)); row.forEach((value, i) => { row[i] = value / scale; }); });
        const pivots: number[] = [];
        let row = 0;
        for (let col = 0; col < indices.length && row < matrix.length; col++) {
            let selected = row;
            for (let j = row + 1; j < matrix.length; j++)
                if (Math.abs(matrix[j]![col]!) > Math.abs(matrix[selected]![col]!))
                    selected = j;
            if (Math.abs(matrix[selected]![col]!) < 1e-10)
                continue;
            [matrix[row], matrix[selected]] = [matrix[selected]!, matrix[row]!];
            const divisor = matrix[row]![col]!;
            matrix[row] = matrix[row]!.map(value => value / divisor);
            for (let j = 0; j < matrix.length; j++)
                if (j !== row) {
                    const factor = matrix[j]![col]!;
                    matrix[j] = matrix[j]!.map((value, k) => value - factor * matrix[row]![k]!);
                }
            pivots.push(col);
            row++;
        }
        for (let free = 0; free < indices.length; free++)
            if (!pivots.includes(free)) {
                const coefficients = Array<number>(indices.length).fill(0);
                coefficients[free] = 1;
                pivots.forEach((pivot, j) => { coefficients[pivot] = -matrix[j]![free]!; });
                inspect(indices, coefficients);
            }
    }
    function subsets(indices: number[], start: number): void {
        if (indices.length >= 3) {
            if (indices.length === 3)
                for (let center = 0; center < 3; center++)
                    inspect(indices, indices.map((_, i) => i === center ? -1 : 0.5));
            circuits(indices, p);
            circuits(indices, q);
        }
        if (indices.length === dimension + 2)
            return;
        for (let i = start; i < p.length; i++)
            subsets([...indices, i], i + 1);
    }
    subsets([], 0);
    return lower;
}
function prepare(source: readonly Point3[], target: readonly Point3[], dimension: 2 | 3): Data {
    const sourceCenter = minimumEnclosingBall(source).center, targetCenter = average(target);
    const p = source.map(point => pointSubtract(point, sourceCenter)), q = target.map(point => pointSubtract(point, targetCenter));
    const sourceRadius = Math.max(0, ...p.map(vectorNorm));
    const roundoff = 2e-10 * Math.max(1, sourceRadius, ...q.map(vectorNorm));
    let pairBound = 0;
    for (let i = 0; i < p.length; i++)
        for (let j = i + 1; j < p.length; j++)
            pairBound = Math.max(pairBound, Math.abs(pointDistance(p[i]!, p[j]!) - pointDistance(q[i]!, q[j]!)) / 2);
    return { source, target, p, q, sourceCenter, targetCenter, sourceRadius, floor: Math.max(0, pairBound, affineLowerBound(p, q, dimension)) - roundoff, roundoff };
}
class MinHeap<T extends {
    lower: number;
}> {
    private nodes: T[] = [];
    get length(): number { return this.nodes.length; }
    peek(): T | undefined { return this.nodes[0]; }
    push(value: T): void {
        let i = this.nodes.length;
        this.nodes.push(value);
        while (i > 0) {
            const parent = (i - 1) >> 1;
            if (this.nodes[parent]!.lower <= value.lower)
                break;
            this.nodes[i] = this.nodes[parent]!;
            i = parent;
        }
        this.nodes[i] = value;
    }
    pop(): T | undefined {
        const first = this.nodes[0], last = this.nodes.pop();
        if (!first || !last || this.nodes.length === 0)
            return first;
        let i = 0;
        while (2 * i + 1 < this.nodes.length) {
            let child = 2 * i + 1;
            if (child + 1 < this.nodes.length && this.nodes[child + 1]!.lower < this.nodes[child]!.lower)
                child++;
            if (last.lower <= this.nodes[child]!.lower)
                break;
            this.nodes[i] = this.nodes[child]!;
            i = child;
        }
        this.nodes[i] = last;
        return first;
    }
}
interface BranchResult {
    best: Evaluation;
    lower: number;
    evaluations: number;
    branch: Branch;
}
function warmStart(options: MinimaxOptions, branch: Branch): Matrix | undefined {
    const t = options.initialTransform;
    if (!t || t.length !== 16 || !t.every(Number.isFinite))
        return;
    const matrix = [t[0]!, t[1]!, t[2]!, t[4]!, t[5]!, t[6]!, t[8]!, t[9]!, t[10]!];
    if (Math.abs(Math.abs(determinant(matrix)) - 1) > 1e-5 || (determinant(matrix) < 0) !== (branch === "improper"))
        return;
    for (let row = 0; row < 3; row++)
        for (let other = row; other < 3; other++) {
            const product = matrix[3 * row]! * matrix[3 * other]! + matrix[3 * row + 1]! * matrix[3 * other + 1]! + matrix[3 * row + 2]! * matrix[3 * other + 2]!;
            if (Math.abs(product - (row === other ? 1 : 0)) > 1e-5)
                return;
        }
    return branch === "improper" ? reflectX(matrix) : matrix;
}
function solveBranch(data: Data, dimension: 2 | 3, branch: Branch, options: MinimaxOptions, tolerance: number, maxNodes: number): BranchResult {
    const p = branch === "improper" ? data.p.map(point => [-point[0], point[1], point[2]] as Point3) : data.p;
    let evaluations = 0;
    const evaluate = (matrix: Matrix): Evaluation => {
        evaluations++;
        const votes = p.map((point, i) => pointSubtract(data.q[i]!, matVec(matrix, point)));
        const ball = minimumEnclosingBall(votes);
        return { matrix, center: ball.center, radius: ball.radius };
    };
    let leastSquares: Matrix, rms: number;
    if (dimension === 2) {
        const pc = average(p), qc = average(data.q);
        let a = 0, b = 0;
        p.forEach((point, i) => {
            const x = pointSubtract(point, pc), y = pointSubtract(data.q[i]!, qc);
            a += x[0] * y[0] + x[1] * y[1];
            b += x[0] * y[1] - x[1] * y[0];
        });
        leastSquares = planarRotation(Math.atan2(b, a));
        rms = Math.hypot(...p.map((point, i) => vectorNorm(pointSubtract(matVec(leastSquares, pointSubtract(point, pc)), pointSubtract(data.q[i]!, qc))))) / Math.sqrt(Math.max(1, p.length));
    }
    else {
        const registration = fitPointPose(p.map((point, i) => ({ source: point, target: data.q[i]! })));
        const t = registration.transform;
        leastSquares = [t[0]!, t[1]!, t[2]!, t[4]!, t[5]!, t[6]!, t[8]!, t[9]!, t[10]!];
        rms = registration.fitError;
    }
    const floor = Math.max(0, data.floor, rms - data.roundoff);
    let best = evaluate(leastSquares);
    let initial = warmStart(options, branch);
    if (dimension === 2 && initial) {
        initial = Math.abs(initial[2]!) + Math.abs(initial[5]!) + Math.abs(initial[6]!) + Math.abs(initial[7]!) + Math.abs(initial[8]! - 1) <= 1e-5
            ? planarRotation(Math.atan2(initial[3]!, initial[0]!)) : undefined;
    }
    const seeds = dimension === 2 ? [planarRotation(0), planarRotation(Math.PI), planarRotation(Math.PI / 2), planarRotation(-Math.PI / 2)] : [IDENTITY, rotationVector([Math.PI, 0, 0]), rotationVector([0, Math.PI, 0]), rotationVector([0, 0, Math.PI])];
    if (initial)
        seeds.push(initial);
    for (const seed of seeds) {
        const value = evaluate(seed);
        if (value.radius < best.radius)
            best = value;
    }
    if (best.radius - floor <= tolerance)
        return { best, lower: Math.min(best.radius, floor), evaluations, branch };
    const pairData: {
        p: Point3;
        q: Point3;
        a: number;
        b: number;
        preferred: number;
    }[] = [];
    for (let i = 0; i < p.length; i++)
        for (let j = i + 1; j < p.length; j++) {
            const dp = pointSubtract(p[i]!, p[j]!), dq = pointSubtract(data.q[i]!, data.q[j]!);
            pairData.push({ p: dp, q: dq, a: vectorNorm(dp), b: vectorNorm(dq), preferred: Math.atan2(dq[1], dq[0]) - Math.atan2(dp[1], dp[0]) });
        }
    const gapAtAngle = (a: number, b: number, angle: number): number => Math.hypot(a - b, 2 * Math.sqrt(a * b) * Math.sin(angle / 2));
    let prunedLower = Infinity;
    if (dimension === 2) {
        let angle = Math.atan2(best.matrix[3]!, best.matrix[0]!);
        let step = Math.PI / 8;
        for (let iteration = 0; iteration < 50 && step * Math.max(1, data.sourceRadius) > tolerance / 10; iteration++) {
            let improved = false;
            for (const sign of [-1, 1]) {
                const candidate = evaluate(planarRotation(angle + sign * step));
                if (candidate.radius < best.radius - data.roundoff) {
                    best = candidate;
                    angle += sign * step;
                    improved = true;
                }
            }
            if (!improved)
                step /= 2;
        }
        interface Interval {
            lo: number;
            hi: number;
            lower: number;
        }
        const heap = new MinHeap<Interval>();
        const create = (lo: number, hi: number): Interval => {
            const middle = (lo + hi) / 2, value = evaluate(planarRotation(middle));
            if (value.radius < best.radius)
                best = value;
            let pairLower = 0;
            for (const pair of pairData) {
                let angleDistance = Math.PI;
                for (let winding = -2; winding <= 2; winding++) {
                    const preferred = pair.preferred + winding * 2 * Math.PI;
                    angleDistance = Math.min(angleDistance, preferred < lo ? lo - preferred : preferred > hi ? preferred - hi : 0);
                }
                pairLower = Math.max(pairLower, gapAtAngle(pair.a, pair.b, Math.min(Math.PI, angleDistance)) / 2);
            }
            const displacement = 2 * data.sourceRadius * Math.sin(Math.min(Math.PI, (hi - lo) / 2) / 2);
            return { lo, hi, lower: Math.max(floor, value.radius - displacement - data.roundoff, pairLower - data.roundoff) };
        };
        const enqueue = (node: Interval): void => { if (node.lower < best.radius - tolerance)
            heap.push(node);
        else
            prunedLower = Math.min(prunedLower, node.lower); };
        for (let i = 0; i < 16; i++)
            enqueue(create(-Math.PI + 2 * Math.PI * i / 16, -Math.PI + 2 * Math.PI * (i + 1) / 16));
        for (let nodes = 0; nodes < maxNodes && heap.length; nodes++) {
            if (best.radius - Math.min(heap.peek()!.lower, prunedLower) <= tolerance)
                break;
            const node = heap.pop()!;
            if (node.lower >= best.radius - tolerance) {
                prunedLower = Math.min(prunedLower, node.lower);
                continue;
            }
            const middle = (node.lo + node.hi) / 2;
            enqueue(create(node.lo, middle));
            enqueue(create(middle, node.hi));
        }
        return { best, lower: Math.max(floor, Math.min(best.radius, heap.peek()?.lower ?? Infinity, prunedLower)), evaluations, branch };
    }
    function refine(seed: Evaluation, iterations: number): Evaluation {
        interface Vertex {
            vector: Point3;
            value: Evaluation;
        }
        const vertex = (vector: Point3): Vertex => ({ vector, value: evaluate(multiply(rotationVector(vector), seed.matrix)) });
        let simplex: Vertex[] = [{ vector: [0, 0, 0], value: seed }, vertex([0.2, 0, 0]), vertex([0, 0.2, 0]), vertex([0, 0, 0.2])];
        const combination = (center: Point3, worst: Point3, factor: number): Point3 => [0, 1, 2].map(axis => center[axis]! + factor * (center[axis]! - worst[axis]!)) as unknown as Point3;
        for (let iteration = 0; iteration < iterations; iteration++) {
            simplex.sort((a, b) => a.value.radius - b.value.radius);
            if (simplex[3]!.value.radius - simplex[0]!.value.radius < tolerance / 100 && Math.max(...simplex.map(v => pointDistance(v.vector, simplex[0]!.vector))) * Math.max(1, data.sourceRadius) < tolerance / 10)
                break;
            const center = average(simplex.slice(0, 3).map(v => v.vector)), worst = simplex[3]!;
            const reflected = vertex(combination(center, worst.vector, 1));
            if (reflected.value.radius < simplex[0]!.value.radius) {
                const expanded = vertex(combination(center, worst.vector, 2));
                simplex[3] = expanded.value.radius < reflected.value.radius ? expanded : reflected;
            }
            else if (reflected.value.radius < simplex[2]!.value.radius)
                simplex[3] = reflected;
            else {
                const contracted = vertex(combination(center, worst.vector, reflected.value.radius < worst.value.radius ? 0.5 : -0.5));
                if (contracted.value.radius < Math.min(worst.value.radius, reflected.value.radius))
                    simplex[3] = contracted;
                else
                    simplex = [simplex[0]!, ...simplex.slice(1).map(v => vertex(average([v.vector, simplex[0]!.vector])))];
            }
        }
        simplex.sort((a, b) => a.value.radius - b.value.radius);
        return simplex[0]!.value.radius < seed.radius ? simplex[0]!.value : seed;
    }
    best = refine(best, 100);
    if (best.radius - floor <= tolerance)
        return { best, lower: Math.min(best.radius, floor), evaluations, branch };
    interface Box {
        lo: Point3;
        hi: Point3;
        lower: number;
    }
    const heap = new MinHeap<Box>();
    const createBox = (lo: Point3, hi: Point3): Box | undefined => {
        const nearest: Point3 = [0, 1, 2].map(axis => lo[axis]! > 0 ? lo[axis]! : hi[axis]! < 0 ? hi[axis]! : 0) as unknown as Point3;
        if (vectorNorm(nearest) > Math.PI + 1e-12)
            return;
        const middle = average([lo, hi]), point = vectorNorm(middle) <= Math.PI ? middle : nearest;
        const beta = Math.min(Math.PI, Math.hypot(...[0, 1, 2].map(axis => Math.max(Math.abs(point[axis]! - lo[axis]!), Math.abs(point[axis]! - hi[axis]!)))));
        const value = evaluate(rotationVector(point));
        if (value.radius < best.radius)
            best = refine(value, 35);
        let pairLower = 0;
        for (const pair of pairData) {
            const rotated = matVec(value.matrix, pair.p);
            const angle = pair.a * pair.b === 0 ? 0 : Math.acos(Math.max(-1, Math.min(1, pointDot(rotated, pair.q) / (pair.a * pair.b))));
            pairLower = Math.max(pairLower, gapAtAngle(pair.a, pair.b, Math.max(0, angle - beta)) / 2);
        }
        const displacement = 2 * data.sourceRadius * Math.sin(beta / 2);
        return { lo, hi, lower: Math.max(floor, value.radius - displacement - data.roundoff, pairLower - data.roundoff) };
    };
    const enqueue = (node: Box | undefined): void => { if (!node)
        return; if (node.lower < best.radius - tolerance)
        heap.push(node);
    else
        prunedLower = Math.min(prunedLower, node.lower); };
    enqueue(createBox([-Math.PI, -Math.PI, -Math.PI], [Math.PI, Math.PI, Math.PI]));
    for (let nodes = 0; nodes < maxNodes && heap.length; nodes++) {
        if (best.radius - Math.min(heap.peek()!.lower, prunedLower) <= tolerance)
            break;
        const node = heap.pop()!;
        if (node.lower >= best.radius - tolerance) {
            prunedLower = Math.min(prunedLower, node.lower);
            continue;
        }
        let axis = 0;
        for (let i = 1; i < 3; i++)
            if (node.hi[i]! - node.lo[i]! > node.hi[axis]! - node.lo[axis]!)
                axis = i;
        const middle = (node.lo[axis]! + node.hi[axis]!) / 2;
        const firstHi = [...node.hi] as [
            number,
            number,
            number
        ], secondLo = [...node.lo] as [
            number,
            number,
            number
        ];
        firstHi[axis] = middle;
        secondLo[axis] = middle;
        enqueue(createBox(node.lo, firstHi));
        enqueue(createBox(secondLo, node.hi));
    }
    return { best, lower: Math.max(floor, Math.min(best.radius, heap.peek()?.lower ?? Infinity, prunedLower)), evaluations, branch };
}
export function solveMinimax(source: readonly Point3[], target: readonly Point3[], options: MinimaxOptions = {}): MinimaxSolution {
    if (source.length !== target.length)
        throw new Error("Correspondence arrays must have equal lengths");
    if (source.length > 20)
        throw new Error("The minimax explorer supports at most twenty points");
    for (const point of [...source, ...target])
        if (point.length !== 3 || !point.every(Number.isFinite))
            throw new Error("Endpoints must contain three finite coordinates");
    const dimension = options.dimension ?? (source.some(p => Math.abs(p[2]) > 1e-12) || target.some(p => Math.abs(p[2]) > 1e-12) ? 3 : 2);
    if (dimension === 2 && [...source, ...target].some(p => Math.abs(p[2]) > 1e-9))
        throw new Error("Planar minimax inputs must lie in the z=0 plane");
    const tolerance = options.tolerance ?? (dimension === 2 ? 1e-4 : 0.002);
    const maxNodes = options.maxNodes ?? (dimension === 2 ? 4096 : 512);
    if (!Number.isFinite(tolerance) || tolerance <= 0 || !Number.isFinite(maxNodes) || maxNodes < 0)
        throw new Error("Solver tolerance must be positive and the node budget nonnegative");
    const data = prepare(source, target, dimension);
    let best: Evaluation, lower: number, branch: MinimaxSolution["branch"], evaluations: number;
    if (options.mode === "translation" || source.length === 0) {
        const ball = minimumEnclosingBall(data.p.map((point, i) => pointSubtract(data.q[i]!, point)));
        best = { matrix: IDENTITY, center: ball.center, radius: ball.radius };
        lower = ball.radius;
        branch = options.mode === "translation" ? "translation" : "proper";
        evaluations = 1;
    }
    else {
        const proper = solveBranch(data, dimension, "proper", options, tolerance, Math.floor(maxNodes));
        const improper = options.allowReflections === false ? undefined : solveBranch(data, dimension, "improper", options, tolerance, Math.floor(maxNodes));
        const chosen = improper && improper.best.radius < proper.best.radius - data.roundoff ? improper : proper;
        best = chosen.best;
        branch = chosen.branch;
        evaluations = proper.evaluations + (improper?.evaluations ?? 0);
        lower = Math.min(proper.lower, improper?.lower ?? Infinity);
    }
    const matrix = branch === "improper" ? reflectX(best.matrix) : best.matrix;
    const rotatedCenter = matVec(matrix, data.sourceCenter);
    const translation: Point3 = [data.targetCenter[0] + best.center[0] - rotatedCenter[0], data.targetCenter[1] + best.center[1] - rotatedCenter[1], data.targetCenter[2] + best.center[2] - rotatedCenter[2]];
    const transform = [matrix[0]!, matrix[1]!, matrix[2]!, translation[0], matrix[3]!, matrix[4]!, matrix[5]!, translation[1], matrix[6]!, matrix[7]!, matrix[8]!, translation[2], 0, 0, 0, 1];
    const fit = source.map(point => applyTransform(transform, point)), residuals = fit.map((point, i) => pointDistance(point, target[i]!));
    const upperBound = Math.max(0, ...residuals), lowerBound = Math.max(0, Math.min(upperBound, lower));
    return { transform, fit, residuals, radius: upperBound, lowerBound, upperBound, certified: upperBound - lowerBound <= tolerance, tolerance, evaluations, dimension, branch };
}
