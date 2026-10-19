import { applyTransform } from "./rigid-minimax.ts";
import { rigidConsensus } from "./maximum-consensus.ts";
import { minimumEnclosingBall } from "./minimax-geometry.ts";
export type Point3 = readonly [
    number,
    number,
    number
];
export type ExplorerMode = "translation" | "rigid";
export type ExplorerOptimizer = "translation" | "proper" | "rigid";
export type ExplorerId = "triangle" | "tetrahedron" | "unbounded" | "clique" | "triples" | "proposition3d" | "outliers" | "conditioning" | "spatial-reflection" | "rigid-pose";
export interface ExplorerEdits {
    source?: readonly Point3[];
    target?: readonly Point3[];
    initialTransform?: readonly number[];
}
export interface ExplorerState {
    ell: number;
    tau: number;
    epsilon: number;
    count: number;
    proper?: boolean;
    optimizer?: ExplorerOptimizer;
    dimension?: 2 | 3;
}
export interface ExplorerPreset {
    id: ExplorerId;
    label: string;
    mode: ExplorerMode;
    dimension: 2 | 3;
    defaults: ExplorerState;
    controls: { ell?: boolean; count?: boolean; };
    ellRange?: readonly [number, number, number];
    tauRange?: readonly [number, number, number];
    epsilonRange?: readonly [number, number, number];
    countRange?: readonly [number, number, number];
    parameterLabel?: string;
    parameterExpression?: string;
}
export interface ExplorerExample {
    source: Point3[];
    target: Point3[];
    mode: ExplorerMode;
    dimension: 2 | 3;
    displacements?: Point3[];
    consensusCount: number;
    consensusUpperBound: number;
    consensusCertified: boolean;
    fitTransform: readonly number[];
    formula: string;
}
const defaults = (changes: Partial<ExplorerState> = {}): ExplorerState => ({ ell: 12, tau: 1, epsilon: 2, count: 7, proper: false, ...changes });
const presetDefinitions: readonly ExplorerPreset[] = [
    {
        id: "triangle", label: "Translation triangle",
        
        mode: "translation", dimension: 2,
        defaults: defaults(), controls: {  },
    },
    {
        id: "tetrahedron", label: "Translation tetrahedron",
        mode: "translation", dimension: 3,
        defaults: defaults({ tau: 1.2, epsilon: 2.4 }), controls: {},
    },
    {
        id: "unbounded", label: "Unbounded alignment error",
        mode: "rigid", dimension: 2,
        defaults: defaults(), controls: { ell: true }, ellRange: [1, 180, 1], tauRange: [0, 15, 0.05],
    },
    {
        id: "clique", label: "Line–parabola construction",
        
        mode: "rigid", dimension: 2,
        defaults: defaults({ ell: 160 }), controls: { ell: true, count: true }, ellRange: [2, 800, 2], countRange: [3, 12, 1], tauRange: [0, 20, 0.05],
    },
    {
        id: "triples", label: "Swapped rectangle",
        mode: "rigid", dimension: 2,
        defaults: defaults({ tau: 0.2, epsilon: 0.4 }), controls: { ell: true }, ellRange: [1, 100, 1],
    },
    {
        id: "proposition3d", label: "Spatial four-point consistency",
        mode: "rigid", dimension: 3,
        defaults: defaults({ ell: 20, tau: 0.3, epsilon: 0.6 }), controls: { ell: true }, ellRange: [2, 100, 1],
    },
    {
        id: "outliers", label: "Translation with outliers",
        mode: "translation", dimension: 2,
        defaults: defaults({ tau: 0.4, epsilon: 0.8, count: 9 }), controls: { count: true }, countRange: [5, 12, 1],
    },
    {
        id: "conditioning", label: "Triangle conditioning",
        mode: "rigid", dimension: 2,
        defaults: defaults({ ell: 0.02, tau: 0.2, epsilon: 0.1 }), controls: { ell: true }, ellRange: [0.02, 6, 0.02], tauRange: [0, 1, 0.01], epsilonRange: [0, 1, 0.01],
    },
    {
        id: "spatial-reflection", label: "Reflected tetrahedron",
        mode: "rigid", dimension: 3,
        defaults: defaults({ ell: 1, tau: 0.2, epsilon: 0, proper: true }), controls: { ell: true }, ellRange: [0.3, 2.5, 0.02],
    },
    {
        id: "rigid-pose", label: "Exact rigid alignment",
        mode: "rigid", dimension: 3,
        defaults: defaults({ ell: 1, tau: 0.15, epsilon: 0.05, count: 8, proper: true }), controls: { ell: true, count: true }, ellRange: [0.3, 3, 0.02], countRange: [4, 12, 1],
    },
];
const parameterInfo: Partial<Record<ExplorerId, {
    parameterLabel: string;
    parameterExpression: string;
}>> = {
    unbounded: { parameterLabel: "Cloud length", parameterExpression: String.raw `\ell` },
    clique: { parameterLabel: "Point spacing", parameterExpression: String.raw `\ell` },
    triples: { parameterLabel: "Rectangle height", parameterExpression: String.raw `\ell` },
    proposition3d: { parameterLabel: "Axis scale", parameterExpression: String.raw `\ell` },
    conditioning: { parameterLabel: "Triangle height", parameterExpression: String.raw `\ell` },
    "rigid-pose": { parameterLabel: "Cloud scale", parameterExpression: "s" },
    "spatial-reflection": { parameterLabel: "Cloud scale", parameterExpression: "s" },
};
export const explorerPresets: readonly ExplorerPreset[] = presetDefinitions.map(preset => ({
    ...preset, ...parameterInfo[preset.id], controls: preset.controls,
}));
export function presetOptimizer(preset: ExplorerPreset): ExplorerOptimizer {
    return preset.mode === "translation" ? "translation" : preset.defaults.proper ? "proper" : "rigid";
}
function configuration(preset: ExplorerPreset, state: ExplorerState): {
    mode: ExplorerMode;
    proper: boolean;
    dimension: 2 | 3;
} {
    const optimizer = state.optimizer ?? (preset.mode === "translation" ? "translation" : state.proper ? "proper" : "rigid");
    return { mode: optimizer === "translation" ? "translation" : "rigid", proper: optimizer === "proper", dimension: state.dimension ?? preset.dimension };
}
export const distance3 = (a: Point3, b: Point3): number => Math.hypot(a[0] - b[0], a[1] - b[1], a[2] - b[2]);
const add = (a: Point3, b: Point3): Point3 => [a[0] + b[0], a[1] + b[1], a[2] + b[2]];
const subtract = (a: Point3, b: Point3): Point3 => [a[0] - b[0], a[1] - b[1], a[2] - b[2]];
export interface ConsistencyEdge {
    a: number;
    b: number;
    gap: number;
}
export interface ConsistencyGraph {
    edges: ConsistencyEdge[];
    maximumClique: number[];
    cliqueNumber: number;
    delta: number;
}
export function consistencyGraph(source: readonly Point3[], target: readonly Point3[], epsilon: number, mode: ExplorerMode = "rigid"): ConsistencyGraph {
    if (source.length !== target.length)
        throw new Error("Correspondence arrays must have the same length");
    const n = source.length;
    if (n > 20)
        throw new Error("Exact clique search is limited to twenty points");
    const displacements = source.map((point, i) => subtract(target[i]!, point));
    const adjacency = Array<number>(n).fill(0);
    const edges: ConsistencyEdge[] = [];
    let delta = 0;
    const threshold = Math.max(0, epsilon);
    for (let a = 0; a < n; a++)
        for (let b = a + 1; b < n; b++) {
            const gap = mode === "translation" ? distance3(displacements[a]!, displacements[b]!) : Math.abs(distance3(source[a]!, source[b]!) - distance3(target[a]!, target[b]!));
            delta = Math.max(delta, gap);
            if (gap <= threshold + 1e-10 * Math.max(1, threshold)) {
                edges.push({ a, b, gap });
                adjacency[a] = adjacency[a]! | (1 << b);
                adjacency[b] = adjacency[b]! | (1 << a);
            }
        }
    const bits = (mask: number) => { let result = 0; while (mask) {
        mask &= mask - 1;
        result++;
    } return result; };
    let maximumClique: number[] = [];
    function search(clique: number[], candidates: number) {
        if (clique.length > maximumClique.length)
            maximumClique = [...clique];
        while (candidates && clique.length + bits(candidates) > maximumClique.length) {
            const bit = candidates & -candidates;
            candidates &= ~bit;
            const vertex = 31 - Math.clz32(bit);
            search([...clique, vertex], candidates & adjacency[vertex]!);
        }
    }
    search([], (1 << n) - 1);
    return { edges, maximumClique, cliqueNumber: maximumClique.length, delta };
}
export interface TranslationConsensus {
    center: Point3;
    indices: number[];
    count: number;
}
export function translationConsensus(points: readonly Point3[], tau: number): TranslationConsensus {
    if (points.length > 12)
        throw new Error("The consensus explorer supports at most twelve votes");
    if (!Number.isFinite(tau) || tau < 0)
        throw new Error("Point tolerance must be finite and nonnegative");
    const radius = Math.max(0, tau);
    if (points.some(point => Math.abs(point[2]) > 1e-10)) {
        let best: TranslationConsensus = { center: [0, 0, 0], indices: [], count: 0 };
        const tolerance = 1e-9 * Math.max(1, radius);
        function supports(members: number[], start: number): void {
            if (best.count === points.length)
                return;
            if (members.length) {
                const ball = minimumEnclosingBall(members.map(i => points[i]!));
                if (ball.radius > radius + tolerance)
                    return;
                const indices = points.map((_, i) => i).filter(i => distance3(ball.center, points[i]!) <= radius + tolerance);
                if (indices.length > best.count)
                    best = { center: ball.center, indices, count: indices.length };
            }
            if (members.length === 4)
                return;
            for (let i = start; i < points.length; i++)
                supports([...members, i], i + 1);
        }
        supports([], 0);
        if (best.count)
            best.center = minimumEnclosingBall(best.indices.map(i => points[i]!)).center;
        return best;
    }
    const centers: Point3[] = [...points];
    for (let i = 0; i < points.length; i++)
        for (let j = i + 1; j < points.length; j++) {
            const first = points[i]!, second = points[j]!;
            const d = distance3(first, second);
            if (d <= 1e-12 || d > 2 * radius + 1e-10)
                continue;
            const h = Math.sqrt(Math.max(0, radius ** 2 - d ** 2 / 4));
            const middle: Point3 = [(first[0] + second[0]) / 2, (first[1] + second[1]) / 2, 0];
            const perpendicular: Point3 = [-(second[1] - first[1]) * h / d, (second[0] - first[0]) * h / d, 0];
            centers.push(add(middle, perpendicular), subtract(middle, perpendicular));
        }
    let best: TranslationConsensus = { center: [0, 0, 0], indices: [], count: 0 };
    for (const center of centers) {
        const indices = points.map((_, i) => i).filter(i => distance3(center, points[i]!) <= radius + 1e-9 * Math.max(1, radius));
        if (indices.length > best.count)
            best = { center, indices, count: indices.length };
    }
    if (best.count)
        best.center = minimumEnclosingBall(best.indices.map(i => points[i]!)).center;
    return best;
}
function translationVotes(id: ExplorerId, count: number): Point3[] {
    if (id === "triangle")
        return [[2 / Math.sqrt(3), 0, 0], [-1 / Math.sqrt(3), 1, 0], [-1 / Math.sqrt(3), -1, 0]];
    if (id === "tetrahedron") {
        const s = 1 / Math.sqrt(2);
        return [[s, s, s], [s, -s, -s], [-s, s, -s], [-s, -s, s]];
    }
    return Array.from({ length: count }, (_, i): Point3 => {
        if (i === count - 2)
            return [2.9, 1.7, 0];
        if (i === count - 1)
            return [-2.2, -1.8, 0];
        const angle = i * 2.399963229728653;
        const radius = 0.08 + 0.16 * (i % 3) / 2;
        return [0.25 + radius * Math.cos(angle), -0.12 + radius * Math.sin(angle), 0];
    });
}
const copyPoints = (points: readonly Point3[]): Point3[] => points.map(point => [point[0], point[1], point[2]]);
export function pointsInDimension(points: readonly Point3[], dimension: 2 | 3): Point3[] {
    return points.map(point => [point[0], point[1], dimension === 2 ? 0 : point[2]]);
}
function validateEndpoints(source: readonly Point3[], target: readonly Point3[], dimension: 2 | 3): void {
    if (source.length !== target.length || source.length === 0 || source.length > 12)
        throw new Error("Edited clouds need the same number of one to twelve correspondence endpoints");
    for (const point of [...source, ...target]) {
        if (point.length !== 3 || !point.every(Number.isFinite))
            throw new Error("Every edited endpoint must have three finite coordinates");
        if (dimension === 2 && Math.abs(point[2]) > 1e-10)
            throw new Error("A planar construction needs planar edited endpoints");
    }
}
function construction(preset: ExplorerPreset, state: ExplorerState): {
    source: Point3[];
    target: Point3[];
    initialTransform?: number[];
} {
    const id = preset.id;
    const ell = Math.max(id === "rigid-pose" || id === "spatial-reflection" ? 0 : .001, state.ell);
    const count = Math.max(3, Math.min(12, Math.round(state.count)));
    if (preset.mode === "translation") {
        const votes = translationVotes(id, id === "outliers" ? Math.max(5, count) : count);
        const source: Point3[] = votes.map((_, i) => [2 * Math.cos(i * 2 * Math.PI / votes.length), 2 * Math.sin(i * 2 * Math.PI / votes.length), 0]);
        return { source, target: source.map((point, i) => add(point, votes[i]!)) };
    }
    if (id === "unbounded") {
        return { source: [[0, ell, 0], [0, -ell, 0], [0, 0, 0]], target: [[0, ell, 0], [0, -ell, 0], [2 * Math.sqrt(ell + 1), 0, 0]] };
    }
    if (id === "clique") {
        const x = Array.from({ length: count }, (_, i) => i - (count - 1) / 2);
        return { source: x.map(value => [ell * value, 0, 0]), target: x.map(value => [ell * value, 3 * value ** 2, 0]) };
    }
    if (id === "triples") {
        return { source: [[1, ell, 0], [-1, ell, 0], [-1, 0, 0], [1, 0, 0]], target: [[1, ell, 0], [-1, ell, 0], [1, 0, 0], [-1, 0, 0]] };
    }
    if (id === "proposition3d") {
        const source: Point3[] = [[1, 0, 0], [0, 2 * ell, 0], [0, 0, 2 * ell], [-1, 0, 0], [2, ell, ell]];
        return { source, target: [...source.slice(0, 4), [-2, ell, ell]] };
    }
    if (id === "conditioning") {
        return { source: [[-4, 0, 0], [4, 0, 0], [0, ell, 0]], target: [[-4, 0, 0], [4, 0, 0], [0, ell + .8, 0]] };
    }
    if (id === "spatial-reflection") {
        const source: Point3[] = [[0, 0, 0], [2 * ell, 0, 0], [.25 * ell, 1.7 * ell, 0], [.35 * ell, .4 * ell, 1.3 * ell]];
        return { source, target: source.map(point => [-point[0] + 1.8, point[1] + .5, point[2] - .3]) };
    }
    const source = Array.from({ length: Math.max(4, count) }, (_, i): Point3 => [ell * (1 + .06 * i) * Math.cos(.8 * i), ell * (1 + .06 * i) * Math.sin(.8 * i), ell * (.45 * i - 1.4)]);
    const yaw = .72, pitch = .35, cy = Math.cos(yaw), sy = Math.sin(yaw), cp = Math.cos(pitch), sp = Math.sin(pitch);
    const transform = [cy, -sy * cp, sy * sp, 2.8, sy, cy * cp, -cy * sp, -.8, 0, sp, cp, 1.1, 0, 0, 0, 1];
    return { source, target: source.map(point => applyTransform(transform, point)), initialTransform: transform };
}
export const translationFormula = String.raw `\rho^{(t)}(C)=\min_t\max_{i\in C}\|Rp_i+t-q_i\|,\qquad\operatorname{MC}^{(t)}(\tau)=\max\{|C|:\rho^{(t)}(C)\le\tau\}`;
export const rigidFormula = String.raw `\rho(C)=\min_{R,t}\max_{i\in C}\|Rp_i+t-q_i\|,\qquad\operatorname{MC}(\tau)=\max\{|C|:\rho(C)\le\tau\}`;
export const properRigidFormula = String.raw `\rho^+(C)=\min_{R\in\mathrm{SO}(d),t}\max_{i\in C}\|Rp_i+t-q_i\|,\qquad\operatorname{MC}^+(\tau)=\max\{|C|:\rho^+(C)\le\tau\}`;
export function buildExample(id: ExplorerId, state: ExplorerState, edits?: ExplorerEdits): ExplorerExample {
    const preset = explorerPresets.find(entry => entry.id === id);
    if (!preset) throw new Error(`Unknown example: ${id}`);
    const { mode, proper, dimension } = configuration(preset, state);
    if (!Number.isFinite(state.tau) || state.tau < 0) throw new Error("Point tolerance must be finite and nonnegative");
    const base = construction(preset, state);
    let source = copyPoints(edits?.source ?? base.source), target = copyPoints(edits?.target ?? base.target);
    const initialTransform = edits?.initialTransform ?? base.initialTransform;
    if (state.dimension !== undefined) {
        validateEndpoints(source, target, 3);
        source = pointsInDimension(source, dimension); target = pointsInDimension(target, dimension);
    }
    validateEndpoints(source, target, dimension);
    if (mode === "translation") {
        const displacements = source.map((point, i) => subtract(target[i]!, point));
        const consensus = translationConsensus(displacements, state.tau);
        const [x, y, z] = consensus.center;
        return { source, target, mode, dimension, displacements,
            consensusCount: consensus.count, consensusUpperBound: consensus.count, consensusCertified: true,
            fitTransform: [1, 0, 0, x, 0, 1, 0, y, 0, 0, 1, z, 0, 0, 0, 1], formula: translationFormula };
    }
    const consensus = rigidConsensus(source, target, state.tau, { dimension, proper, initialTransform });
    return { source, target, mode, dimension,
        consensusCount: consensus.count, consensusUpperBound: consensus.upperBound, consensusCertified: consensus.certified,
        fitTransform: consensus.transform, formula: proper ? properRigidFormula : rigidFormula };
}
