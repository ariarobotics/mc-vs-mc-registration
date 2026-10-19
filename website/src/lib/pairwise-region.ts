export type Point3 = readonly [
    number,
    number,
    number
];
export type Point2 = readonly [
    number,
    number
];
export interface MotionShell {
    center: Point3;
    inner: number;
    outer: number;
    pair: readonly [
        number,
        number
    ];
}
export interface MotionPlane {
    origin: Point3;
    x: Point3;
    y: Point3;
}
export interface PlanarShell {
    center: Point2;
    inner: number;
    outer: number;
    pair: readonly [
        number,
        number
    ];
}
type Edge = readonly [
    number,
    number
] | {
    readonly a: number;
    readonly b: number;
};
const difference = (a: Point3, b: Point3): Point3 => [a[0] - b[0], a[1] - b[1], a[2] - b[2]];
const dot = (a: Point3, b: Point3): number => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
const length = (a: Point3): number => Math.hypot(...a);
const finitePoint = (point: readonly number[], dimensions: number): boolean => point.length === dimensions && point.every(Number.isFinite);
const tolerance = (radius: number, width = 0): number => {
    const thresholdScale = Math.max(1, width / 2);
    return Math.min(1e-12 * thresholdScale + 8 * Number.EPSILON * Math.max(1, radius), 5e-11 * thresholdScale);
};
export function motionShells(source: readonly Point3[], target: readonly Point3[], edges: readonly Edge[], indices: readonly number[] | ReadonlySet<number>, cloud: "source" | "target", mode: "translation" | "rigid", epsilon: number, anchorIndex: number): MotionShell[] {
    if (source.length !== target.length)
        throw new Error("Correspondence arrays must have the same length");
    if (!Number.isFinite(epsilon) || epsilon < 0)
        throw new Error("Pairwise tolerance must be finite and nonnegative");
    if (![...source, ...target].every(point => finitePoint(point, 3)))
        throw new Error("Every endpoint must have three finite coordinates");
    const validIndex = (i: number) => Number.isInteger(i) && i >= 0 && i < source.length;
    if (!validIndex(anchorIndex))
        throw new Error("The dragged anchor is outside the cloud");
    const moved = new Set(indices);
    if (![...moved].every(validIndex))
        throw new Error("The selected correspondence is outside the cloud");
    const points = cloud === "source" ? source : target, reference = cloud === "source" ? target : source;
    const anchor = points[anchorIndex]!;
    const shells: MotionShell[] = [];
    for (const edge of edges) {
        const [a, b] = "a" in edge ? [edge.a, edge.b] : edge;
        if (!validIndex(a) || !validIndex(b))
            throw new Error("A consistency edge is outside the cloud");
        if (a === b || moved.has(a) === moved.has(b))
            continue;
        const i = moved.has(a) ? a : b, j = moved.has(a) ? b : a;
        let center: Point3, inner: number, outer: number;
        if (mode === "translation") {
            const q = difference(target[i]!, target[j]!), p = difference(source[i]!, source[j]!);
            const sign = cloud === "source" ? 1 : -1;
            center = [anchor[0] + sign * (q[0] - p[0]), anchor[1] + sign * (q[1] - p[1]), anchor[2] + sign * (q[2] - p[2])];
            inner = 0;
            outer = epsilon;
        }
        else {
            const offset = difference(anchor, points[i]!);
            center = [points[j]![0] + offset[0], points[j]![1] + offset[1], points[j]![2] + offset[2]];
            const r = length(difference(reference[i]!, reference[j]!));
            inner = Math.max(0, r - epsilon);
            outer = r + epsilon;
        }
        if (!finitePoint(center, 3) || !Number.isFinite(outer))
            throw new Error("Pairwise constraints exceed the finite coordinate range");
        shells.push({ center, inner, outer, pair: [a, b] });
    }
    return shells;
}
export function motionSlice(shells: readonly MotionShell[], plane: MotionPlane): {
    shells: PlanarShell[];
    empty: boolean;
} {
    if (![plane.origin, plane.x, plane.y].every(point => finitePoint(point, 3)) || Math.abs(length(plane.x) - 1) > 1e-8 || Math.abs(length(plane.y) - 1) > 1e-8 || Math.abs(dot(plane.x, plane.y)) > 1e-8) {
        throw new Error("The drag plane must have finite orthonormal axes");
    }
    const normal: Point3 = [plane.x[1] * plane.y[2] - plane.x[2] * plane.y[1], plane.x[2] * plane.y[0] - plane.x[0] * plane.y[2], plane.x[0] * plane.y[1] - plane.x[1] * plane.y[0]];
    const result: PlanarShell[] = [];
    let empty = false;
    for (const shell of shells) {
        const relative = difference(shell.center, plane.origin), depth = Math.abs(dot(relative, normal));
        if (depth > shell.outer + tolerance(shell.outer, shell.outer - shell.inner))
            empty = true;
        const sectionRadius = (r: number): number => r === 0 || depth >= r ? 0 : r * Math.sqrt((1 - depth / r) * (1 + depth / r));
        result.push({ center: [dot(relative, plane.x), dot(relative, plane.y)], inner: sectionRadius(shell.inner), outer: sectionRadius(shell.outer), pair: shell.pair });
    }
    return { shells: result, empty };
}
export function planePoint(point: Point2, plane: MotionPlane): Point3 {
    return [plane.origin[0] + point[0] * plane.x[0] + point[1] * plane.y[0], plane.origin[1] + point[0] * plane.x[1] + point[1] * plane.y[1], plane.origin[2] + point[0] * plane.x[2] + point[1] * plane.y[2]];
}
export function pointAllowed(point: Point2, shells: readonly PlanarShell[]): boolean {
    if (!finitePoint(point, 2))
        return false;
    return shells.every(shell => {
        const r = Math.hypot(point[0] - shell.center[0], point[1] - shell.center[1]);
        const error = tolerance(Math.max(r, shell.outer), shell.outer - shell.inner);
        return r >= shell.inner - error && r <= shell.outer + error;
    });
}
type Circle = {
    center: Point2;
    radius: number;
};
function circleIntersections(a: Circle, b: Circle): Point2[] {
    const dx = b.center[0] - a.center[0], dy = b.center[1] - a.center[1], distance = Math.hypot(dx, dy);
    if (distance === 0)
        return [];
    const error = tolerance(Math.max(distance, a.radius, b.radius));
    if (distance > a.radius + b.radius + error || distance < Math.abs(a.radius - b.radius) - error)
        return [];
    const scale = Math.max(distance, a.radius, b.radius), d = distance / scale, r = a.radius / scale, s = b.radius / scale;
    const along = (d + (r - s) * (r + s) / d) / 2;
    const height = Math.sqrt(Math.max(0, (r - along) * (r + along)));
    const x = a.center[0] + scale * (along * (dx / distance)), y = a.center[1] + scale * (along * (dy / distance));
    const ox = -dy / distance * scale * height, oy = dx / distance * scale * height;
    return height === 0 ? [[x, y]] : [[x + ox, y + oy], [x - ox, y - oy]];
}
export function nearestAllowedPoint(desired: Point2, shells: readonly PlanarShell[], fallback: Point2): Point2 {
    if (!finitePoint(desired, 2) || !finitePoint(fallback, 2))
        throw new Error("Drag positions must have two finite coordinates");
    const circles: Circle[] = [];
    for (const shell of shells) {
        if (!finitePoint(shell.center, 2) || !Number.isFinite(shell.inner) || !Number.isFinite(shell.outer) || shell.inner < 0 || shell.outer < shell.inner)
            throw new Error("An annulus must have finite ordered nonnegative radii");
        circles.push({ center: shell.center, radius: shell.outer });
        if (shell.inner > 0 && shell.inner !== shell.outer)
            circles.push({ center: shell.center, radius: shell.inner });
    }
    if (pointAllowed(desired, shells))
        return desired;
    let best: Point2 | undefined, bestDistance = Infinity;
    const inspect = (point: Point2): void => {
        if (!pointAllowed(point, shells))
            return;
        const distance = Math.hypot(point[0] - desired[0], point[1] - desired[1]);
        if (distance < bestDistance) {
            best = point;
            bestDistance = distance;
        }
    };
    inspect(fallback);
    for (const circle of circles) {
        let dx = desired[0] - circle.center[0], dy = desired[1] - circle.center[1], radius = Math.hypot(dx, dy);
        if (radius === 0) {
            dx = fallback[0] - circle.center[0];
            dy = fallback[1] - circle.center[1];
            radius = Math.hypot(dx, dy);
            if (radius === 0) {
                dx = 1;
                dy = 0;
                radius = 1;
            }
        }
        inspect([circle.center[0] + circle.radius * (dx / radius), circle.center[1] + circle.radius * (dy / radius)]);
    }
    for (let a = 0; a < circles.length; a++)
        for (let b = a + 1; b < circles.length; b++) {
            for (const point of circleIntersections(circles[a]!, circles[b]!))
                inspect(point);
        }
    if (!best)
        throw new Error("The pairwise region has no feasible point in the drag plane");
    return best;
}
