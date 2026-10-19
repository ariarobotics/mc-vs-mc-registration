export type Point3 = readonly [
    number,
    number,
    number
];
export interface SmallEnclosingBall {
    center: Point3;
    radius: number;
    support: number[];
}
export const pointDistance = (a: Point3, b: Point3): number => Math.hypot(a[0] - b[0], a[1] - b[1], a[2] - b[2]);
export const pointSubtract = (a: Point3, b: Point3): Point3 => [a[0] - b[0], a[1] - b[1], a[2] - b[2]];
export const pointDot = (a: Point3, b: Point3): number => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
const cross = (a: Point3, b: Point3): Point3 => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
export function minimumEnclosingBall(input: readonly Point3[]): SmallEnclosingBall {
    if (input.length === 0)
        return { center: [0, 0, 0], radius: 0, support: [] };
    if (input.length > 20)
        throw new Error("The minimax explorer supports at most twenty points");
    const offset = input[0]!;
    const points = input.map(point => pointSubtract(point, offset));
    let diameter = 0, first = 0, second = 0;
    for (let i = 0; i < points.length; i++)
        for (let j = i + 1; j < points.length; j++) {
            const d = pointDistance(points[i]!, points[j]!);
            if (d > diameter) {
                diameter = d;
                first = i;
                second = j;
            }
        }
    const midpoint: Point3 = [0, 1, 2].map(axis => (points[first]![axis]! + points[second]![axis]!) / 2) as unknown as Point3;
    const radiusAt = (center: Point3): number => Math.max(...points.map(point => pointDistance(point, center)));
    const midpointRadius = radiusAt(midpoint);
    const roundoff = 2e-12 * Math.max(1, diameter);
    if (midpointRadius <= diameter / 2 + roundoff)
        return {
            center: [midpoint[0] + offset[0], midpoint[1] + offset[1], midpoint[2] + offset[2]],
            radius: midpointRadius,
            support: diameter === 0 ? [first] : [first, second],
        };
    let bestCenter = midpoint, bestRadius = midpointRadius, support = [first, second];
    const inspect = (center: Point3, indices: number[]): void => {
        const radius = pointDistance(center, points[indices[0]!]!);
        if (radius >= bestRadius + roundoff || !Number.isFinite(radius))
            return;
        for (const point of points)
            if (pointDistance(point, center) > radius + roundoff)
                return;
        const actualRadius = radiusAt(center);
        if (actualRadius < bestRadius) {
            bestCenter = center;
            bestRadius = actualRadius;
            support = indices;
        }
    };
    for (let i = 0; i < points.length; i++)
        for (let j = i + 1; j < points.length; j++) {
            const a = points[i]!, b = points[j]!;
            inspect([(a[0] + b[0]) / 2, (a[1] + b[1]) / 2, (a[2] + b[2]) / 2], [i, j]);
        }
    for (let i = 0; i < points.length; i++)
        for (let j = i + 1; j < points.length; j++)
            for (let k = j + 1; k < points.length; k++) {
                const origin = points[i]!, u = pointSubtract(points[j]!, origin), v = pointSubtract(points[k]!, origin);
                const n = cross(u, v), n2 = pointDot(n, n), u2 = pointDot(u, u), v2 = pointDot(v, v);
                if (n2 <= 1e-28 * u2 * v2)
                    continue;
                const vn = cross(v, n), nu = cross(n, u);
                const center: Point3 = [0, 1, 2].map(axis => origin[axis]! + (u2 * vn[axis]! + v2 * nu[axis]!) / (2 * n2)) as unknown as Point3;
                inspect(center, [i, j, k]);
                for (let l = k + 1; l < points.length; l++) {
                    const w = pointSubtract(points[l]!, origin), vw = cross(v, w), wu = cross(w, u), uv = n;
                    const determinant = pointDot(u, vw);
                    const w2 = pointDot(w, w);
                    if (Math.abs(determinant) <= 1e-14 * Math.sqrt(u2 * v2 * w2))
                        continue;
                    const sphere: Point3 = [0, 1, 2].map(axis => origin[axis]! + (u2 * vw[axis]! + v2 * wu[axis]! + w2 * uv[axis]!) / (2 * determinant)) as unknown as Point3;
                    inspect(sphere, [i, j, k, l]);
                }
            }
    return { center: [bestCenter[0] + offset[0], bestCenter[1] + offset[1], bestCenter[2] + offset[2]], radius: bestRadius, support };
}
