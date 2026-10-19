export interface PointMatch {
    source: readonly number[];
    target: readonly number[];
}
interface PointFit {
    transform: number[];
    fitError: number;
}
type Vector3 = [
    number,
    number,
    number
];
const identity = (): number[] => [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1];
const difference = (a: readonly number[], b: readonly number[]): Vector3 => [a[0]! - b[0]!, a[1]! - b[1]!, a[2]! - b[2]!];
const norm = (v: readonly number[]): number => Math.hypot(v[0]!, v[1]!, v[2]!);
function symmetricEigen(matrix: readonly (readonly number[])[]): {
    values: number[];
    vectors: number[][];
} {
    const n = matrix.length;
    const scale = Math.max(...matrix.flatMap(row => [...row].map(Math.abs)));
    const vectors: number[][] = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j): number => i === j ? 1 : 0));
    if (scale === 0)
        return { values: Array<number>(n).fill(0), vectors };
    const a = matrix.map(row => row.map(value => value / scale));
    for (let iteration = 0; iteration < 160; iteration++) {
        let p = 0, q = 1, largest = 0;
        for (let i = 0; i < n; i++)
            for (let j = i + 1; j < n; j++)
                if (Math.abs(a[i]![j]!) > largest) {
                    p = i;
                    q = j;
                    largest = Math.abs(a[i]![j]!);
                }
        if (largest <= 2e-15)
            break;
        const apq = a[p]![q]!;
        const tau = (a[q]![q]! - a[p]![p]!) / (2 * apq);
        const t = (tau >= 0 ? 1 : -1) / (Math.abs(tau) + Math.hypot(1, tau));
        const c = 1 / Math.hypot(1, t), s = t * c;
        a[p]![p] = a[p]![p]! - t * apq;
        a[q]![q] = a[q]![q]! + t * apq;
        a[p]![q] = a[q]![p] = 0;
        for (let k = 0; k < n; k++) {
            if (k !== p && k !== q) {
                const akp = a[k]![p]!, akq = a[k]![q]!;
                a[k]![p] = a[p]![k] = c * akp - s * akq;
                a[k]![q] = a[q]![k] = s * akp + c * akq;
            }
            const vkp = vectors[k]![p]!, vkq = vectors[k]![q]!;
            vectors[k]![p] = c * vkp - s * vkq;
            vectors[k]![q] = s * vkp + c * vkq;
        }
    }
    return { values: a.map((row, i) => row[i]!), vectors };
}
function centroid(points: readonly (readonly number[])[]): Vector3 {
    const origin = points[0]!;
    return [0, 1, 2].map(axis => origin[axis]! + points.reduce((sum, point) => sum + (point[axis]! - origin[axis]!) / points.length, 0)) as Vector3;
}
function quaternionRotation(q: readonly number[]): number[] {
    const [w, x, y, z] = q as [
        number,
        number,
        number,
        number
    ];
    return [
        1 - 2 * (y * y + z * z), 2 * (x * y - w * z), 2 * (x * z + w * y),
        2 * (x * y + w * z), 1 - 2 * (x * x + z * z), 2 * (y * z - w * x),
        2 * (x * z - w * y), 2 * (y * z + w * x), 1 - 2 * (x * x + y * y),
    ];
}
function rotate(rotation: readonly number[], point: readonly number[]): Vector3 {
    return [0, 1, 2].map(row => rotation[3 * row]! * point[0]! + rotation[3 * row + 1]! * point[1]! + rotation[3 * row + 2]! * point[2]!) as Vector3;
}
export function fitPointPose(matches: readonly PointMatch[]): PointFit {
    for (const match of matches)
        for (const point of [match.source, match.target]) {
            if (point.length !== 3 || !point.every(Number.isFinite))
                throw new Error("Every endpoint must have three finite coordinates");
        }
    if (matches.length === 0)
        return { transform: identity(), fitError: 0 };
    const sourceCenter = centroid(matches.map(match => match.source));
    const targetCenter = centroid(matches.map(match => match.target));
    const source = matches.map(match => difference(match.source, sourceCenter));
    const target = matches.map(match => difference(match.target, targetCenter));
    const coordinateScale = Math.max(0, ...source.flat().map(Math.abs), ...target.flat().map(Math.abs));
    const covariance = Array.from({ length: 3 }, () => Array<number>(3).fill(0));
    if (coordinateScale > 0)
        source.forEach((point, i) => {
            for (let row = 0; row < 3; row++)
                for (let column = 0; column < 3; column++) {
                    covariance[row]![column] += (point[row]! / coordinateScale) * (target[i]![column]! / coordinateScale);
                }
        });
    const [[xx, xy, xz], [yx, yy, yz], [zx, zy, zz]] = covariance as [
        [
            number,
            number,
            number
        ],
        [
            number,
            number,
            number
        ],
        [
            number,
            number,
            number
        ]
    ];
    const horn = [
        [xx + yy + zz, yz - zy, zx - xz, xy - yx],
        [yz - zy, xx - yy - zz, xy + yx, zx + xz],
        [zx - xz, xy + yx, -xx + yy - zz, yz + zy],
        [xy - yx, zx + xz, yz + zy, -xx - yy + zz],
    ];
    const eigen = symmetricEigen(horn);
    const greatest = Math.max(...eigen.values);
    const top = eigen.values.map((value, i) => ({ value, i })).filter(entry => greatest - entry.value <= 1e-11 * Math.max(1, Math.abs(greatest))).map(entry => entry.i);
    let quaternion = [1, 0, 0, 0];
    for (let preferred = 0; preferred < 4; preferred++) {
        const projected = [0, 1, 2, 3].map(component => top.reduce((sum, index) => sum + eigen.vectors[component]![index]! * eigen.vectors[preferred]![index]!, 0));
        const magnitude = Math.hypot(...projected);
        if (magnitude > 1e-12) {
            quaternion = projected.map(value => value / magnitude);
            break;
        }
    }
    const rotation = quaternionRotation(quaternion);
    const rotatedCenter = rotate(rotation, sourceCenter);
    const translation = difference(targetCenter, rotatedCenter);
    const transform = [
        rotation[0]!, rotation[1]!, rotation[2]!, translation[0],
        rotation[3]!, rotation[4]!, rotation[5]!, translation[1],
        rotation[6]!, rotation[7]!, rotation[8]!, translation[2],
        0, 0, 0, 1,
    ];
    const residuals = source.map((point, i) => norm(difference(rotate(rotation, point), target[i]!)));
    return {
        transform,
        fitError: Math.hypot(...residuals) / Math.sqrt(matches.length),
    };
}
