import { renderToString } from "katex";
import { minimumEnclosingBall, type Point3 } from "./minimax-geometry.ts";
export type FeasibleOptimizer = "translation" | "proper" | "rigid";
export type OrientationBranch = "proper" | "improper";
export interface FeasibleSetOptions {
    source: readonly Point3[];
    target: readonly Point3[];
    tau: number;
    optimizer: FeasibleOptimizer;
    dimension: 2 | 3;
    project: (point: Point3) => [
        number,
        number
    ];
    depth?: (point: Point3) => number;
    pxPerUnit: number;
    transform?: readonly number[];
    aligned?: boolean;
    reflectionBranch?: OrientationBranch;
    indices?: readonly number[];
    thetaScale?: number;
}
export interface FeasibleSetRenderResult {
    thetaScale: number;
    approximate: boolean;
    sampledIntersection: boolean;
}
const NS = "http://www.w3.org/2000/svg";
const constraintColor = "#437fa5", feasibleColor = "#278675", ink = "#355a46";
const PI2 = Math.PI * 2;
let clipSequence = 0;
const norm = (point: Point3) => Math.hypot(...point);
const distance = (a: Point3, b: Point3) => Math.hypot(a[0] - b[0], a[1] - b[1], a[2] - b[2]);
const tolerance = (points: readonly Point3[], radius: number) => 64 * Number.EPSILON * Math.max(1, radius, ...points.map(norm));
export function rotatePlanar(point: Point3, angle: number, branch: OrientationBranch = "proper"): Point3 {
    const x = branch === "improper" ? -point[0] : point[0], c = Math.cos(angle), s = Math.sin(angle);
    return [c * x - s * point[1], s * x + c * point[1], point[2]];
}
export function translationCenters(source: readonly Point3[], target: readonly Point3[], rotation?: readonly number[]): Point3[] {
    if (source.length !== target.length)
        throw new Error("Correspondence clouds must have the same length");
    return source.map((point, i) => {
        const rotated: Point3 = rotation ? [
            rotation[0]! * point[0] + rotation[1]! * point[1] + rotation[2]! * point[2],
            rotation[4]! * point[0] + rotation[5]! * point[1] + rotation[6]! * point[2],
            rotation[8]! * point[0] + rotation[9]! * point[1] + rotation[10]! * point[2],
        ] : point;
        return [target[i]![0] - rotated[0], target[i]![1] - rotated[1], target[i]![2] - rotated[2]];
    });
}
export function planarTranslationCenters(source: readonly Point3[], target: readonly Point3[], angle: number, branch: OrientationBranch = "proper"): Point3[] {
    if (source.length !== target.length)
        throw new Error("Correspondence clouds must have the same length");
    return source.map((point, i) => {
        const rotated = rotatePlanar(point, angle, branch);
        return [target[i]![0] - rotated[0], target[i]![1] - rotated[1], 0];
    });
}
export function planarTubePoint(source: Point3, target: Point3, theta: number, alpha: number, tau: number, thetaScale: number, branch: OrientationBranch = "proper"): Point3 {
    const rotated = rotatePlanar(source, theta, branch);
    return [target[0] - rotated[0] + tau * Math.cos(alpha), target[1] - rotated[1] + tau * Math.sin(alpha), theta * thetaScale];
}
export function isTranslationFeasible(point: Point3, centers: readonly Point3[], tau: number): boolean {
    if (!Number.isFinite(tau) || tau < 0)
        return false;
    const roundoff = tolerance([...centers, point], tau);
    return centers.every(center => distance(point, center) <= tau + roundoff);
}
export function diskIntersectionBoundary(centers: readonly Point3[], tau: number, segments = 96): Point3[] {
    if (!centers.length || !Number.isFinite(tau) || tau < 0)
        return [];
    if (tau === 0)
        return isTranslationFeasible(centers[0]!, centers, tau) ? [centers[0]!] : [];
    const result: Point3[] = [], roundoff = tolerance(centers, tau);
    const unique = centers.filter((center, i) => !centers.slice(0, i).some(other => distance(center, other) <= roundoff));
    for (const center of unique) {
        const angles = [0, PI2];
        for (const other of unique) {
            const dx = other[0] - center[0], dy = other[1] - center[1], d = Math.hypot(dx, dy);
            if (d > 2 * tau + roundoff)
                return [];
            if (d <= roundoff)
                continue;
            const heading = Math.atan2(dy, dx), half = Math.acos(Math.min(1, d / (2 * tau)));
            for (const angle of [heading - half, heading + half])
                angles.push((angle % PI2 + PI2) % PI2);
        }
        angles.sort((a, b) => a - b);
        const at = (angle: number): Point3 => [center[0] + tau * Math.cos(angle), center[1] + tau * Math.sin(angle), 0];
        for (const angle of angles)
            if (isTranslationFeasible(at(angle), centers, tau))
                result.push(at(angle));
        for (let i = 0; i < angles.length - 1; i++) {
            const from = angles[i]!, to = angles[i + 1]!;
            if (to - from < 1e-12 || !isTranslationFeasible(at((from + to) / 2), centers, tau))
                continue;
            const count = Math.max(1, Math.ceil((to - from) / PI2 * segments));
            for (let j = 0; j <= count; j++)
                result.push(at(from + (to - from) * j / count));
        }
    }
    if (!result.length)
        return [];
    const center: Point3 = [result.reduce((sum, p) => sum + p[0], 0) / result.length, result.reduce((sum, p) => sum + p[1], 0) / result.length, 0];
    result.sort((a, b) => Math.atan2(a[1] - center[1], a[0] - center[0]) - Math.atan2(b[1] - center[1], b[0] - center[0]));
    return result.filter((point, i) => i === 0 || distance(point, result[i - 1]!) > roundoff);
}
type GeometryOptions = Pick<FeasibleSetOptions, "source" | "target" | "tau" | "optimizer" | "dimension" | "indices" | "thetaScale" | "reflectionBranch" | "transform">;
const selectedClouds = (options: GeometryOptions) => {
    const indices = options.indices ?? options.source.map((_, i) => i);
    return { source: indices.map(i => options.source[i]!), target: indices.map(i => options.target[i]!) };
};
export function feasibleAngleScale(options: GeometryOptions): number {
    if (options.thetaScale !== undefined && options.thetaScale > 0)
        return options.thetaScale;
    const extent = Math.max(1, ...options.source.map(norm), ...options.target.map(norm));
    return extent / Math.PI;
}
export const feasibleSetIsSpatial = (options: Pick<FeasibleSetOptions, "optimizer" | "dimension">) => options.optimizer !== "translation" || options.dimension === 3;
export function feasibleSetPoints(options: GeometryOptions): Point3[] {
    const { source, target } = selectedClouds(options), points: Point3[] = [[0, 0, 0]];
    const thetaScale = feasibleAngleScale(options), branch = options.reflectionBranch ?? "proper";
    const angles = options.optimizer === "translation" ? [0] : Array.from({ length: 33 }, (_, i) => -Math.PI + i * PI2 / 32);
    for (const angle of angles) {
        const centers = options.optimizer === "translation" ? translationCenters(source, target, options.transform) : planarTranslationCenters(source, target, angle, branch);
        for (const center of centers) {
            const z = options.optimizer === "translation" ? center[2] : angle * thetaScale;
            points.push([center[0], center[1], z]);
            for (const axis of [0, 1, ...(options.optimizer === "translation" && options.dimension === 3 ? [2] : [])]) {
                for (const sign of [-1, 1]) {
                    const point: [
                        number,
                        number,
                        number
                    ] = [center[0], center[1], z];
                    point[axis] = point[axis]! + sign * options.tau;
                    points.push(point);
                }
            }
        }
    }
    return points;
}
function node<K extends keyof SVGElementTagNameMap>(name: K, attributes: Record<string, string | number> = {}, text?: string): SVGElementTagNameMap[K] {
    const element = document.createElementNS(NS, name);
    for (const [key, value] of Object.entries(attributes))
        element.setAttribute(key, String(value));
    if (text !== undefined)
        element.textContent = text;
    return element;
}
const path = (points: readonly Point3[], project: FeasibleSetOptions["project"], close = false) => points.map((point, i) => `${i ? "L" : "M"}${project(point).map(n => n.toFixed(3)).join(",")}`).join(" ") + (close ? " Z" : "");
function label(parent: SVGElement, point: Point3, options: FeasibleSetOptions, expression: string) {
    const [x, y] = options.project(point), foreign = node("foreignObject", { x: x + 8, y: y + 5, width: 80, height: 32, "pointer-events": "none" });
    const span = document.createElementNS("http://www.w3.org/1999/xhtml", "span");
    span.setAttribute("class", "point-math");
    span.style.color = ink;
    span.innerHTML = renderToString(expression, { throwOnError: false, output: "htmlAndMathml", trust: false });
    foreign.append(span);
    parent.append(foreign);
}
function marker(parent: SVGElement, point: Point3, options: FeasibleSetOptions) {
    const [x, y] = options.project(point), group = node("g", { "data-feasible-pose-marker": options.aligned ? "optimal" : "translation" });
    group.append(node("path", { d: `M${x - 5},${y}h10 M${x},${y - 5}v10`, stroke: ink, "stroke-width": 2 }));
    label(group, point, options, options.aligned ? String.raw `\mathbf t^\star` : String.raw `\mathbf t`);
    parent.append(group);
}
function renderPlanarDisks(parent: SVGElement, options: FeasibleSetOptions, centers: readonly Point3[]): boolean {
    const definitions = node("defs"), radius = options.tau * options.pxPerUnit, id = `feasible-${++clipSequence}`;
    let intersection: SVGElement = parent;
    const constraints = node("g", { "data-feasible-constraints": "disks" });
    centers.forEach((center, i) => {
        const [cx, cy] = options.project(center), disk = node("circle", { cx, cy, r: radius, fill: constraintColor, "fill-opacity": .045, stroke: constraintColor, "stroke-opacity": .5, "stroke-width": 1.1, "data-feasible-constraint": i, "data-feasible-radius": options.tau });
        constraints.append(disk);
        const clip = node("clipPath", { id: `${id}-${i}`, clipPathUnits: "userSpaceOnUse" });
        clip.append(node("circle", { cx, cy, r: radius }));
        definitions.append(clip);
    });
    parent.append(definitions, constraints);
    if (centers.length) {
        const all = node("g", { "data-feasible-intersection": "exact-disks" });
        parent.append(all);
        intersection = all;
        centers.forEach((_, i) => { const group = node("g", { "clip-path": `url(#${id}-${i})` }); intersection.append(group); intersection = group; });
        const [cx, cy] = options.project(centers[0]!);
        intersection.append(node("circle", { cx, cy, r: radius, fill: feasibleColor, "fill-opacity": .23 }));
        if (options.tau === 0 && isTranslationFeasible(centers[0]!, centers, 0))
            parent.append(node("circle", { cx, cy, r: 2.5, fill: feasibleColor, "data-feasible-singleton": "true" }));
    }
    return diskIntersectionBoundary(centers, options.tau).length > 0;
}
function renderSpatialBalls(parent: SVGElement, options: FeasibleSetOptions, centers: readonly Point3[]): boolean {
    const constraints = node("g", { "data-feasible-constraints": "balls" }), intersection = node("g", { "data-feasible-intersection": "sampled-ball-boundary" });
    let sampled = false;
    const sphereAt = (center: Point3, latitude: number, longitude: number): Point3 => [center[0] + options.tau * Math.cos(latitude) * Math.cos(longitude), center[1] + options.tau * Math.cos(latitude) * Math.sin(longitude), center[2] + options.tau * Math.sin(latitude)];
    centers.forEach((center, i) => {
        const sphere = node("g", { "data-feasible-constraint": i, "data-feasible-radius": options.tau });
        for (let axis = 0; axis < 3; axis++) {
            const circle = Array.from({ length: 49 }, (_, j): Point3 => { const a = PI2 * j / 48, point: [
                number,
                number,
                number
            ] = [...center]; point[(axis + 1) % 3] += options.tau * Math.cos(a); point[(axis + 2) % 3] += options.tau * Math.sin(a); return point; });
            sphere.append(node("path", { d: path(circle, options.project), fill: "none", stroke: constraintColor, "stroke-width": 1, opacity: .25 }));
        }
        constraints.append(sphere);
        const latitudes = 16, longitudes = 32;
        const grid = Array.from({ length: latitudes + 1 }, (_, a) => Array.from({ length: longitudes }, (_, b) => sphereAt(center, -Math.PI / 2 + Math.PI * a / latitudes, PI2 * b / longitudes)));
        for (let a = 0; a < latitudes; a++)
            for (let b = 0; b < longitudes; b++) {
                const next = (b + 1) % longitudes, corners = [grid[a]![b]!, grid[a]![next]!, grid[a + 1]![next]!, grid[a + 1]![b]!];
                if (!corners.every(point => isTranslationFeasible(point, centers, options.tau)))
                    continue;
                sampled = true;
                intersection.append(node("path", { d: path(corners, options.project, true), fill: feasibleColor, "fill-opacity": .2, stroke: feasibleColor, "stroke-opacity": .12, "stroke-width": .4 }));
            }
    });
    parent.append(constraints, intersection);
    if (centers.length) {
        const center = minimumEnclosingBall(centers).center;
        if (isTranslationFeasible(center, centers, options.tau)) {
            const [cx, cy] = options.project(center);
            parent.append(node("circle", { cx, cy, r: 2.5, fill: feasibleColor, "data-feasible-witness": "true" }));
            sampled = true;
        }
    }
    return sampled;
}
function poseAngle(transform: readonly number[], branch: OrientationBranch): number {
    const sign = branch === "improper" ? -1 : 1;
    return Math.atan2(sign * transform[4]!, sign * transform[0]!);
}
function transformBranch(transform: readonly number[]): OrientationBranch {
    return transform[0]! * transform[5]! - transform[1]! * transform[4]! < 0 ? "improper" : "proper";
}
const dot = (a: Point3, b: Point3) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
const unit = (point: Point3): Point3 => { const length = norm(point) || 1; return [point[0] / length, point[1] / length, point[2] / length]; };
const cross = (a: Point3, b: Point3): Point3 => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
function tubeCamera(options: FeasibleSetOptions) {
    const origin = options.project([0, 0, 0]), axes: Point3[] = [[1, 0, 0], [0, 1, 0], [0, 0, 1]];
    const projected = axes.map(axis => options.project(axis));
    const right = unit(projected.map(p => p[0] - origin[0]) as unknown as Point3);
    const up = unit(projected.map(p => origin[1] - p[1]) as unknown as Point3);
    const originDepth = options.depth?.([0, 0, 0]) ?? 0;
    const view = options.depth ? unit(axes.map(axis => options.depth!(axis) - originDepth) as unknown as Point3) : unit(cross(right, up));
    const light = unit([-.45 * right[0] + .4 * up[0] + .8 * view[0], -.45 * right[1] + .4 * up[1] + .8 * view[1], -.45 * right[2] + .4 * up[2] + .8 * view[2]]);
    return { view, light, depth: options.depth ?? ((point: Point3) => dot(point, view)) };
}
interface TubeFace {
    points: Point3[];
    normal: Point3;
    depth: number;
    cap?: boolean;
}
function filledTube(parent: SVGElement, options: FeasibleSetOptions, source: Point3, target: Point3, thetaScale: number, branch: OrientationBranch, index: number, camera: ReturnType<typeof tubeCamera>) {
    const tube = node("g", { "data-feasible-constraint": index, "data-feasible-radius": options.tau, "data-tube-rendering": "filled-surface", opacity: .2 });
    if (options.tau === 0) {
        const curve = Array.from({ length: 97 }, (_, j) => planarTubePoint(source, target, -Math.PI + PI2 * j / 96, 0, 0, thetaScale, branch));
        tube.append(node("path", { d: path(curve, options.project), fill: "none", stroke: constraintColor, "stroke-width": 1.4 }));
        parent.append(tube);
        return;
    }
    const thetaSteps = 72, alphaSteps = 32;
    const grid = Array.from({ length: thetaSteps + 1 }, (_, i) => Array.from({ length: alphaSteps }, (_, j) => planarTubePoint(source, target, -Math.PI + PI2 * i / thetaSteps, PI2 * j / alphaSteps, options.tau, thetaScale, branch)));
    const faces: TubeFace[] = [];
    for (let i = 0; i < thetaSteps; i++) {
        const theta = -Math.PI + PI2 * (i + .5) / thetaSteps, rotated = rotatePlanar(source, theta, branch);
        for (let j = 0; j < alphaSteps; j++) {
            const alpha = PI2 * (j + .5) / alphaSteps, c = Math.cos(alpha), s = Math.sin(alpha);
            const normal = unit([thetaScale * c, thetaScale * s, -c * rotated[1] + s * rotated[0]]);
            if (dot(normal, camera.view) <= 0)
                continue;
            const next = (j + 1) % alphaSteps, points = [grid[i]![j]!, grid[i]![next]!, grid[i + 1]![next]!, grid[i + 1]![j]!];
            faces.push({ points, normal, depth: points.reduce((sum, point) => sum + camera.depth(point), 0) / 4 });
        }
    }
    for (const sign of [-1, 1]) {
        const normal: Point3 = [0, 0, sign];
        if (dot(normal, camera.view) <= 0)
            continue;
        const points = Array.from({ length: 65 }, (_, j) => planarTubePoint(source, target, sign * Math.PI, PI2 * j / 64, options.tau, thetaScale, branch));
        faces.push({ points, normal, depth: points.reduce((sum, point) => sum + camera.depth(point), 0) / points.length, cap: true });
    }
    faces.sort((a, b) => a.depth - b.depth);
    let shade = "", fragments: string[] = [], hasCap = false;
    const flush = () => {
        if (!fragments.length)
            return;
        tube.append(node("path", { d: fragments.join(" "), fill: shade, stroke: shade, "stroke-width": .3, "stroke-linejoin": "round", "data-tube-surface": hasCap ? "end-cap" : "side" }));
        fragments = [];
        hasCap = false;
    };
    for (const face of faces) {
        const brightness = .25 + .75 * Math.max(0, dot(face.normal, camera.light));
        const bucket = Math.round(brightness * 10) / 10;
        const fill = `rgb(${Math.round(46 + 83 * bucket)} ${Math.round(111 + 61 * bucket)} ${Math.round(151 + 47 * bucket)})`;
        if (fill !== shade || face.cap) {
            flush();
            shade = fill;
        }
        fragments.push(path(face.points, options.project, true));
        hasCap ||= !!face.cap;
        if (face.cap)
            flush();
    }
    flush();
    parent.append(tube);
}
function renderPlanarTubes(parent: SVGElement, options: FeasibleSetOptions, source: readonly Point3[], target: readonly Point3[], thetaScale: number): boolean {
    const branch = options.optimizer === "proper" ? "proper" : options.reflectionBranch ?? "proper";
    const tubes = node("g", { "data-feasible-constraints": "rotation-tubes", "data-orientation-branch": branch, "data-theta-display-scale": thetaScale });
    const camera = tubeCamera(options), ordered = source.map((point, i) => ({ point, target: target[i]!, i, depth: camera.depth([target[i]![0], target[i]![1], 0]) })).sort((a, b) => a.depth - b.depth);
    for (const entry of ordered)
        filledTube(tubes, options, entry.point, entry.target, thetaScale, branch, entry.i, camera);
    parent.append(tubes);
    const slices = new Set(Array.from({ length: 65 }, (_, j) => -Math.PI + PI2 * j / 64));
    if (options.transform && transformBranch(options.transform) === branch) {
        const theta = poseAngle(options.transform, branch), width = Math.min(.05, options.tau / Math.max(1, ...source.map(norm)) / 4);
        for (const delta of [-width, 0, width])
            slices.add(Math.max(-Math.PI, Math.min(Math.PI, theta + delta)));
    }
    let sampled = false;
    const intersection = node("g", { "data-feasible-intersection": "sampled-rotation-slices", "data-angle-units": "radians" });
    for (const theta of [...slices].sort((a, b) => a - b)) {
        const centers = planarTranslationCenters(source, target, theta, branch), boundary = diskIntersectionBoundary(centers, options.tau, 64);
        if (!boundary.length)
            continue;
        sampled = true;
        const points = boundary.map((p): Point3 => [p[0], p[1], theta * thetaScale]);
        if (points.length === 1) {
            const [cx, cy] = options.project(points[0]!);
            intersection.append(node("circle", { cx, cy, r: 2, fill: feasibleColor, "data-feasible-slice-angle": theta }));
        }
        else
            intersection.append(node("path", { d: path(points, options.project, true), fill: feasibleColor, "fill-opacity": .24, stroke: feasibleColor, "stroke-width": .8, "stroke-opacity": .6, "data-feasible-slice-angle": theta }));
    }
    parent.append(intersection);
    if (options.transform && transformBranch(options.transform) === branch) {
        marker(parent, [options.transform[3]!, options.transform[7]!, poseAngle(options.transform, branch) * thetaScale], options);
    }
    return sampled;
}
export function renderFeasibleSet(svg: SVGSVGElement, options: FeasibleSetOptions): FeasibleSetRenderResult {
    const thetaScale = feasibleAngleScale(options), approximate = feasibleSetIsSpatial(options);
    if (options.dimension === 3 && options.optimizer !== "translation")
        throw new Error("The 3D rigid-motion feasible set has six continuous dimensions");
    const { source, target } = selectedClouds(options), group = node("g", { "data-feasible-set": options.optimizer, "data-feasible-dimension": options.dimension, "data-constraint-count": source.length });
    group.append(node("title", {}, options.optimizer !== "translation" ? `Each tube is one correspondence constraint in (tx, ty, theta); theta is in radians. Green cross-sections are sampled intersections.${options.optimizer === "rigid" ? " The two determinant branches are shown separately." : ""}` : options.dimension === 3 ? "Translation constraints are tau-balls centered at q_i - R p_i. Green patches are sampled surfaces inside every ball." : "Translation constraints are tau-disks centered at q_i - R p_i. Green is their exact intersection."));
    svg.append(group);
    let sampledIntersection: boolean;
    if (options.optimizer === "translation") {
        const centers = translationCenters(source, target, options.transform);
        sampledIntersection = options.dimension === 2 ? renderPlanarDisks(group, options, centers) : renderSpatialBalls(group, options, centers);
        if (options.transform)
            marker(group, [options.transform[3]!, options.transform[7]!, options.transform[11]!], options);
    }
    else
        sampledIntersection = renderPlanarTubes(group, options, source, target, thetaScale);
    return { thetaScale, approximate, sampledIntersection };
}
