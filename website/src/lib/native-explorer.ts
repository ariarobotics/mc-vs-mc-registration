import { renderToString } from "katex";
import { explorerPresets, presetOptimizer, pointsInDimension, buildExample, consistencyGraph, type ExplorerEdits, type ExplorerState, type ExplorerOptimizer } from "./explorer-model";
import { renderFeasibleSet, feasibleSetPoints, feasibleSetIsSpatial, feasibleAngleScale, type FeasibleSetOptions, type OrientationBranch } from "./feasible-set";
import { formatDisplayNumber as format } from "./display-number";
import { motionShells, motionSlice, nearestAllowedPoint, type MotionPlane, type Point2 } from "./pairwise-region.ts";
import { renderPairwiseRegion } from "./pairwise-overlay";
type Point3 = readonly [
    number,
    number,
    number
];
type Scene = ReturnType<typeof buildExample>;
type Preset = typeof explorerPresets[number];
type State = ExplorerState;
type Camera = {
    center: Point3;
    scale: number;
    zoom: number;
    panX: number;
    panY: number;
    yaw: number;
    pitch: number;
    locked: boolean;
    width: number;
    height: number;
    spatial: boolean;
    thetaScale?: number;
};
type View = {
    svg: SVGSVGElement;
    votes: boolean;
    camera: Camera;
};
const NS = "http://www.w3.org/2000/svg";
const color = { source: "#cb8b3c", target: "#437fa5", fit: "#278675", ink: "#355a46", muted: "#98aa9a", fail: "#c6735e" };
const roundSlider = (n: number) => Math.round((n + Number.EPSILON) * 100) / 100;
const math = (s: string) => renderToString(s, { throwOnError: false, output: "htmlAndMathml", trust: false });
const distance = (a: Point3, b: Point3) => Math.hypot(...a.map((v, i) => v - b[i]!));
const clone = (ps: readonly Point3[]) => ps.map(p => [...p] as Point3);
const key = (kind: string, i: number) => `${kind}:${i}`;
function svgNode<K extends keyof SVGElementTagNameMap>(name: K, attrs: Record<string, string | number> = {}, text?: string) {
    const node = document.createElementNS(NS, name);
    Object.entries(attrs).forEach(([k, v]) => node.setAttribute(k, String(v)));
    if (text !== undefined)
        node.textContent = text;
    return node;
}
export function mountExplorer(root: HTMLElement) {
    const get = <T extends Element = HTMLElement>(s: string) => root.querySelector<T>(s)!;
    const graph = get<SVGSVGElement>("[data-graph]"), examples = get<HTMLSelectElement>("[data-example]");
    const tau = get<HTMLInputElement>("[data-tau]"), epsilon = get<HTMLInputElement>("[data-epsilon]");
    const scale = get<HTMLInputElement>("[data-scale]"), count = get<HTMLSelectElement>("[data-count]");
    const newCamera = (): Camera => ({ center: [0, 0, 0], scale: 1, zoom: 1, panX: 0, panY: 0, yaw: -.55, pitch: .55, locked: false, width: 560, height: 390, spatial: false });
    const views: View[] = [{ svg: get<SVGSVGElement>("[data-geometry]"), votes: false, camera: newCamera() }, { svg: get<SVGSVGElement>("[data-feasible]"), votes: true, camera: newCamera() }];
    let optimizer: ExplorerOptimizer = "translation", dimension: 2 | 3 = 2;
    let preset: Preset = explorerPresets[0], state: State = { ...preset.defaults, optimizer, dimension }, edited: ExplorerEdits | undefined;
    let feasibleOpen = false, reflectionBranch: OrientationBranch = "proper";
    const optimizerInputs = root.querySelectorAll<HTMLButtonElement>("button[data-optimizer]"), branchInput = get<HTMLSelectElement>("[data-branch]");
    let scene: Scene, network: ReturnType<typeof consistencyGraph>, highlight = -1, selection = new Set<string>();
    let preserveEdges = true, inspection: {
        kind: "source" | "target";
        index: number;
    } | undefined;
    let animationEndpoints: Point3[] = [];
    let blend = 0, aligned = false, playing = false, frameId = 0, rebuildTimer: ReturnType<typeof setTimeout> | undefined;
    let lastDown = { time: 0, kind: "", index: -1, x: 0, y: 0 };
    type MotionRegion = ReturnType<typeof motionSlice> & {
        plane: MotionPlane;
    };
    type Drag = {
        view: View;
        kind: string;
        indices: Set<string>;
        x: number;
        y: number;
        camera: Camera;
        pan: boolean;
        source: Point3[];
        target: Point3[];
        transform: readonly number[] | undefined;
        moved: boolean;
        anchor?: Point3;
        motion?: MotionRegion;
        lastAllowed?: Point2;
    };
    let drag: Drag | undefined;
    const show = (s: string, on: boolean) => { get<HTMLElement>(s).hidden = !on; };
    function rotate(p: Point3, c: Camera): Point3 {
        if (!c.spatial)
            return p;
        const x = Math.cos(c.yaw) * p[0] - Math.sin(c.yaw) * p[1], y = Math.sin(c.yaw) * p[0] + Math.cos(c.yaw) * p[1];
        return [x, Math.cos(c.pitch) * p[2] - Math.sin(c.pitch) * y, Math.cos(c.pitch) * y + Math.sin(c.pitch) * p[2]];
    }
    function inverseScreen(x: number, y: number, c: Camera): Point3 {
        if (!c.spatial)
            return [x, y, 0];
        const yy = -Math.sin(c.pitch) * y, z = Math.cos(c.pitch) * y;
        return [Math.cos(c.yaw) * x + Math.sin(c.yaw) * yy, -Math.sin(c.yaw) * x + Math.cos(c.yaw) * yy, z];
    }
    function project(p: Point3, c: Camera): [
        number,
        number
    ] {
        const r = rotate(p.map((v, i) => v - c.center[i]!) as unknown as Point3, c), s = c.scale * c.zoom;
        return [c.width / 2 + c.panX + r[0] * s, c.height / 2 + c.panY - r[1] * s];
    }
    function inversePose(p: Point3, transform = scene.fitTransform): Point3 {
        if (!transform)
            return p;
        const d = [p[0] - transform[3]!, p[1] - transform[7]!, p[2] - transform[11]!];
        return [0, 1, 2].map(j => transform[j]! * d[0]! + transform[4 + j]! * d[1]! + transform[8 + j]! * d[2]!) as unknown as Point3;
    }
    const targetAt = (i: number): Point3 => { const p = scene.target[i]!, end = inversePose(p); return p.map((v, a) => v * (1 - blend) + end[a]! * blend) as unknown as Point3; };
    function movingSelection(kind: string, index: number): Set<string> {
        const k = key(kind, index), selected = selection.has(k) ? selection : new Set([k]);
        return new Set(preserveEdges ? [...selected].filter(k => k.startsWith(`${kind}:`)) : selected);
    }
    function motionRegion(kind: string, index: number, indices: ReadonlySet<string>, source: readonly Point3[], target: readonly Point3[], c: Camera): MotionRegion | undefined {
        if (!preserveEdges || (kind !== "source" && kind !== "target" && kind !== "displacement"))
            return;
        if ([...indices].some(k => !k.startsWith(`${kind}:`)))
            return;
        const cloud = kind === "source" ? "source" : "target", moving = [...indices].map(k => Number(k.split(":")[1])), anchor = (cloud === "source" ? source : target)[index]!;
        const plane: MotionPlane = { origin: anchor, x: inverseScreen(1, 0, c), y: inverseScreen(0, 1, c) };
        return { ...motionSlice(motionShells(source, target, network.edges, moving, cloud, scene.mode, state.epsilon, index), plane), plane };
    }
    function inspectedRegion(view: View): MotionRegion | undefined {
        if (!inspection || !preserveEdges || playing)
            return;
        if (drag && drag.kind !== "view")
            return drag.motion;
        const { kind, index } = inspection;
        return motionRegion(kind, index, movingSelection(kind, index), scene.source, scene.target.map((_, i) => targetAt(i)), view.camera);
    }
    function feasibleOptions(view = views[1]!): FeasibleSetOptions {
        return { source: scene.source, target: scene.target, tau: state.tau, optimizer, dimension,
            project: p => project(p, view.camera), depth: p => rotate(p.map((v, i) => v - view.camera.center[i]!) as unknown as Point3, view.camera)[2], pxPerUnit: view.camera.scale * view.camera.zoom,
            transform: scene.fitTransform, aligned: aligned && !!scene.consensusCertified, reflectionBranch, thetaScale: view.camera.thetaScale };
    }
    function viewport(view: View) {
        const bounds = view.svg.getBoundingClientRect();
        view.camera.width = Math.max(1, bounds.width);
        view.camera.height = Math.max(1, bounds.height);
        view.camera.spatial = view.votes ? feasibleSetIsSpatial({ optimizer, dimension }) : dimension === 3;
        view.svg.setAttribute("viewBox", `0 0 ${view.camera.width} ${view.camera.height}`);
    }
    function fitCamera(view: View) {
        const c = view.camera;
        if (c.locked)
            return;
        if (view.votes && optimizer !== "translation")
            c.thetaScale = feasibleAngleScale(feasibleOptions(view));
        const points = view.votes ? feasibleSetPoints(feasibleOptions(view)) : [...scene.source, ...scene.target, ...scene.target.map(p => inversePose(p)), ...animationEndpoints];
        if (view.votes && optimizer === "rigid" && dimension === 2)
            points.push(...feasibleSetPoints({ ...feasibleOptions(view), reflectionBranch: reflectionBranch === "proper" ? "improper" : "proper" }));
        points.push([0, 0, 0]);
        const min = [0, 1, 2].map(i => Math.min(...points.map(p => p[i]!))), max = [0, 1, 2].map(i => Math.max(...points.map(p => p[i]!)));
        c.center = min.map((v, i) => (v + max[i]!) / 2) as unknown as Point3;
        if (view.votes) {
            const rotated = points.map(p => rotate(p.map((v, i) => v - c.center[i]!) as unknown as Point3, c));
            const span = (axis: number) => Math.max(.5, Math.max(...rotated.map(p => p[axis]!)) - Math.min(...rotated.map(p => p[axis]!)));
            c.scale = Math.min(Math.max(30, c.width - 42) / span(0), Math.max(30, c.height - 30) / span(1));
            c.panX = -(Math.min(...rotated.map(p => p[0])) + Math.max(...rotated.map(p => p[0]))) / 2 * c.scale;
            c.panY = (Math.min(...rotated.map(p => p[1])) + Math.max(...rotated.map(p => p[1]))) / 2 * c.scale;
            c.locked = true;
            return;
        }
        const radius = Math.max(.6, ...points.map(p => distance(p, c.center)));
        const fitScale = c.spatial ? Math.max(25, Math.min(c.width - 70, c.height - 50)) / (2 * radius) : Math.min(Math.max(35, c.width - 100) / Math.max(1, max[0]! - min[0]!), Math.max(35, c.height - 65) / Math.max(1, max[1]! - min[1]!));
        const ideal = 50 / fitScale, magnitude = 10 ** Math.floor(Math.log10(ideal));
        const unit = [1, 2, 5, 10].map(n => n * magnitude).find(n => n >= ideal)!;
        c.scale = 50 / unit;
        c.locked = true;
    }
    const gridStep = (c: Camera) => { const ideal = 32 / (c.scale * c.zoom), m = 10 ** Math.floor(Math.log10(ideal)); return [1, 2, 5, 10].map(n => n * m).find(n => n >= ideal)!; };
    function line(parent: SVGElement, a: Point3, b: Point3, c: Camera, stroke: string, width = 1.3, dash?: string, opacity = 1) {
        const [x1, y1] = project(a, c), [x2, y2] = project(b, c), node = svgNode("line", { x1, y1, x2, y2, stroke, "stroke-width": width, opacity });
        if (dash)
            node.setAttribute("stroke-dasharray", dash);
        parent.append(node);
    }
    function latex(parent: SVGElement, x: number, y: number, expression: string, fill: string, attrs: Record<string, string | number> = {}) {
        const foreign = svgNode("foreignObject", { x, y, width: 75, height: 30, "pointer-events": "none", ...attrs });
        const span = document.createElementNS("http://www.w3.org/1999/xhtml", "span");
        span.setAttribute("class", "point-math");
        span.style.color = fill;
        span.innerHTML = math(expression);
        foreign.append(span);
        parent.append(foreign);
    }
    function dot(parent: SVGElement, p: Point3, i: number, kind: string, c: Camera) {
        const [cx, cy] = project(p, c), fill = kind === "source" ? color.source : color.target, selected = selection.has(key(kind, i)), inspected = inspection?.index === i && inspection.kind === kind, active = highlight === i || selected || inspected;
        const group = svgNode("g", { "data-point-index": i, "data-point-kind": kind, "data-point-position": JSON.stringify(p), "data-selected": String(selected), "data-inspected": String(inspected), tabindex: 0, role: "button", "aria-pressed": String(selected), "aria-label": `${kind} point ${i + 1}; click for allowed motion, drag to move, Shift-click to select` });
        group.append(svgNode("circle", { cx, cy, r: 15, fill: "transparent" }));
        if (active)
            group.append(svgNode("circle", { cx, cy, r: 12, fill, opacity: .13, stroke: selected ? fill : "none", "stroke-width": 1.5 }));
        group.append(svgNode("circle", { cx, cy, r: kind === "source" ? (active ? 9 : 7.7) : (active ? 6.8 : 5.8), fill, stroke: "#fffefa", "stroke-width": 2 }));
        latex(group, kind === "source" ? cx - 40 : cx + 10, kind === "source" ? cy + 8 : cy - 22, `${kind === "source" ? "p" : kind === "target" ? "q" : String.raw `\mu`}_{${i + 1}}`, fill);
        group.append(svgNode("title", {}, p.map(format).join(", ")));
        parent.append(group);
    }
    function drawAxes(parent: SVGElement, c: Camera, labels: string[], spatial: boolean) {
        const step = gridStep(c), axes = svgNode("g", { "data-axis-origin": "0,0,0", "data-axis-length": 2.5 * step });
        [0, 1, ...(spatial ? [2] : [])].forEach(i => {
            const end = [0, 0, 0] as [
                number,
                number,
                number
            ];
            end[i] = 2.5 * step;
            const stroke = ["#c27954", "#4e9371", "#5081ac"][i]!;
            line(axes, [0, 0, 0], end, c, stroke, 1.6);
            const [x, y] = project(end, c);
            latex(axes, Math.max(4, Math.min(c.width - 42, x + 4)), Math.max(4, Math.min(c.height - 28, y - 15)), labels[i]!, stroke, { "data-spatial-axis": labels[i]! });
        });
        parent.append(axes);
    }
    function ground(parent: SVGElement, c: Camera, labels: string[]) {
        const step = gridStep(c), s = c.scale * c.zoom, sp = Math.sin(c.pitch);
        const groundAt = (sx: number, sy: number): Point3 => { const x = (sx - c.width / 2 - c.panX) / s, y = (c.height / 2 + c.panY - sy) / s, yy = (-y - Math.cos(c.pitch) * c.center[2]) / sp; return [c.center[0] + Math.cos(c.yaw) * x + Math.sin(c.yaw) * yy, c.center[1] - Math.sin(c.yaw) * x + Math.cos(c.yaw) * yy, 0]; };
        const corners = [[-30, -30], [c.width + 30, -30], [c.width + 30, c.height + 30], [-30, c.height + 30]].map(([x, y]) => groundAt(x!, y!));
        const minX = Math.floor(Math.min(...corners.map(p => p[0])) / step) * step - step, maxX = Math.max(...corners.map(p => p[0])) + step;
        const minY = Math.floor(Math.min(...corners.map(p => p[1])) / step) * step - step, maxY = Math.max(...corners.map(p => p[1])) + step;
        const grid = svgNode("g", { "data-spatial-grid": "XY", "data-grid-step": step, "data-grid-z": 0, opacity: .5 });
        const xs = step * Math.max(1, Math.ceil((maxX - minX) / step / 120)), ys = step * Math.max(1, Math.ceil((maxY - minY) / step / 120));
        for (let x = minX; x <= maxX; x += xs)
            line(grid, [x, minY, 0], [x, maxY, 0], c, "#cbd8c6", .8);
        for (let y = minY; y <= maxY; y += ys)
            line(grid, [minX, y, 0], [maxX, y, 0], c, "#cbd8c6", .8);
        parent.append(grid);
        drawAxes(parent, c, labels, true);
    }
    function planarGrid(svg: SVGSVGElement, c: Camera, votes: boolean) {
        const step = gridStep(c), [ox, oy] = project([0, 0, 0], c), px = step * c.scale * c.zoom, id = votes ? "feasible-grid" : "point-grid";
        const pattern = svgNode("pattern", { id, width: px, height: px, x: ox, y: oy, patternUnits: "userSpaceOnUse" });
        pattern.append(svgNode("path", { d: `M0 ${px}V0H${px}`, fill: "none", stroke: "#cbd8c6", "stroke-width": .8, opacity: .52 }));
        const defs = svgNode("defs");
        defs.append(pattern);
        svg.append(defs, svgNode("rect", { width: c.width, height: c.height, fill: `url(#${id})`, "data-planar-grid": "true", "data-grid-step": step }));
        const [x, y] = project([0, 0, 0], c);
        svg.append(svgNode("line", { x1: 0, y1: y, x2: c.width, y2: y, stroke: "#afc6b9", opacity: .55 }), svgNode("line", { x1: x, y1: 0, x2: x, y2: c.height, stroke: "#afc6b9", opacity: .55 }));
        drawAxes(svg, c, votes ? [String.raw ` t_x`, String.raw `t_y`] : ["x", "y"], false);
    }
    function drawView(view: View) {
        if (view.votes && !feasibleOpen)
            return;
        viewport(view);
        fitCamera(view);
        const { svg, camera: c } = view, s = c.scale * c.zoom;
        svg.replaceChildren(svgNode("title", {}, view.votes ? "Feasible sets" : "Point correspondences"));
        const labels = view.votes ? (optimizer === "translation" ? [String.raw `t_x`, String.raw `t_y`, String.raw `t_z`] : [String.raw `t_x`, String.raw `t_y`, String.raw `\theta`]) : ["x", "y", "z"];
        if (c.spatial)
            ground(svg, c, labels);
        else
            planarGrid(svg, c, view.votes);
        if (!view.votes) {
            const region = inspectedRegion(view);
            if (region && inspection)
                renderPairwiseRegion(svg, { ...region, index: inspection.index, kind: inspection.kind, dimension, project: p => project(p, c) });
            const legend = get<HTMLElement>("[data-motion-legend]");
            legend.hidden = !region;
            get("[data-motion-label]").textContent = region ? (region.shells.length ? (dimension === 3 ? "Allowed motion (section)" : "Allowed motion") : "Unrestricted motion") : "Allowed motion";
            root.dataset.motionConstraintCount = String(region?.shells.length ?? 0);
            root.dataset.motionLocked = String(preserveEdges);
            root.dataset.motionVisible = String(!!region);
        }
        const shapes = svgNode("g");
        if (view.votes) {
            const result = renderFeasibleSet(svg, feasibleOptions(view));
            svg.dataset.approximate = String(result.approximate);
            svg.dataset.sampledIntersection = String(result.sampledIntersection);
            if (optimizer === "translation")
                (scene.displacements ?? []).forEach((p, i) => dot(shapes, p, i, "displacement", c));
        }
        else {
            scene.source.forEach((p, i) => {
                const q = targetAt(i), within = distance(p, q) <= state.tau + 1e-8;
                line(shapes, p, q, c, aligned ? (within ? color.fit : color.fail) : color.muted, highlight === i ? 2.3 : 1.2, "4 5", .55);
                if (aligned) {
                    const [cx, cy] = project(q, c);
                    shapes.append(svgNode("circle", { cx, cy, r: state.tau * s, fill: within ? "#27867508" : "#c6735e08", stroke: within ? color.fit : color.fail, "stroke-width": 1.2, opacity: .7, "data-tau-circle": i, "data-within-tau": String(within), "data-tau-radius": state.tau }));
                }
            });
            const markers = [...scene.source.map((p, i) => ({ p, i, kind: "source" })), ...scene.target.map((_, i) => ({ p: targetAt(i), i, kind: "target" }))];
            if (c.spatial)
                markers.sort((a, b) => rotate(a.p, c)[2] - rotate(b.p, c)[2]);
            markers.forEach(({ p, i, kind }) => dot(shapes, p, i, kind, c));
        }
        const bx = c.width - 65, by = c.height - 27;
        svg.append(shapes, svgNode("path", { d: `M${bx - 25} ${by}v4h50v-4`, fill: "none", stroke: "#8b9c88" }), svgNode("text", { x: bx, y: by + 20, "text-anchor": "middle", fill: "#71836b", "font-size": 11, "data-view-scale": "true" }, format(50 / s)));
        svg.dataset.cameraScale = String(s);
        svg.dataset.blend = String(blend);
        svg.dataset.dimension = String(scene.dimension);
    }
    function drawGraph() {
        if (feasibleOpen)
            return;
        const bounds = graph.getBoundingClientRect(), width = Math.max(1, bounds.width), height = Math.max(1, bounds.height);
        graph.setAttribute("viewBox", `0 0 ${width} ${height}`);
        const radius = Math.max(20, Math.min(width, height) / 2 - 23), nodeRadius = Math.min(17, Math.max(10, height * .075));
        const n = scene.source.length, clique = new Set(network.maximumClique), nodes = Array.from({ length: n }, (_, i) => [width / 2 + radius * Math.cos(-Math.PI / 2 + i * 2 * Math.PI / n), height / 2 + radius * Math.sin(-Math.PI / 2 + i * 2 * Math.PI / n)]);
        graph.replaceChildren(svgNode("title", {}, `${network.edges.length} edges, maximum clique ${network.cliqueNumber}`));
        const edgeSet = new Set(network.edges.map(e => `${e.a}:${e.b}`));
        const hoverEnabled = n < 10 && network.edges.length <= 10;
        graph.dataset.edgeHoverEnabled = String(hoverEnabled);
        for (let a = 0; a < n; a++)
            for (let b = a + 1; b < n; b++) {
                const present = edgeSet.has(`${a}:${b}`), gap = scene.mode === "translation" ? distance(scene.displacements![a]!, scene.displacements![b]!) : Math.abs(distance(scene.source[a]!, scene.source[b]!) - distance(scene.target[a]!, scene.target[b]!));
                const edge = svgNode("g", { "data-graph-edge": `${a}:${b}`, "data-edge-gap": gap, "data-edge-compatible": String(present) });
                const coords = { x1: nodes[a]![0]!, y1: nodes[a]![1]!, x2: nodes[b]![0]!, y2: nodes[b]![1]! };
                if (hoverEnabled)
                    edge.append(svgNode("line", { ...coords, stroke: "transparent", "stroke-width": 12, "pointer-events": "stroke", "data-edge-hit": "true" }));
                const line = svgNode("line", { ...coords, stroke: present ? (clique.has(a) && clique.has(b) ? "#72a992" : "#bdcfc0") : "#c6735e", "stroke-width": present && (highlight === a || highlight === b) ? 2.5 : 1.6, opacity: present ? .75 : .5, "pointer-events": "none", "data-edge-visible": "true" });
                if (!present) {
                    line.setAttribute("stroke-dasharray", "3 5");
                    line.dataset.missingEdge = "true";
                }
                edge.append(line);
                graph.append(edge);
            }
        nodes.forEach(([cx, cy], i) => { const active = highlight === i || inspection?.index === i || [...selection].some(k => k.endsWith(`:${i}`)), g = svgNode("g", { "data-point-index": i, "data-point-kind": "graph", role: "button", tabindex: 0, "aria-label": `Correspondence ${i + 1}` }); if (active)
            g.append(svgNode("circle", { cx: cx!, cy: cy!, r: nodeRadius + 6, fill: color.fit, opacity: .12 })); g.append(svgNode("circle", { cx: cx!, cy: cy!, r: nodeRadius, fill: clique.has(i) ? color.fit : "#edf2e9", stroke: active ? color.ink : "#fffefa", "stroke-width": 2 }), svgNode("text", { x: cx!, y: cy! + 4, "text-anchor": "middle", fill: clique.has(i) ? "#fff" : "#72866f", "font-family": "system-ui", "font-size": 12, "font-weight": 600 }, String(i + 1))); graph.append(g); });
        get("[data-edge-count]").textContent = `${network.edges.length} edges`;
    }
    function measurements() {
        const exact = scene.consensusCertified, count = scene.consensusCount, upper = scene.consensusUpperBound ?? count;
        get("[data-native-metrics]").innerHTML = `<div><dt>Maximum consensus</dt><dd>${math(`${scene.mode === "translation" ? String.raw `\operatorname{MC}^{(t)}` : (state.proper ? String.raw `\operatorname{MC}^{+}` : String.raw `\operatorname{MC}`)}(${format(state.tau)})${exact ? "=" : "\\in"}${exact ? count : `[${count},${upper}]`}`)}${exact ? "" : "<small>Achieved count and upper bound</small>"}</dd></div><div><dt>Maximum clique</dt><dd>${math((scene.mode === "translation" ? String.raw `\omega(G_\epsilon^{(t)})` : String.raw `\omega(G_\epsilon)`) + `=${network.cliqueNumber}`)}</dd></div>`;
        root.dataset.consensusCount = String(count);
        root.dataset.consensusUpperBound = String(upper);
        root.dataset.consensusCertified = String(exact);
    }
    function populateExamples() {
        examples.replaceChildren();
        const names: Record<ExplorerOptimizer, string> = { translation: "Translation", proper: "Proper Rigid Motion", rigid: "Rigid Motion" };
        const available = explorerPresets;
        for (const mode of [optimizer, ...(["translation", "proper", "rigid"] as const).filter(m => m !== optimizer)]) {
            const group = document.createElement("optgroup");
            group.label = names[mode];
            available.filter(p => presetOptimizer(p) === mode).forEach(p => group.append(new Option(`${p.label} · ${p.dimension}D`, p.id)));
            if (group.children.length)
                examples.append(group);
        }
        examples.append(new Option("Custom", "custom"));
    }
    function refreshControls() {
        const custom = !!edited?.source || !!edited?.target, supported = optimizer === "translation" || dimension === 2;
        show("[data-scale-control]", !!preset.controls.ell && !custom);
        show("[data-count-control]", !!preset.controls.count && !custom);
        show(".construction-options", !custom && (!!preset.controls.ell || !!preset.controls.count));
        if (!supported)
            feasibleOpen = false;
        show("[data-feasible-panel]", feasibleOpen);
        show("[data-graph-panel]", !feasibleOpen);
        show("[data-graph-legend]", !feasibleOpen);
        show("[data-feasible-legend]", feasibleOpen);
        show("[data-edge-count]", !feasibleOpen);
        show("[data-edge-tooltip]", false);
        show("[data-branch-control]", feasibleOpen && optimizer === "rigid" && dimension === 2);
        get("[data-analysis-panel]").classList.toggle("feasible-open", feasibleOpen);
        const toggle = get<HTMLButtonElement>("[data-feasible-toggle]");
        toggle.disabled = !supported;
        toggle.setAttribute("aria-pressed", String(feasibleOpen));
        toggle.title = supported ? `${feasibleOpen ? "Hide" : "Show"} feasible sets` : "A 3D rigid pose has six continuous parameters";
        root.dataset.customized = String(custom);
        root.dataset.preset = preset.id;
        root.dataset.optimizer = optimizer;
        root.dataset.dimension = String(dimension);
        examples.value = custom ? "custom" : preset.id;
        optimizerInputs.forEach(b => b.setAttribute("aria-pressed", String(b.dataset.optimizer === optimizer)));
        root.querySelectorAll<HTMLButtonElement>("button[data-dimension]").forEach(b => b.setAttribute("aria-pressed", String(Number(b.dataset.dimension) === dimension)));
        get<HTMLButtonElement>("[data-add]").disabled = scene.source.length >= 12;
        get<HTMLButtonElement>("[data-add]").title = scene.source.length >= 12 ? "Up to twelve correspondences per example" : "Add correspondence";
        for (const [range, number, value] of [[tau, get<HTMLInputElement>("[data-tau-number]"), state.tau], [epsilon, get<HTMLInputElement>("[data-epsilon-number]"), state.epsilon]] as const) {
            range.max = String(Math.max(Number(range.max), value));
            range.value = String(value);
            if (document.activeElement !== number)
                number.value = String(value);
        }
        if (document.activeElement !== get("[data-scale-number]"))
            get<HTMLInputElement>("[data-scale-number]").value = String(state.ell);
        get("[data-graph-title]").innerHTML = feasibleOpen ? "Feasible sets" : `Consistency graph ${math(scene.mode === "translation" ? String.raw `G_\epsilon^{(t)}` : String.raw `G_\epsilon`)}`;
        get("[data-graph-title]").setAttribute("title", feasibleOpen ? "Constraints for every correspondence; green shows their intersection. Spatial surfaces and rotation cross-sections are sampled." : "");
        get("[data-construction-formula]").innerHTML = scene.formula.split(String.raw `,\qquad`).map((s, i) => `<div><span class="formula-label">${i === 0 ? "Alignment Error" : "Maximum Consensus"}</span><span class="formula-math">${math(s)}</span></div>`).join("");
    }
    const redraw = () => { views.forEach(drawView); drawGraph(); };
    function rebuild() {
        if (rebuildTimer)
            clearTimeout(rebuildTimer);
        rebuildTimer = undefined;
        try {
            scene = buildExample(preset.id, state, edited);
            if (inspection && inspection.index >= scene.source.length)
                inspection = undefined;
            selection = new Set([...selection].filter(k => Number(k.split(":")[1]) < scene.source.length));
            if (!views[0]!.camera.locked && scene.mode === "rigid") {
                const alternative = buildExample(preset.id, { ...state, optimizer: optimizer === "proper" ? "rigid" : "proper" }, edited);
                animationEndpoints = scene.target.map(p => inversePose(p, alternative.fitTransform));
            }
            network = consistencyGraph(scene.source, scene.target, state.epsilon, scene.mode);
            epsilon.max = String(Math.max(preset.epsilonRange?.[1] ?? 4, network.delta * 1.2, state.epsilon));
            refreshControls();
            redraw();
            measurements();
            show("[data-explorer-error]", false);
        }
        catch (e) {
            get("[data-explorer-error]").textContent = e instanceof Error ? e.message : "Unable to draw the example";
            show("[data-explorer-error]", true);
        }
    }
    function schedule() { if (rebuildTimer)
        clearTimeout(rebuildTimer); rebuildTimer = setTimeout(rebuild, 60); }
    function stop() { playing = false; cancelAnimationFrame(frameId); get("[data-align-label]").textContent = "Align"; }
    function choose(id: string) {
        stop();
        inspection = undefined;
        preset = explorerPresets.find(p => p.id === id) ?? explorerPresets[0];
        optimizer = presetOptimizer(preset);
        dimension = preset.dimension;
        state = { ...preset.defaults, optimizer, dimension, proper: optimizer === "proper" };
        edited = undefined;
        animationEndpoints = [];
        selection.clear();
        highlight = -1;
        blend = 0;
        aligned = false;
        views.forEach(v => v.camera = newCamera());
        reflectionBranch = "proper";
        branchInput.value = reflectionBranch;
        populateExamples();
        get("[data-scale-control] > span").innerHTML = `${preset.parameterLabel ?? "Scale"} ${math(preset.parameterExpression ?? String.raw `\ell`)}`;
        const ellRange = preset.ellRange ?? [1, 100], log = ellRange[0] > 0 && ellRange[1] / ellRange[0] > 30;
        scale.dataset.logarithmic = String(log);
        scale.min = String(log ? Math.log10(ellRange[0]) : ellRange[0]);
        scale.max = String(log ? Math.log10(ellRange[1]) : ellRange[1]);
        scale.step = "any";
        scale.value = String(log ? Math.log10(state.ell) : state.ell);
        const scaleNumber = get<HTMLInputElement>("[data-scale-number]");
        scaleNumber.min = String(ellRange[0]);
        scaleNumber.max = String(ellRange[1]);
        scaleNumber.value = String(state.ell);
        tau.min = "0";
        tau.max = String(Math.max(preset.tauRange?.[1] ?? 3, state.tau));
        tau.step = "any";
        tau.value = String(state.tau);
        epsilon.min = "0";
        epsilon.step = "any";
        epsilon.value = String(state.epsilon);
        get<HTMLInputElement>("[data-tau-number]").value = String(state.tau);
        get<HTMLInputElement>("[data-epsilon-number]").value = String(state.epsilon);
        const cr = preset.countRange ?? [3, 12];
        count.replaceChildren(...Array.from({ length: cr[1] - cr[0] + 1 }, (_, i) => new Option(String(i + cr[0]), String(i + cr[0]))));
        count.value = String(state.count);
        rebuild();
        if (optimizer === "rigid" && scene.fitTransform) {
            reflectionBranch = scene.fitTransform[0]! * scene.fitTransform[5]! - scene.fitTransform[1]! * scene.fitTransform[4]! < 0 ? "improper" : "proper";
            branchInput.value = reflectionBranch;
            if (feasibleOpen)
                drawView(views[1]!);
        }
    }
    optimizerInputs.forEach(b => b.addEventListener("click", () => { if (b.dataset.optimizer === optimizer)
        return; stop(); edited = { source: clone(scene.source), target: clone(scene.target), initialTransform: scene.fitTransform }; optimizer = b.dataset.optimizer as ExplorerOptimizer; state.optimizer = optimizer; state.proper = optimizer === "proper"; aligned = false; blend = 0; views[1]!.camera = newCamera(); populateExamples(); rebuild(); if (optimizer === "rigid" && scene.fitTransform) {
        reflectionBranch = scene.fitTransform[0]! * scene.fitTransform[5]! - scene.fitTransform[1]! * scene.fitTransform[4]! < 0 ? "improper" : "proper";
        branchInput.value = reflectionBranch;
        if (feasibleOpen)
            drawView(views[1]!);
    } }));
    root.querySelectorAll<HTMLButtonElement>("button[data-dimension]").forEach(b => b.addEventListener("click", () => {
        const next = Number(b.dataset.dimension) as 2 | 3;
        if (next === dimension)
            return;
        stop();
        dimension = next;
        state.dimension = dimension;
        edited = { source: pointsInDimension(scene.source, dimension), target: pointsInDimension(scene.target, dimension) };
        aligned = false;
        blend = 0;
        selection.clear();
        inspection = undefined;
        animationEndpoints = [];
        views.forEach(v => v.camera = newCamera());
        populateExamples();
        rebuild();
    }));
    get("[data-feasible-toggle]").addEventListener("click", () => { feasibleOpen = !feasibleOpen; refreshControls(); requestAnimationFrame(() => { drawView(views[1]!); drawGraph(); }); });
    get<HTMLButtonElement>("[data-preserve-edges]").addEventListener("click", () => { preserveEdges = !preserveEdges; get("[data-preserve-edges]").setAttribute("aria-pressed", String(preserveEdges)); redraw(); });
    branchInput.addEventListener("change", () => { reflectionBranch = branchInput.value as OrientationBranch; drawView(views[1]!); });
    examples.addEventListener("change", () => { if (examples.value === "custom") {
        edited = { source: clone(scene.source), target: clone(scene.target), initialTransform: scene.fitTransform };
        refreshControls();
    }
    else
        choose(examples.value); });
    get("[data-reset]").addEventListener("click", () => { stop(); blend = 0; aligned = false; selection.clear(); inspection = undefined; highlight = -1; redraw(); });
    for (const [name, range] of [["tau", tau], ["epsilon", epsilon]] as const) {
        range.addEventListener("input", () => { state[name] = roundSlider(Number(range.value)); range.value = String(state[name]); get<HTMLInputElement>(`[data-${name}-number]`).value = range.value; stop(); schedule(); });
        get<HTMLInputElement>(`[data-${name}-number]`).addEventListener("input", e => { const input = e.target as HTMLInputElement, v = input.valueAsNumber; if (Number.isFinite(v) && v >= 0) {
            state[name] = v;
            range.max = String(Math.max(Number(range.max), v));
            range.value = String(v);
            stop();
            schedule();
        } });
    }
    scale.addEventListener("input", () => { state.ell = roundSlider(scale.dataset.logarithmic === "true" ? 10 ** Number(scale.value) : Number(scale.value)); scale.value = String(scale.dataset.logarithmic === "true" ? Math.log10(state.ell) : state.ell); get<HTMLInputElement>("[data-scale-number]").value = String(state.ell); edited = undefined; stop(); schedule(); });
    get<HTMLInputElement>("[data-scale-number]").addEventListener("input", e => { const v = (e.target as HTMLInputElement).valueAsNumber; if (Number.isFinite(v) && v >= Number(get<HTMLInputElement>("[data-scale-number]").min) && v <= Number(get<HTMLInputElement>("[data-scale-number]").max)) {
        state.ell = v;
        scale.value = String(scale.dataset.logarithmic === "true" ? Math.log10(v) : v);
        edited = undefined;
        stop();
        schedule();
    } });
    count.addEventListener("change", () => { state.count = Number(count.value); edited = undefined; stop(); rebuild(); });
    get("[data-add]").addEventListener("click", () => { stop(); const c = views[0]!.camera, step = gridStep(c), i = scene.source.length, p: Point3 = [c.center[0] + ((i % 3) - 1) * step, c.center[1] + ((i % 2) - .5) * step, scene.dimension === 3 ? c.center[2] : 0], q: Point3 = [p[0] + step, p[1] + .5 * step, p[2]]; edited = { source: [...clone(scene.source), p], target: [...clone(scene.target), q], initialTransform: scene.fitTransform }; aligned = false; blend = 0; rebuild(); });
    get("[data-align]").addEventListener("click", () => {
        if (playing) {
            stop();
            return;
        }
        rebuild();
        aligned = true;
        blend = 0;
        playing = true;
        get("[data-align-label]").textContent = "Pause";
        drawView(views[1]!);
        const start = performance.now(), duration = matchMedia("(prefers-reduced-motion: reduce)").matches ? 0 : 1100;
        function frame(now: number) { if (!playing)
            return; const t = duration === 0 ? 1 : Math.min(1, (now - start) / duration); blend = t * t * (3 - 2 * t); drawView(views[0]!); if (t < 1)
            frameId = requestAnimationFrame(frame);
        else
            stop(); }
        frameId = requestAnimationFrame(frame);
    });
    function snapDelta(d: Drag, delta: Point3): Point3 {
        if (!d.anchor)
            return delta;
        const c = d.view.camera, step = gridStep(c), limit = Math.min(step * .06, 1.7 / (c.scale * c.zoom));
        const point = d.anchor.map((v, i) => v + delta[i]!) as unknown as Point3;
        const correction = [0, 0, 0];
        for (const axis of [0, 1]) {
            const nearest = Math.round(point[axis]! / step) * step, difference = nearest - point[axis]!;
            if (Math.abs(difference) <= limit)
                correction[axis] = difference;
        }
        const snapped = point.map((v, i) => v + correction[i]!) as unknown as Point3;
        const before = project(point, c), after = project(snapped, c);
        return Math.hypot(after[0] - before[0], after[1] - before[1]) <= 2.5 ? delta.map((v, i) => v + correction[i]!) as unknown as Point3 : delta;
    }
    function move(d: Drag, delta: Point3) {
        if (d.motion?.shells.length) {
            const { plane, shells } = d.motion;
            const desired: Point2 = [delta.reduce((sum, v, i) => sum + v * plane.x[i]!, 0), delta.reduce((sum, v, i) => sum + v * plane.y[i]!, 0)];
            const allowed = d.motion.empty ? (d.lastAllowed ?? [0, 0]) : nearestAllowedPoint(desired, shells, d.lastAllowed ?? [0, 0]);
            d.lastAllowed = allowed;
            delta = plane.x.map((v, i) => v * allowed[0] + plane.y[i]! * allowed[1]) as unknown as Point3;
        }
        const source = clone(d.source), target = clone(d.target), moved = new Set<string>();
        d.indices.forEach(k => { const [kind, s] = k.split(":"), i = Number(s), endpoint = key(kind === "source" ? "source" : "target", i); if (moved.has(endpoint))
            return; moved.add(endpoint); const ps = kind === "source" ? source : target, p = ps[i]!; ps[i] = p.map((v, a) => v + delta[a]!) as unknown as Point3; });
        edited = { source, target, initialTransform: d.transform };
        aligned = false;
        blend = 0;
        rebuild();
    }
    function coordinates(e: PointerEvent, svg: SVGSVGElement): [
        number,
        number
    ] { const p = new DOMPoint(e.clientX, e.clientY).matrixTransform(svg.getScreenCTM()!.inverse()); return [p.x, p.y]; }
    views.forEach(view => {
        const svg = view.svg;
        svg.addEventListener("pointerdown", e => {
            if (e.button !== 0 && e.button !== 2)
                return;
            const node = (e.target as Element).closest<SVGGElement>("[data-point-index]"), [x, y] = coordinates(e, svg), kind = node?.dataset.pointKind ?? "view", index = node ? Number(node.dataset.pointIndex) : -1;
            if (node && e.button === 0) {
                const k = key(kind, index), now = performance.now(), double = lastDown.kind === kind && lastDown.index === index && now - lastDown.time < 350 && Math.hypot(x - lastDown.x, y - lastDown.y) < 8;
                stop();
                if (kind === "displacement") {
                    blend = 0;
                    aligned = false;
                }
                else if (blend > 0 && blend < 1)
                    blend = 1;
                inspection = kind === "source" || kind === "target" ? { kind, index } : kind === "displacement" ? { kind: "target", index } : undefined;
                if (double) {
                    selection = new Set(scene.source.map((_, i) => key(kind, i)));
                    lastDown.time = 0;
                }
                else {
                    lastDown = { time: now, kind, index, x, y };
                    if (e.shiftKey) {
                        if (selection.has(k))
                            selection.delete(k);
                        else
                            selection.add(k);
                    }
                }
                const indices = movingSelection(kind, index);
                drag = { view, kind, indices, x, y, camera: { ...view.camera }, pan: false, source: clone(scene.source), target: view.votes ? clone(scene.target) : scene.target.map((_, i) => targetAt(i)), transform: scene.fitTransform, moved: false, anchor: kind === "source" ? scene.source[index] : kind === "displacement" ? scene.displacements?.[index] : targetAt(index) };
                drag.motion = motionRegion(kind, index, indices, drag.source, drag.target, drag.camera);
            }
            else
                drag = { view, kind: "view", indices: new Set(), x, y, camera: { ...view.camera }, pan: !(e.shiftKey || e.button === 2), source: [], target: [], transform: undefined, moved: false };
            svg.setPointerCapture(e.pointerId);
            svg.classList.add("dragging");
            e.preventDefault();
            redraw();
        });
        svg.addEventListener("pointermove", e => {
            if (!drag) {
                const node = (e.target as Element).closest<SVGGElement>("[data-point-index]"), i = node ? Number(node.dataset.pointIndex) : -1;
                if (highlight !== i) {
                    highlight = i;
                    redraw();
                }
                return;
            }
            if (drag.view !== view)
                return;
            const [x, y] = coordinates(e, svg), dx = x - drag.x, dy = y - drag.y;
            if (Math.hypot(dx, dy) < 2 && !drag.moved)
                return;
            drag.moved = true;
            if (drag.kind === "view") {
                if (view.camera.spatial && !drag.pan) {
                    view.camera.yaw = drag.camera.yaw + dx * .009;
                    view.camera.pitch = Math.max(.08, Math.min(1.48, drag.camera.pitch + dy * .009));
                }
                else {
                    view.camera.panX = drag.camera.panX + dx;
                    view.camera.panY = drag.camera.panY + dy;
                }
                drawView(view);
            }
            else
                move(drag, snapDelta(drag, inverseScreen(dx / (drag.camera.scale * drag.camera.zoom), -dy / (drag.camera.scale * drag.camera.zoom), drag.camera)));
        });
        const finish = () => { if (!drag || drag.view !== view)
            return; if (!drag.moved && drag.kind === "view") {
            selection.clear();
            inspection = undefined;
        } drag = undefined; svg.classList.remove("dragging"); redraw(); };
        svg.addEventListener("pointerup", finish);
        svg.addEventListener("pointercancel", finish);
        svg.addEventListener("lostpointercapture", finish);
        svg.addEventListener("pointerleave", () => { if (!drag && highlight !== -1) {
            highlight = -1;
            redraw();
        } });
        svg.addEventListener("dblclick", e => { const node = (e.target as Element).closest<SVGGElement>("[data-point-index]"); if (node) {
            selection = new Set(scene.source.map((_, i) => key(node.dataset.pointKind!, i)));
            redraw();
        } });
        svg.addEventListener("contextmenu", e => e.preventDefault());
        svg.addEventListener("wheel", e => { e.preventDefault(); view.camera.zoom = Math.max(.03, Math.min(40, view.camera.zoom * Math.exp(-e.deltaY * .002))); drawView(view); }, { passive: false });
        svg.addEventListener("keydown", e => { const node = (e.target as Element).closest<SVGGElement>("[data-point-index]"); if (!node || !["Enter", " ", "ArrowLeft", "ArrowRight", "ArrowUp", "ArrowDown"].includes(e.key))
            return; const kind = node.dataset.pointKind!, i = Number(node.dataset.pointIndex), k = key(kind, i); inspection = kind === "source" || kind === "target" ? { kind, index: i } : kind === "displacement" ? { kind: "target", index: i } : undefined; if (e.key === "Enter" || e.key === " ") {
            e.preventDefault();
            selection.has(k) ? selection.delete(k) : selection.add(k);
            redraw();
        }
        else {
            e.preventDefault();
            stop();
            if (kind === "displacement") {
                blend = 0;
                aligned = false;
            }
            else if (blend > 0 && blend < 1)
                blend = 1;
            const c = view.camera, step = 6 / (c.scale * c.zoom), d: Drag = { view, kind, indices: movingSelection(kind, i), x: 0, y: 0, camera: c, pan: false, source: clone(scene.source), target: view.votes ? clone(scene.target) : scene.target.map((_, i) => targetAt(i)), transform: scene.fitTransform, moved: true };
            d.motion = motionRegion(kind, i, d.indices, d.source, d.target, c);
            move(d, inverseScreen(e.key === "ArrowRight" ? step : e.key === "ArrowLeft" ? -step : 0, e.key === "ArrowUp" ? step : e.key === "ArrowDown" ? -step : 0, c));
        } svg.querySelector<SVGGElement>(`[data-point-kind="${kind}"][data-point-index="${i}"]`)?.focus(); });
    });
    graph.addEventListener("pointermove", e => {
        if (drag)
            return;
        const node = (e.target as Element).closest<SVGGElement>("[data-point-index]"), i = node ? Number(node.dataset.pointIndex) : -1;
        if (highlight !== i) {
            highlight = i;
            redraw();
        }
        const edge = (e.target as Element).closest<SVGGElement>("[data-graph-edge]"), tooltip = get<HTMLElement>("[data-edge-tooltip]");
        if (edge && graph.dataset.edgeHoverEnabled === "true") {
            const [a, b] = edge.dataset.graphEdge!.split(":").map(Number), compatible = edge.dataset.edgeCompatible === "true", bounds = get(".analysis-plots").getBoundingClientRect();
            tooltip.innerHTML = math(String.raw `\delta${scene.mode === "translation" ? "^{(t)}" : ""}_{${a! + 1},${b! + 1}}\approx ${format(Number(edge.dataset.edgeGap))}`);
            tooltip.dataset.compatible = String(compatible);
            tooltip.hidden = false;
            tooltip.style.left = `${Math.max(6, Math.min(bounds.width - tooltip.offsetWidth - 6, e.clientX - bounds.left + 12))}px`;
            tooltip.style.top = `${Math.max(6, Math.min(bounds.height - tooltip.offsetHeight - 6, e.clientY - bounds.top + 12))}px`;
        }
        else
            tooltip.hidden = true;
    });
    graph.addEventListener("pointerleave", () => { highlight = -1; show("[data-edge-tooltip]", false); redraw(); });
    graph.addEventListener("click", e => { const node = (e.target as Element).closest<SVGGElement>("[data-point-index]"); if (node) {
        stop();
        if (blend > 0 && blend < 1)
            blend = 1;
        const i = Number(node.dataset.pointIndex);
        selection = new Set([key("source", i)]);
        inspection = { kind: "source", index: i };
        redraw();
    } });
    graph.addEventListener("keydown", e => { if (e.key === "Enter" || e.key === " ") {
        const node = (e.target as Element).closest<SVGGElement>("[data-point-index]");
        if (!node)
            return;
        e.preventDefault();
        const i = node.dataset.pointIndex;
        node.dispatchEvent(new MouseEvent("click", { bubbles: true }));
        graph.querySelector<SVGGElement>(`[data-point-index="${i}"]`)?.focus();
    } });
    let resizeFrame = 0;
    const observer = new ResizeObserver(() => {
        cancelAnimationFrame(resizeFrame);
        resizeFrame = requestAnimationFrame(() => {
            if (!scene)
                return;
            for (const view of views) {
                if (view.votes && !feasibleOpen)
                    continue;
                const bounds = view.svg.getBoundingClientRect();
                if (Math.abs(bounds.width - view.camera.width) > 1 || Math.abs(bounds.height - view.camera.height) > 1) {
                    view.camera.locked = false;
                    view.camera.panX = 0;
                    view.camera.panY = 0;
                }
                drawView(view);
            }
            drawGraph();
        });
    });
    views.forEach(v => observer.observe(v.svg));
    window.addEventListener("pagehide", () => { observer.disconnect(); cancelAnimationFrame(resizeFrame); cancelAnimationFrame(frameId); if (rebuildTimer)
        clearTimeout(rebuildTimer); }, { once: true });
    choose(preset.id);
}
