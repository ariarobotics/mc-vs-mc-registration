import { planePoint, type MotionPlane, type PlanarShell } from "./pairwise-region.ts";
const NS = "http://www.w3.org/2000/svg";
function node<K extends keyof SVGElementTagNameMap>(name: K, attributes: Record<string, string | number> = {}) {
    const element = document.createElementNS(NS, name);
    for (const [key, value] of Object.entries(attributes))
        element.setAttribute(key, String(value));
    return element;
}
function annulusPath(shell: PlanarShell): string {
    const [x, y] = shell.center;
    const circle = (r: number) => `M${x - r},${y}a${r},${r} 0 1,0 ${2 * r},0a${r},${r} 0 1,0 ${-2 * r},0Z`;
    return shell.outer === 0 ? `M${x},${y}Z` : circle(shell.outer) + (shell.inner > 0 ? circle(shell.inner) : "");
}
export function renderPairwiseRegion(svg: SVGSVGElement, options: {
    shells: readonly PlanarShell[];
    plane: MotionPlane;
    project: (point: readonly [
        number,
        number,
        number
    ]) => readonly [
        number,
        number
    ];
    empty: boolean;
    index: number;
    kind: string;
    dimension: 2 | 3;
}) {
    const { shells, plane, project } = options;
    const origin = project(plane.origin), x = project(planePoint([1, 0], plane)), y = project(planePoint([0, 1], plane));
    const group = node("g", {
        "data-motion-region": options.kind,
        "data-motion-point": options.index,
        "data-motion-constraint-count": shells.length,
        "data-motion-plane": options.dimension === 3 ? "camera-section" : "XY",
        "data-motion-empty": String(options.empty),
        "pointer-events": "none",
        transform: `matrix(${x[0] - origin[0]} ${x[1] - origin[1]} ${y[0] - origin[0]} ${y[1] - origin[1]} ${origin[0]} ${origin[1]})`,
    });
    const defs = node("defs"), boundaries = node("g");
    shells.forEach((shell, i) => {
        const path = annulusPath(shell), id = `pairwise-motion-${i}`;
        const clip = node("clipPath", { id, clipPathUnits: "userSpaceOnUse" });
        clip.append(node("path", { d: path, "clip-rule": "evenodd", "fill-rule": "evenodd" }));
        defs.append(clip);
        group.append(node("path", {
            d: path, fill: "#278675", "fill-opacity": .035, "fill-rule": "evenodd",
            stroke: "#6ca08f", "stroke-width": 1, "stroke-opacity": .5,
            "vector-effect": "non-scaling-stroke", "stroke-dasharray": "3 3",
            "data-motion-shell": `${shell.pair[0]}:${shell.pair[1]}`,
            "data-motion-inner": shell.inner, "data-motion-outer": shell.outer,
            "data-motion-center": JSON.stringify(shell.center),
        }));
        boundaries.append(node("path", {
            d: path, fill: "none", stroke: "#278675", "stroke-width": 2.4,
            "vector-effect": "non-scaling-stroke",
        }));
    });
    group.prepend(defs);
    if (shells.length && !options.empty) {
        const intersection = node("g", { "data-motion-intersection": "true" });
        let clipped: SVGElement = intersection;
        shells.forEach((_, i) => {
            const next = node("g", { "clip-path": `url(#pairwise-motion-${i})` });
            clipped.append(next);
            clipped = next;
        });
        clipped.append(node("path", { d: annulusPath(shells[0]!), fill: "#278675", "fill-opacity": .22, "fill-rule": "evenodd" }), boundaries);
        group.append(intersection);
    }
    svg.append(group);
}
