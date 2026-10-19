import * as THREE from "three";
import { OrbitControls } from "three/addons/controls/OrbitControls.js";
import { loadRealPair, knownStudyGraphMaximum, type RealPair, type RealSample, type PointProposal, type StudySet } from "./real-world-cache";
import { realDisplayFrame, targetDisplayPose, transformScan as transformPoints } from "./real-world-frame";
import { normalizeDisplayNumber } from "./display-number";
const SOURCE = "#d47a0b", TARGET = "#2c6eaa", CLIQUE = "#2f8b57";
const SVG_NS = "http://www.w3.org/2000/svg";
function robustBounds(points: Float32Array): THREE.Box3 {
    const bounds = new THREE.Box3();
    const count = points.length / 3;
    for (let axis = 0; axis < 3; axis++) {
        const values = Float32Array.from({ length: count }, (_, i) => points[i * 3 + axis]).sort();
        bounds.min.setComponent(axis, values[Math.floor((count - 1) * .01)] ?? 0);
        bounds.max.setComponent(axis, values[Math.ceil((count - 1) * .99)] ?? 0);
    }
    return bounds;
}
export async function mountRealWorldExplorer(root: HTMLElement) {
    const query = <T extends Element>(selector: string) => {
        const element = root.querySelector<T>(selector);
        if (!element)
            throw new Error(`Missing real scan control: ${selector}`);
        return element;
    };
    const canvas = query<HTMLCanvasElement>("[data-rw-canvas]");
    const graph = query<SVGSVGElement>("[data-rw-graph]");
    const edgeCanvas = query<HTMLCanvasElement>("[data-rw-graph-edges]");
    const edgeContext = edgeCanvas.getContext("2d")!;
    const sampleSelect = query<HTMLSelectElement>("[data-rw-sample]");
    const epsilon = query<HTMLInputElement>("[data-rw-epsilon]");
    let alignment = 0;
    const epsilonNumber = query<HTMLInputElement>("[data-rw-epsilon-number]");
    const tauNumber = query<HTMLInputElement>("[data-rw-tau-number]");
    const resetButton = query<HTMLButtonElement>("[data-rw-reset]");
    const setSelect = query<HTMLSelectElement>("[data-rw-set]");
    const tau = query<HTMLInputElement>("[data-rw-tau]");
    const animateButton = query<HTMLButtonElement>("[data-rw-animate]");
    const resetInputButton = query<HTMLButtonElement>("[data-rw-reset-input]");
    const graphToggle = query<HTMLButtonElement>("[data-rw-graph-toggle]");
    const graphPanel = query<HTMLElement>("[data-rw-graph-panel]");
    const placeholder = query<HTMLElement>("[data-rw-placeholder]");
    const loading = query<HTMLElement>("[data-rw-loading]");
    const manifestUrl = new URL(root.dataset.manifest!, document.baseURI);
    const manifestResponse = await fetch(manifestUrl);
    if (!manifestResponse.ok)
        throw new Error("The real scan examples could not load. Try again.");
    const samples = await manifestResponse.json() as RealSample[];
    if (!samples.length)
        throw new Error("No real scan examples are available.");
    const renderer = (() => {
        try {
            return new THREE.WebGLRenderer({ canvas, antialias: true, powerPreference: "high-performance" });
        }
        catch {
            throw new Error("The 3D view needs a browser with WebGL enabled.");
        }
    })();
    renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
    renderer.setClearColor(0xf4f7fa, 1);
    const scene = new THREE.Scene();
    const camera = new THREE.PerspectiveCamera(42, 1, .01, 3000);
    camera.up.set(0, 0, 1);
    const controls = new OrbitControls(camera, canvas);
    controls.enableDamping = true;
    controls.dampingFactor = .08;
    controls.zoomToCursor = true;
    controls.enablePan = true;
    controls.mouseButtons.LEFT = THREE.MOUSE.PAN;
    controls.mouseButtons.RIGHT = THREE.MOUSE.ROTATE;
    controls.screenSpacePanning = true;
    controls.minPolarAngle = .05;
    controls.maxPolarAngle = Math.PI * .49;
    const group = new THREE.Group();
    scene.add(group);
    const grid = new THREE.GridHelper(2, 20, 0xaebac5, 0xd7dee4);
    grid.rotation.x = Math.PI / 2;
    scene.add(grid);
    const axes = new THREE.AxesHelper(1);
    (axes.material as THREE.LineBasicMaterial).depthTest = false;
    axes.renderOrder = 2;
    scene.add(axes);
    const axisLabels = ["x", "y", "z"].map((label) => {
        const image = document.createElement("canvas");
        image.width = image.height = 64;
        const context = image.getContext("2d")!;
        context.font = "italic 38px Georgia";
        context.textAlign = "center";
        context.textBaseline = "middle";
        context.fillStyle = "#526b7b";
        context.fillText(label, 32, 32);
        const sprite = new THREE.Sprite(new THREE.SpriteMaterial({ map: new THREE.CanvasTexture(image), depthTest: false }));
        scene.add(sprite);
        return sprite;
    });
    let disposed = false, loadVersion = 0, visible = true, animationFrame = 0;
    let pair: RealPair | undefined;
    let activeSet: StudySet | undefined;
    let frame = new THREE.Matrix4();
    let frozenPose: {
        rotation: THREE.Quaternion;
        target: THREE.Vector3;
    } | undefined;
    let poseAnimation: {
        start: number;
        rotation: THREE.Quaternion;
        target: THREE.Vector3;
    } | undefined;
    let radius = 1;
    let center = new THREE.Vector3();
    let cameraBounds = new THREE.Box3();
    let sourcePositions: Float32Array = new Float32Array();
    let targetPositions: Float32Array = new Float32Array();
    let sourceCloud: THREE.Points | undefined, targetCloud: THREE.Points | undefined;
    const fittedRotation = new THREE.Quaternion(), fittedTranslation = new THREE.Vector3();
    const sourceDisplayRotation = new THREE.Quaternion(), sourceDisplayTranslation = new THREE.Vector3();
    let sourceDisplayPose: THREE.Matrix4 | undefined;
    const targetOffset = new THREE.Vector3();
    let matches: Array<{
        source: THREE.Vector3;
        target: THREE.Vector3;
    }> = [];
    let fullProposals: PointProposal[] = [];
    let highlights = new Set<number>();
    let graphState: {
        count: number;
        edgeCount: number;
        edges: Uint32Array;
        adjacency: Uint32Array;
        clique: {
            indices: number[];
            lowerBound: number;
            upperBound: number;
            certified: boolean;
        };
    } | undefined;
    let graphCoordinates: number[][] = [];
    let graphRequest = 0;
    let graphDirty = true;
    let graphDebounce = 0;
    let graphViewBox = { x: 0, y: 0, width: 320, height: 300 };
    const graphWorker = new Worker(new URL("./real-world-graph-worker.ts", import.meta.url), { type: "module" });
    const pendingGraphs = new Map<number, {
        resolve: (value: typeof graphState) => void;
        reject: (error: Error) => void;
    }>();
    graphWorker.addEventListener("message", (event) => {
        const pending = pendingGraphs.get(event.data.request);
        if (!pending)
            return;
        pendingGraphs.delete(event.data.request);
        if (event.data.error)
            pending.reject(new Error(event.data.error));
        else
            pending.resolve(event.data);
    });
    graphWorker.addEventListener("error", (event) => {
        pendingGraphs.forEach(pending => pending.reject(new Error(event.message || "The full graph could not be computed.")));
        pendingGraphs.clear();
    });
    const lines = new THREE.LineSegments(new THREE.BufferGeometry(), new THREE.LineBasicMaterial({ vertexColors: true, transparent: true, opacity: .88, depthWrite: false, depthTest: false }));
    const discCanvas = document.createElement("canvas");
    discCanvas.width = discCanvas.height = 32;
    const discContext = discCanvas.getContext("2d")!;
    discContext.fillStyle = "white";
    discContext.beginPath();
    discContext.arc(16, 16, 15, 0, 2 * Math.PI);
    discContext.fill();
    const discTexture = new THREE.CanvasTexture(discCanvas);
    const endpointHalos = new THREE.Points(new THREE.BufferGeometry(), new THREE.PointsMaterial({ color: "#fffefa", size: 13, sizeAttenuation: false, depthTest: false, depthWrite: false, transparent: true }));
    const sourceHandles = new THREE.Points(new THREE.BufferGeometry(), new THREE.PointsMaterial({ color: "#a55400", size: 8, sizeAttenuation: false, depthTest: false, depthWrite: false, transparent: true }));
    const targetHandles = new THREE.Points(new THREE.BufferGeometry(), new THREE.PointsMaterial({ color: "#194e7c", size: 8, sizeAttenuation: false, depthTest: false, depthWrite: false, transparent: true }));
    [endpointHalos, sourceHandles, targetHandles].forEach(object => { object.material.map = discTexture; object.material.alphaTest = .05; });
    const toleranceBalls = new THREE.Group();
    let toleranceMesh: THREE.InstancedMesh | undefined;
    const ballGeometry = new THREE.SphereGeometry(1, 12, 8);
    const ballMaterial = new THREE.MeshBasicMaterial({ color: "#ffffff", transparent: true, opacity: .09, depthWrite: false });
    const tauMatrix = new THREE.Matrix4(), tauScale = new THREE.Vector3(), tauColor = new THREE.Color(), tauRotation = new THREE.Quaternion();
    scene.add(toleranceBalls);
    lines.renderOrder = 3;
    sourceHandles.renderOrder = targetHandles.renderOrder = 5;
    endpointHalos.renderOrder = 4;
    const highlightedSources = new THREE.Points(new THREE.BufferGeometry(), (sourceHandles.material as THREE.PointsMaterial).clone());
    const highlightedTargets = new THREE.Points(new THREE.BufferGeometry(), (targetHandles.material as THREE.PointsMaterial).clone());
    const highlightedLines = new THREE.LineSegments(new THREE.BufferGeometry(), new THREE.LineBasicMaterial({ vertexColors: true, transparent: true, opacity: .88, depthWrite: false, depthTest: false }));
    highlightedSources.renderOrder = highlightedTargets.renderOrder = 5;
    highlightedLines.renderOrder = 4;
    scene.add(lines, highlightedLines, sourceHandles, targetHandles, highlightedSources, highlightedTargets, endpointHalos);
    const meters = (value: number) => {
        const displayed = normalizeDisplayNumber(value);
        return displayed < 1 ? `${(displayed * 100).toFixed(2)} cm` : `${displayed.toFixed(2)} m`;
    };
    function makePoints(points: Float32Array, color: string, size: number) {
        const geometry = new THREE.BufferGeometry();
        geometry.setAttribute("position", new THREE.BufferAttribute(points, 3));
        geometry.computeBoundingSphere();
        const material = new THREE.PointsMaterial({
            color, size, sizeAttenuation: true, transparent: true, opacity: .8, depthWrite: true,
        });
        return new THREE.Points(geometry, material);
    }
    function clearClouds() {
        for (const cloud of [sourceCloud, targetCloud]) {
            if (!cloud)
                continue;
            group.remove(cloud);
            cloud.geometry.dispose();
            const material = cloud.material;
            if (Array.isArray(material))
                material.forEach((m) => m.dispose());
            else
                material.dispose();
        }
    }
    const worldSource = (point: THREE.Vector3) => point.clone().applyQuaternion(sourceCloud!.quaternion).add(sourceCloud!.position);
    const worldTarget = (point: THREE.Vector3) => point.clone().applyQuaternion(targetCloud!.quaternion).add(targetCloud!.position);
    function updateMatches() {
        if (!pair || !sourceCloud || !targetCloud)
            return;
        toleranceBalls.visible = alignment > 0 || Boolean(poseAnimation);
        const positions: number[] = [], colors: number[] = [], strongPositions: number[] = [], strongColors: number[] = [];
        const sources: number[] = [], targets: number[] = [], strongSources: number[] = [], strongTargets: number[] = [], residuals: number[] = [];
        let inside = 0, balls = 0;
        const selectedResiduals: number[] = [];
        const visibleLines = true;
        matches.forEach((match, i) => {
            const source = worldSource(match.source), target = worldTarget(match.target);
            source.toArray(sources, sources.length);
            target.toArray(targets, targets.length);
            const residual = source.distanceTo(target);
            residuals.push(residual);
            const feasible = residual <= Number(tau.value) + 1e-9;
            const highlighted = highlights.has(i);
            if (highlighted) {
                selectedResiduals.push(residual);
                if (feasible)
                    inside++;
            }
            if (highlighted) {
                source.toArray(strongSources, strongSources.length);
                target.toArray(strongTargets, strongTargets.length);
                if (toleranceMesh) {
                    tauScale.setScalar(Number(tau.value));
                    tauMatrix.compose(target, tauRotation, tauScale);
                    toleranceMesh.setMatrixAt(balls, tauMatrix);
                    toleranceMesh.setColorAt(balls++, tauColor.set(feasible ? CLIQUE : "#a33768"));
                }
            }
            if (!visibleLines)
                return;
            const linePositions = highlighted ? strongPositions : positions, lineColors = highlighted ? strongColors : colors;
            source.toArray(linePositions, linePositions.length);
            target.toArray(linePositions, linePositions.length);
            const color = new THREE.Color(highlighted ? feasible ? CLIQUE : "#a33768" : "#8196a6");
            color.toArray(lineColors, lineColors.length);
            color.toArray(lineColors, lineColors.length);
        });
        if (toleranceMesh) {
            toleranceMesh.count = balls;
            toleranceMesh.instanceMatrix.needsUpdate = true;
            if (toleranceMesh.instanceColor)
                toleranceMesh.instanceColor.needsUpdate = true;
            toleranceMesh.computeBoundingSphere();
        }
        for (const [object, coordinates, vertexColors] of [[lines, positions, colors], [highlightedLines, strongPositions, strongColors]] as const) {
            object.geometry.setAttribute("position", new THREE.Float32BufferAttribute(coordinates, 3));
            object.geometry.setAttribute("color", new THREE.Float32BufferAttribute(vertexColors, 3));
            object.geometry.computeBoundingSphere();
        }
        (lines.material as THREE.LineBasicMaterial).opacity = .045;
        for (const [object, coordinates] of [[sourceHandles, sources], [targetHandles, targets], [highlightedSources, strongSources], [highlightedTargets, strongTargets], [endpointHalos, [...strongSources, ...strongTargets]]] as const) {
            object.geometry.setAttribute("position", new THREE.Float32BufferAttribute(coordinates, 3));
            object.geometry.computeBoundingSphere();
        }
        const size = matches.length > 100 ? 3.5 : 8;
        (sourceHandles.material as THREE.PointsMaterial).size = (targetHandles.material as THREE.PointsMaterial).size = size;
        (highlightedSources.material as THREE.PointsMaterial).size = (highlightedTargets.material as THREE.PointsMaterial).size = 8;
        query<HTMLOutputElement>("[data-rw-fit-error]").value = meters(Math.max(0, ...selectedResiduals));
        query<HTMLElement>("[data-rw-selected-count]").textContent = String(highlights.size);
        query<HTMLElement>("[data-rw-current-consensus]").textContent = `${inside} / ${highlights.size}`;
        root.dataset.selectedMaxResidual = String(Math.max(0, ...selectedResiduals));
        root.dataset.selectedWithinTolerance = String(inside);
        root.dataset.correspondenceCount = String(matches.length);
        root.dataset.highlightCount = String(highlights.size);
        root.dataset.visibleLineCount = String((positions.length + strongPositions.length) / 6);
    }
    function updatePose() {
        if (!sourceCloud || !targetCloud)
            return;
        sourceCloud.quaternion.copy(sourceDisplayRotation);
        sourceCloud.position.copy(sourceDisplayTranslation);
        if (frozenPose) {
            targetCloud.quaternion.copy(frozenPose.rotation);
            targetCloud.position.copy(frozenPose.target);
        }
        else {
            targetCloud.quaternion.identity().slerp(fittedRotation, alignment);
            targetCloud.position.copy(targetOffset).lerp(fittedTranslation, alignment);
        }
        root.dataset.alignmentFraction = String(alignment);
        updateMatches();
    }
    function updateFit() {
        if (!pair || !activeSet)
            return;
        const transform = frame.clone().multiply(new THREE.Matrix4().fromArray(activeSet.pose).transpose()).multiply(frame.clone().invert());
        if (!sourceDisplayPose) {
            sourceDisplayPose = transform.clone();
            sourceDisplayRotation.setFromRotationMatrix(sourceDisplayPose);
            sourceDisplayTranslation.setFromMatrixPosition(sourceDisplayPose);
        }
        const targetPose = targetDisplayPose(transform, sourceDisplayPose);
        fittedRotation.setFromRotationMatrix(targetPose);
        fittedTranslation.setFromMatrixPosition(targetPose);
        updatePose();
        updateCameraBounds();
    }
    function hasEdge(i: number, j: number) {
        if (!graphState)
            return false;
        const words = Math.ceil(graphState.count / 32);
        return (graphState.adjacency[i * words + (j >>> 5)] & (1 << (j & 31))) !== 0;
    }
    function drawGraphEdges() {
        if (!graphState)
            return;
        const bounds = edgeCanvas.getBoundingClientRect(), ratio = Math.min(window.devicePixelRatio, 2);
        edgeCanvas.width = Math.max(1, Math.round(bounds.width * ratio));
        edgeCanvas.height = Math.max(1, Math.round(bounds.height * ratio));
        const scale = edgeCanvas.width / graphViewBox.width;
        edgeContext.setTransform(scale, 0, 0, scale, -graphViewBox.x * scale, -graphViewBox.y * scale);
        const draw = (pairs: number[], color: string, opacity: number, width: number, dashed = false) => {
            if (!pairs.length)
                return;
            edgeContext.beginPath();
            edgeContext.strokeStyle = color;
            edgeContext.globalAlpha = opacity;
            edgeContext.lineWidth = width;
            edgeContext.setLineDash(dashed ? [2, 4] : []);
            for (let k = 0; k < pairs.length; k += 2) {
                const a = graphCoordinates[pairs[k]], b = graphCoordinates[pairs[k + 1]];
                edgeContext.moveTo(a[0], a[1]);
                edgeContext.lineTo(b[0], b[1]);
            }
            edgeContext.stroke();
        };
        const ordinary: number[] = [], highlighted: number[] = [];
        const stride = Math.max(1, Math.ceil(graphState.edgeCount / 16000));
        for (let edge = 0; edge < graphState.edgeCount; edge += stride) {
            const i = graphState.edges[edge * 2], j = graphState.edges[edge * 2 + 1];
            ordinary.push(i, j);
        }
        for (const [group, output] of [[[...highlights], highlighted]] as const) {
            if (group.length > 100)
                continue;
            for (let a = 0; a < group.length; a++)
                for (let b = a + 1; b < group.length; b++)
                    if (hasEdge(group[a], group[b]))
                        output.push(group[a], group[b]);
        }
        const missing: number[] = [];
        const pairCount = graphState.count * (graphState.count - 1) / 2;
        if (graphState.edgeCount < pairCount) {
            if (graphState.count <= 25)
                for (let i = 0; i < graphState.count; i++)
                    for (let j = i + 1; j < graphState.count; j++) {
                        if (!hasEdge(i, j))
                            missing.push(i, j);
                    }
            else
                for (let k = 0; k < 1200; k++) {
                    const i = (k * 197 + 37) % graphState.count, j = (k * 541 + 101) % graphState.count;
                    if (i !== j && !hasEdge(i, j))
                        missing.push(i, j);
                }
        }
        draw(missing, "#a33768", graphState.count > 100 ? .045 : .3, .5, true);
        draw(ordinary, "#7893a7", graphState.count > 100 ? .045 : .5, .45);
        draw(highlighted, CLIQUE, .72, .9);
        root.dataset.drawnGraphEdges = String(ordinary.length / 2);
    }
    function updateGraphHighlights() {
        graph.querySelectorAll<SVGGElement>("[data-match]").forEach(node => {
            node.dataset.highlighted = String(highlights.has(Number(node.dataset.match)));
        });
        drawGraphEdges();
    }
    function renderGraph() {
        const n = fullProposals.length;
        graphCoordinates = fullProposals.map((_, i) => {
            if (n < 30) {
                const angle = -Math.PI / 2 + i / n * Math.PI * 2;
                return [160 + Math.cos(angle) * 120, 150 + Math.sin(angle) * 120];
            }
            const radius = 126 * Math.sqrt((i + .5) / n), angle = i * Math.PI * (3 - Math.sqrt(5));
            return [160 + Math.cos(angle) * radius, 150 + Math.sin(angle) * radius];
        });
        const elements: SVGElement[] = [];
        const size = n < 30 ? 11 : Math.max(.75, Math.min(5, 42 / Math.sqrt(n)));
        fullProposals.forEach((proposal, i) => {
            const node = document.createElementNS(SVG_NS, "g");
            node.classList.add("rw-graph-node");
            node.setAttribute("transform", `translate(${graphCoordinates[i][0]},${graphCoordinates[i][1]})`);
            node.dataset.match = String(i);
            const circle = document.createElementNS(SVG_NS, "circle");
            circle.setAttribute("r", String(size));
            circle.dataset.radius = String(size);
            node.append(circle);
            if (n < 50) {
                const text = document.createElementNS(SVG_NS, "text");
                text.textContent = String(proposal.id + 1);
                node.append(text);
            }
            elements.push(node);
        });
        graph.dataset.large = String(n >= 50);
        graph.replaceChildren(...elements);
        updateGraphHighlights();
    }
    async function updateGraph() {
        if (!pair)
            return;
        const request = ++graphRequest;
        const resultPromise = new Promise<typeof graphState>((resolve, reject) => pendingGraphs.set(request, { resolve, reject }));
        const points = graphDirty ? pair.proposals.map(point => ({ source: point.source, target: point.target })) : undefined;
        graphDirty = false;
        graphWorker.postMessage({ request, matches: points, epsilon: Number(epsilon.value), seed: pair.study.fullClique, knownMaximum: knownStudyGraphMaximum(pair.study, Number(epsilon.value)) });
        const result = await resultPromise;
        if (disposed || request !== graphRequest || !result)
            return;
        graphState = result;
        epsilonNumber.value = Number(epsilon.value).toFixed(2);
        query<HTMLElement>("[data-rw-edge-count]").textContent = result.edgeCount.toLocaleString();
        query<HTMLElement>("[data-rw-clique-label]").textContent = result.clique.certified ? "Maximum clique" : "Clique bounds";
        query<HTMLElement>("[data-rw-clique-size]").textContent = result.clique.certified ? String(result.clique.lowerBound) : `${result.clique.lowerBound}–${result.clique.upperBound}`;
        query<HTMLElement>("[data-rw-graph-size]").textContent = `${result.count.toLocaleString()} matches`;
        root.dataset.graphCertified = String(result.clique.certified);
        root.dataset.graphCount = String(result.count);
        renderGraph();
        updateFit();
    }
    function scheduleGraph() {
        window.clearTimeout(graphDebounce);
        graphDebounce = window.setTimeout(() => void updateGraph().catch(reportLoadError), 75);
    }
    function resetCamera(includeAlignment = false) {
        if (sourceCloud && targetCloud) {
            sourceCloud.updateMatrix();
            targetCloud.updateMatrix();
            cameraBounds = robustBounds(transformPoints(sourcePositions, sourceCloud.matrix)).union(robustBounds(transformPoints(targetPositions, targetCloud.matrix)));
            if (includeAlignment) {
                const endPose = new THREE.Matrix4().compose(fittedTranslation, fittedRotation, new THREE.Vector3(1, 1, 1));
                cameraBounds.union(robustBounds(transformPoints(targetPositions, endPose)));
            }
            center = cameraBounds.getCenter(new THREE.Vector3());
            const currentSize = cameraBounds.getSize(new THREE.Vector3());
            radius = Math.max(currentSize.x, currentSize.y, currentSize.z, 1) * .5;
        }
        const direction = new THREE.Vector3(.94, -1.12, .66).normalize();
        const right = new THREE.Vector3().crossVectors(camera.up, direction).normalize();
        const up = new THREE.Vector3().crossVectors(direction, right);
        const size = cameraBounds.getSize(new THREE.Vector3());
        const verticalTan = Math.tan(THREE.MathUtils.degToRad(camera.fov / 2)) / 1.1;
        const horizontalTan = verticalTan * camera.aspect;
        let distance = .5;
        for (const x of [-.5, .5])
            for (const y of [-.5, .5])
                for (const z of [-.5, .5]) {
                    const corner = new THREE.Vector3(x * size.x, y * size.y, z * size.z);
                    distance = Math.max(distance, corner.dot(direction) + Math.max(Math.abs(corner.dot(right)) / horizontalTan, Math.abs(corner.dot(up)) / verticalTan));
                }
        camera.position.copy(center).addScaledVector(direction, distance);
        camera.near = Math.max(radius / 1500, .005);
        camera.far = radius * 25;
        camera.updateProjectionMatrix();
        controls.target.copy(center);
        controls.minDistance = radius * .08;
        controls.maxDistance = radius * 15;
        controls.update();
    }
    function cameraFitFactor(aspect: number) {
        return Math.max(1, 1 / aspect) * (1 + .1 * Math.max(0, Math.min(1, (1.5 - aspect) / .5)));
    }
    function updateTolerance() {
        tauNumber.value = Number(tau.value).toFixed(2);
        updateMatches();
    }
    function stopPoseAnimation() {
        if (poseAnimation && sourceCloud && targetCloud) {
            frozenPose = { rotation: targetCloud.quaternion.clone(), target: targetCloud.position.clone() };
        }
        poseAnimation = undefined;
    }
    function animateFit() {
        if (!sourceCloud || !targetCloud)
            return;
        stopPoseAnimation();
        const initial = { rotation: targetCloud.quaternion.clone(), target: targetCloud.position.clone() };
        const desired = fittedTranslation.clone();
        const alreadyFitted = initial.target.distanceTo(desired) < 1e-8 && initial.rotation.angleTo(fittedRotation) < 1e-8;
        if (alreadyFitted) {
            initial.rotation.identity();
            initial.target.copy(targetOffset);
        }
        frozenPose = undefined;
        if (window.matchMedia("(prefers-reduced-motion: reduce)").matches) {
            alignment = 1;
            updatePose();
            resetCamera();
            return;
        }
        targetCloud.quaternion.copy(initial.rotation);
        targetCloud.position.copy(initial.target);
        resetCamera(true);
        root.dataset.alignmentFraction = "animating";
        poseAnimation = { start: performance.now(), ...initial };
        updateMatches();
    }
    function setPointSet() {
        if (!pair)
            return;
        activeSet = pair.study.sets.find(set => set.id === setSelect.value);
        if (!activeSet) throw new Error("The selected alignment is missing.");
        highlights = new Set(activeSet.indices);
        root.dataset.alignmentId = activeSet.id;
        stopPoseAnimation();
        frozenPose = undefined;
        alignment = 1;
        updateFit();
        updateGraphHighlights();
        updateMatches();
    }
    function updateCameraBounds() {
        if (!sourceCloud || !targetCloud)
            return;
        const fitted = new THREE.Matrix4().compose(fittedTranslation, fittedRotation, new THREE.Vector3(1, 1, 1));
        cameraBounds = robustBounds(transformPoints(sourcePositions, sourceDisplayPose!))
            .union(robustBounds(targetPositions).translate(targetOffset))
            .union(robustBounds(transformPoints(targetPositions, fitted)));
        center = cameraBounds.getCenter(new THREE.Vector3());
        const size = cameraBounds.getSize(new THREE.Vector3());
        radius = Math.max(size.x, size.y, size.z, 1) * .5;
    }
    function updateGrid() {
        const worldPerPixel = 2 * camera.position.distanceTo(controls.target) * Math.tan(THREE.MathUtils.degToRad(camera.fov / 2)) / Math.max(canvas.clientHeight, 1);
        const desiredStep = Math.max(worldPerPixel * 55, .001);
        const magnitude = 10 ** Math.floor(Math.log10(desiredStep));
        const step = [1, 2, 5, 10].map(value => value * magnitude).find(value => value >= desiredStep)!;
        grid.scale.setScalar(step * 10);
        grid.position.set(Math.round(controls.target.x / step) * step, Math.round(controls.target.y / step) * step, 0);
        axes.scale.setScalar(step * 2.5);
        axisLabels.forEach((sprite, axis) => {
            sprite.position.set(0, 0, 0).setComponent(axis, step * 2.8);
            sprite.scale.setScalar(step * .45);
        });
        query<HTMLElement>("[data-rw-grid-scale]").textContent = `Grid: ${meters(step)}`;
    }
    const setDisabled = (disabled: boolean) => {
        [sampleSelect, epsilon, epsilonNumber, resetButton, setSelect, tau, tauNumber, animateButton, resetInputButton, graphToggle].forEach((element) => { element.disabled = disabled; });
    };
    async function loadSample(id: string) {
        const version = ++loadVersion;
        ++graphRequest;
        const sample = samples.find((item) => item.id === id)!;
        setDisabled(true);
        placeholder.hidden = false;
        loading.textContent = `Loading ${sample.title.toLowerCase()}…`;
        const nextPair = await loadRealPair(sample, manifestUrl);
        if (disposed || version !== loadVersion)
            return;
        loading.textContent = "Selecting point proposals…";
        await new Promise<void>((resolve) => requestAnimationFrame(() => resolve()));
        if (disposed || version !== loadVersion)
            return;
        clearClouds();
        pair = nextPair;
        sourceDisplayPose = undefined;
        graphState = undefined;
        graphDirty = true;
        graphViewBox = { x: 0, y: 0, width: 320, height: 300 };
        graph.setAttribute("viewBox", "0 0 320 300");
        frame = realDisplayFrame(pair, sample);
        sourcePositions = transformPoints(pair.source.points, frame);
        targetPositions = transformPoints(pair.target.points, frame);
        sourceCloud = makePoints(sourcePositions, SOURCE, sample.voxelSize * 1.4);
        targetCloud = makePoints(targetPositions, TARGET, sample.voxelSize * 1.4);
        group.add(sourceCloud, targetCloud);
        const sourceBounds = robustBounds(sourcePositions), targetBounds = robustBounds(targetPositions);
        const targetCenter = targetBounds.getCenter(new THREE.Vector3());
        const sourceSize = sourceBounds.getSize(new THREE.Vector3()), targetSize = targetBounds.getSize(new THREE.Vector3());
        const width = Math.max(sourceSize.x, targetSize.x, sourceSize.y * .7, targetSize.y * .7);
        targetOffset.set(width * 1.15 - targetCenter.x, -targetCenter.y, 0);
        epsilon.max = sample.dataset === "3DMatch" ? "1" : sample.dataset === "ETH" ? "2" : "4";
        epsilon.step = "any";
        epsilon.value = String(sample.epsilon);
        epsilonNumber.step = "any";
        tau.max = sample.dataset === "3DMatch" ? ".35" : "1.5";
        tau.step = "any";
        tau.value = String(pair.study.evidence.diagnosticTolerance);
        tauNumber.step = "any";
        alignment = 1;
        const alignments = pair.study.sets;
        setSelect.replaceChildren(...alignments.map(set => {
            const option = document.createElement("option");
            option.value = set.id;
            option.textContent = set.label;
            return option;
        }));
        setSelect.value = alignments[0].id;
        query<HTMLElement>("[data-rw-title]").textContent = sample.title;
        query<HTMLElement>("[data-rw-detail]").textContent = `${sample.dataset} · Scans ${sample.sourceScan} / ${sample.targetScan}`;
        matches = pair.proposals.map(point => ({ source: new THREE.Vector3().fromArray(point.source).applyMatrix4(frame), target: new THREE.Vector3().fromArray(point.target).applyMatrix4(frame) }));
        fullProposals = pair.proposals;
        toleranceMesh?.dispose();
        toleranceBalls.clear();
        toleranceMesh = new THREE.InstancedMesh(ballGeometry, ballMaterial, matches.length);
        toleranceBalls.add(toleranceMesh);
        setPointSet();
        updateTolerance();
        await updateGraph();
        resetCamera();
        placeholder.hidden = true;
        root.dataset.error = "false";
        setDisabled(false);
    }
    function reportLoadError(error: unknown) {
        if (disposed)
            return;
        console.error(error);
        placeholder.hidden = false;
        loading.textContent = error instanceof Error ? error.message : "The real scan data could not load.";
        root.dataset.error = "true";
        setDisabled(false);
    }
    sampleSelect.replaceChildren(...samples.map((sample) => {
        const option = document.createElement("option");
        option.value = sample.id;
        option.textContent = sample.title;
        return option;
    }));
    const onSampleChange = () => void loadSample(sampleSelect.value).catch(reportLoadError);
    const onSetChange = () => { setPointSet(); };
    const onEpsilonInput = () => { stopPoseAnimation(); scheduleGraph(); };
    const roundSlider = (input: HTMLInputElement) => { input.value = String(Math.round(input.valueAsNumber * 100) / 100); };
    const onEpsilonSlide = () => { roundSlider(epsilon); onEpsilonInput(); };
    const onTauSlide = () => { roundSlider(tau); updateTolerance(); };
    const setNumber = (number: HTMLInputElement, range: HTMLInputElement, update: () => void) => {
        if (!number.value || !Number.isFinite(number.valueAsNumber))
            return;
        if (number.valueAsNumber < Number(range.min)) {
            number.value = range.value;
            return;
        }
        if (number.valueAsNumber > Number(range.max))
            range.max = String(number.valueAsNumber * 1.2);
        range.value = number.value;
        update();
    };
    const onEpsilonNumber = () => setNumber(epsilonNumber, epsilon, onEpsilonInput);
    const onTauNumber = () => setNumber(tauNumber, tau, updateTolerance);
    const onResetInput = () => { stopPoseAnimation(); frozenPose = undefined; alignment = 0; updatePose(); resetCamera(); };
    const onResetCamera = () => resetCamera();
    const onGraphWheel = (event: WheelEvent) => {
        event.preventDefault();
        const bounds = graph.getBoundingClientRect();
        const x = (event.clientX - bounds.left) / bounds.width, y = (event.clientY - bounds.top) / bounds.height;
        const nextWidth = Math.max(24, Math.min(640, graphViewBox.width * Math.exp(event.deltaY * .0015)));
        const factor = nextWidth / graphViewBox.width;
        graphViewBox.x += x * graphViewBox.width * (1 - factor);
        graphViewBox.y += y * graphViewBox.height * (1 - factor);
        graphViewBox.width = nextWidth;
        graphViewBox.height *= factor;
        graph.setAttribute("viewBox", `${graphViewBox.x} ${graphViewBox.y} ${graphViewBox.width} ${graphViewBox.height}`);
        drawGraphEdges();
    };
    const onGraphToggle = () => {
        const open = graphPanel.hidden;
        graphPanel.hidden = !open;
        root.dataset.graphOpen = String(open);
        graphToggle.setAttribute("aria-pressed", String(open));
        graphToggle.setAttribute("aria-label", `${open ? "Hide" : "Show"} consistency graph`);
        if (open)
            requestAnimationFrame(drawGraphEdges);
    };
    graphToggle.addEventListener("click", onGraphToggle);
    graph.addEventListener("wheel", onGraphWheel, { passive: false });
    sampleSelect.addEventListener("change", onSampleChange);
    setSelect.addEventListener("change", onSetChange);
    tau.addEventListener("input", onTauSlide);
    epsilonNumber.addEventListener("change", onEpsilonNumber);
    tauNumber.addEventListener("change", onTauNumber);
    animateButton.addEventListener("click", animateFit);
    resetInputButton.addEventListener("click", onResetInput);
    epsilon.addEventListener("input", onEpsilonSlide);
    resetButton.addEventListener("click", onResetCamera);
    controls.addEventListener("start", stopPoseAnimation);
    const resizeObserver = new ResizeObserver(() => {
        const bounds = canvas.parentElement!.getBoundingClientRect();
        const width = Math.max(bounds.width, 1), height = Math.max(bounds.height, 1);
        renderer.setSize(width, height, false);
        const oldFit = cameraFitFactor(camera.aspect);
        camera.aspect = width / height;
        if (pair)
            camera.position.sub(controls.target).multiplyScalar(cameraFitFactor(camera.aspect) / oldFit).add(controls.target);
        camera.updateProjectionMatrix();
    });
    resizeObserver.observe(canvas.parentElement!);
    const graphResizeObserver = new ResizeObserver(drawGraphEdges);
    graphResizeObserver.observe(edgeCanvas);
    const visibilityObserver = new IntersectionObserver((entries) => { visible = entries.some((entry) => entry.isIntersecting); });
    visibilityObserver.observe(root);
    const render = () => {
        if (disposed)
            return;
        animationFrame = requestAnimationFrame(render);
        if (!visible || document.hidden)
            return;
        if (poseAnimation && sourceCloud && targetCloud) {
            const progress = Math.min(1, (performance.now() - poseAnimation.start) / 1100);
            const eased = progress * progress * (3 - 2 * progress);
            targetCloud.quaternion.copy(poseAnimation.rotation).slerp(fittedRotation, eased);
            targetCloud.position.copy(poseAnimation.target).lerp(fittedTranslation, eased);
            alignment = eased;
            updateMatches();
            if (progress === 1) {
                poseAnimation = undefined;
                alignment = 1;
                updatePose();
            }
        }
        controls.update();
        updateGrid();
        renderer.render(scene, camera);
    };
    render();
    const dispose = () => {
        if (disposed)
            return;
        disposed = true;
        ++loadVersion;
        ++graphRequest;
        window.clearTimeout(graphDebounce);
        graphWorker.terminate();
        pendingGraphs.forEach(pending => pending.resolve(undefined));
        pendingGraphs.clear();
        cancelAnimationFrame(animationFrame);
        resizeObserver.disconnect();
        graphResizeObserver.disconnect();
        visibilityObserver.disconnect();
        controls.dispose();
        graph.removeEventListener("wheel", onGraphWheel);
        graphToggle.removeEventListener("click", onGraphToggle);
        sampleSelect.removeEventListener("change", onSampleChange);
        epsilon.removeEventListener("input", onEpsilonSlide);
        setSelect.removeEventListener("change", onSetChange);
        tau.removeEventListener("input", onTauSlide);
        epsilonNumber.removeEventListener("change", onEpsilonNumber);
        tauNumber.removeEventListener("change", onTauNumber);
        animateButton.removeEventListener("click", animateFit);
        resetInputButton.removeEventListener("click", onResetInput);
        resetButton.removeEventListener("click", onResetCamera);
        clearClouds();
        [lines, highlightedLines, sourceHandles, targetHandles, highlightedSources, highlightedTargets, endpointHalos].forEach((object) => { object.geometry.dispose(); (object.material as THREE.Material).dispose(); });
        toleranceMesh?.dispose();
        ballGeometry.dispose();
        ballMaterial.dispose();
        axes.geometry.dispose();
        (axes.material as THREE.Material).dispose();
        axisLabels.forEach(sprite => { sprite.material.map?.dispose(); sprite.material.dispose(); });
        discTexture.dispose();
        grid.geometry.dispose();
        const gridMaterial = grid.material;
        if (Array.isArray(gridMaterial))
            gridMaterial.forEach((material) => material.dispose());
        else
            gridMaterial.dispose();
        renderer.dispose();
    };
    try {
        await loadSample(samples[0].id);
    }
    catch (error) {
        dispose();
        throw error;
    }
    return { dispose };
}
