export interface RealSample {
    id: string;
    dataset: string;
    title: string;
    sourceScan: number;
    targetScan: number;
    epsilon: number;
    voxelSize: number;
    groundNormal?: [
        number,
        number,
        number
    ];
}
export interface Scan {
    count: number;
    points: Float32Array;
}
export interface PointProposal {
    id: number;
    source: number[];
    target: number[];
}
export interface StudySet {
    id: string;
    label: string;
    indices: number[];
    pose: number[];
}
interface StudyEvidence { diagnosticTolerance: number; }
export interface StudyGraph {
    searchStatus: "heuristic" | "optimal" | "bounded";
    epsilon: number;
    edgeCount: number;
    cliqueSize: number;
}
export interface StudyData {
    proposals: PointProposal[];
    sets: StudySet[];
    evidence: StudyEvidence;
    fullClique: number[];
    graph: StudyGraph;
}
export interface RealPair {
    source: Scan;
    target: Scan;
    proposals: PointProposal[];
    study: StudyData;
}
export function knownStudyGraphMaximum(study: StudyData, epsilon: number): number | undefined {
    const graph = study.graph;
    return graph.searchStatus === "optimal" && graph.epsilon === epsilon
        && study.fullClique.length === graph.cliqueSize ? graph.cliqueSize : undefined;
}
function validateStudyData(study: StudyData): void {
    const indicesValid = (indices: number[]) => Array.isArray(indices) && indices.length > 0
        && new Set(indices).size === indices.length
        && indices.every(index => Number.isInteger(index) && index >= 0 && index < study.proposals.length);
    const pointValid = (point: number[]) => Array.isArray(point) && point.length === 3 && point.every(Number.isFinite);
    const graph = study.graph;
    if (!Array.isArray(study.proposals) || !study.proposals.length || !Array.isArray(study.sets) || !study.sets.length
        || study.proposals.some(match => !pointValid(match.source) || !pointValid(match.target))
        || study.sets.some(set => !indicesValid(set.indices) || !Array.isArray(set.pose) || set.pose.length !== 16 || !set.pose.every(Number.isFinite))
        || !indicesValid(study.fullClique) || !graph || !["heuristic", "optimal", "bounded"].includes(graph.searchStatus)
        || !Number.isFinite(graph.epsilon) || graph.epsilon < 0
        || !Number.isInteger(graph.edgeCount) || graph.edgeCount < 0 || graph.edgeCount > study.proposals.length * (study.proposals.length - 1) / 2
        || !Number.isInteger(graph.cliqueSize) || graph.cliqueSize < 1 || graph.cliqueSize > study.proposals.length
        || !study.evidence || !Number.isFinite(study.evidence.diagnosticTolerance) || study.evidence.diagnosticTolerance < 0) {
        throw new Error("The study point data is invalid.");
    }
}
export function decodeRealScan(buffer: ArrayBuffer): Scan {
    if (buffer.byteLength < 8)
        throw new Error("The scan data is incomplete.");
    const header = new DataView(buffer);
    const count = header.getUint32(4, true);
    if (header.getUint32(0, true) === 0x32534350 && buffer.byteLength === 8 + count * 12) {
        return { count, points: new Float32Array(buffer, 8, count * 3) };
    }
    throw new Error("The point scan data is invalid.");
}
async function fetchBuffer(url: URL): Promise<ArrayBuffer> {
    const response = await fetch(url);
    if (!response.ok)
        throw new Error("The real scan data could not load. Try again.");
    return response.arrayBuffer();
}
export async function loadRealPair(sample: RealSample, manifestUrl: URL): Promise<RealPair> {
    const root = new URL(`${sample.id}/`, manifestUrl);
    const [sourceBuffer, targetBuffer, response] = await Promise.all([
        fetchBuffer(new URL("source.bin", root)), fetchBuffer(new URL("target.bin", root)),
        fetch(new URL("study.json", root)),
    ]);
    if (!response.ok)
        throw new Error("The point data could not load.");
    const study = await response.json() as StudyData;
    validateStudyData(study);
    return { source: decodeRealScan(sourceBuffer), target: decodeRealScan(targetBuffer), proposals: study.proposals, study };
}
