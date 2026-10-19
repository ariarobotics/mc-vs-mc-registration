import { buildPairwiseDiscrepancies, thresholdGraph, boundedMaximumClique, graphHasEdge } from "./full-registration";
import type { PointMatch } from "./point-registration";
let cache: ReturnType<typeof buildPairwiseDiscrepancies> | undefined;
self.addEventListener("message", (event: MessageEvent<{
    request: number;
    matches?: PointMatch[];
    epsilon: number;
    seed: number[];
    knownMaximum?: number;
}>) => {
    const { request, matches, epsilon, seed, knownMaximum } = event.data;
    try {
        if (matches)
            cache = buildPairwiseDiscrepancies(matches);
        if (!cache)
            throw new Error("The correspondence graph has no points.");
        const graph = thresholdGraph(cache, epsilon);
        const validSeed: number[] = [];
        seed.forEach(vertex => {
            if (vertex >= 0 && vertex < graph.count && !validSeed.includes(vertex) && validSeed.every(other => graphHasEdge(graph, vertex, other)))
                validSeed.push(vertex);
        });
        const result = boundedMaximumClique(graph, { seed: validSeed, knownMaximum, timeBudgetMs: 35, maxNodes: 100000 });
        const words = Math.ceil(graph.count / 32);
        const adjacency = new Uint32Array(graph.count * words);
        graph.adjacency.forEach((row, i) => adjacency.set(row, i * words));
        self.postMessage({ request, count: graph.count, edgeCount: graph.edgeCount, edges: graph.edges, adjacency, clique: result }, { transfer: [graph.edges.buffer, adjacency.buffer] });
    }
    catch (error) {
        self.postMessage({ request, error: error instanceof Error ? error.message : "The graph could not be computed." });
    }
});
