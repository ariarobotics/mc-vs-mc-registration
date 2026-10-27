import { sitePath } from "../lib/paths";
const titleLines = ["On Maximum Clique and Maximum Consensus Formulations", "in Point Cloud Registration"] as const;
export const paper = {
    title: titleLines.join(" "),
    titleLines,
    authors: ["Abolfazl Babanazari", "Kaveh Fathian"],
    affiliation: "Department of Computer Science, Colorado School of Mines",
    summary: `Supplementary material for ${titleLines.join(" ")}.`,
    links: { paper: "https://arxiv.org/abs/2610.27275", proofs: "https://github.com/ariarobotics/mc-vs-mc-registration", video: sitePath("media/maximum-clique-and-maximum-consensus.mp4"), lean: "https://lean-lang.org/" },
    abstract: String.raw `Maximum clique and maximum consensus are widely used formulations for robust point cloud registration in robotics. Maximum consensus seeks one transformation that aligns as many matches as possible, while maximum clique selects matches through pairwise distance tests. Maximum clique is often used as a substitute for or an approximation to maximum consensus, with empirical evidence suggesting a close relationship. However, how closely the two formulations agree is not fully understood. We study this relationship theoretically. We show that a maximum clique can have arbitrarily large alignment error and be arbitrarily larger than the maximum consensus set at any fixed positive tolerance, and derive geometric conditions that bound this error. When rotation is fixed, we derive sharp error bounds and tests that exactly characterize maximum consensus for the translation subproblem. Finally, we study group-$k$ consistency, which tests groups of $k$ matches, and determine the smallest group sizes that guarantee alignment error bounds independent of point cloud scale and geometry. These are $d+1$ for rotations and translations and $d+2$ when reflections are allowed, in dimensions $d\ge2$. Interactive examples and proof verification using the Lean theorem prover are available at \url{https://ariarobotics.github.io/mc-vs-mc-registration/}.`,
};
export const results = [
    {
        title: "Translation", label: "Known rotation",
        pairwiseFactor: String.raw `\sqrt{\frac{2d}{d+1}}`,
        pairwiseExpression: String.raw `\rho^{(t)}(C)\le\sqrt{\frac{2d}{d+1}}\,\rho^{(t)}_2(C)`,
        pairwiseExplanation: "Jung’s bound is sharp for a regular simplex.",
        order: "d+1", factor: "1",
        expression: String.raw `\rho^{(t)}(C)=\rho^{(t)}_{d+1}(C)`,
        explanation: "Consistency is exact at order d + 1.",
    },
    {
        title: "Proper rigid motions", label: "Rotations without reflections",
        pairwiseFactor: null, pairwiseExpression: null,
        pairwiseExplanation: "Pairwise consistency admits no dimension-only alignment-error bound.",
        order: "d+1", factor: "2d+1",
        expression: String.raw `\rho^+(C)\le(2d+1)\,\rho^+_{d+1}(C)`,
        explanation: "Order d + 1 is the first with a dimension-only error bound.",
    },
    {
        title: "Rigid motions", label: "Rotations and reflections",
        pairwiseFactor: null, pairwiseExpression: null,
        pairwiseExplanation: "Both the alignment error at fixed pairwise tolerance and the clique-to-consensus ratio can be arbitrarily large.",
        order: "d+2", factor: String.raw `2\sqrt d`,
        expression: String.raw `\rho(C)\le2\sqrt d\,\rho_{d+2}(C)`,
        explanation: "Order d + 2 is the first with a dimension-only error bound.",
    },
] as const;
