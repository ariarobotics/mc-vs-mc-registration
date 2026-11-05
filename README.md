<h2 align="center">
  On Maximum Clique and Maximum Consensus Formulations<br>
  in Point Cloud Registration
</h2>

<p align="center">
  Abolfazl Babanazari and Kaveh Fathian<br>
  Department of Computer Science, Colorado School of Mines
</p>

This repository contains the supplementary material for [**On Maximum Clique and Maximum Consensus Formulations in Point Cloud Registration**](https://arxiv.org/abs/2610.27275): interactive examples, a video, and formal proofs in Lean.

[**Paper (arXiv)**](https://arxiv.org/abs/2610.27275) · [**Project website**](https://ariarobotics.github.io/mc-vs-mc-registration/) · [**Video**](https://ariarobotics.github.io/mc-vs-mc-registration/media/maximum-clique-and-maximum-consensus.mp4) · [**Lean proofs**](lean/)

## Overview

Robust point cloud registration seeks a transformation between two point clouds despite incorrect candidate correspondences. Maximum consensus finds the largest set of matches that a single transformation can align within a given tolerance. Maximum clique instead selects the largest set whose matches pass pairwise distance checks. The paper studies when these formulations agree and how far they can differ.

The main results establish that:

- **Pairwise consistency can be insufficient.** A maximum clique can have unbounded alignment error and an unbounded size ratio relative to maximum consensus at a fixed positive tolerance. Geometric assumptions can provide error bounds.
- **Fixing the rotation gives stronger guarantees.** The translation subproblem admits tight error bounds and local consistency tests that characterize maximum consensus exactly.
- **Larger groups provide global guarantees.** For dimensions $d \ge 2$, the smallest group sizes yielding alignment error bounds independent of cloud scale and geometry are $d+1$ for rotations and translations, and $d+2$ when reflections are allowed.

## Lean proofs

To build the Lean project and check the proofs, install Lean through [elan](https://github.com/leanprover/elan), then run from the repository root:

```sh
cd lean
lake exe cache get
lake build
```

The project pins its Lean version in [`lean/lean-toolchain`](lean/lean-toolchain). See the [Lean README](lean/README.md) for the proof organization and how to import the library.

## Citation

If you use this work, please cite the paper:

```bibtex
@misc{cliqueConsensus2026,
  title         = {On Maximum Clique and Maximum Consensus Formulations in Point Cloud Registration},
  author        = {Abolfazl Babanazari and Kaveh Fathian},
  year          = {2026},
  eprint        = {2610.27275},
  archivePrefix = {arXiv},
  primaryClass  = {cs.RO},
  url           = {https://arxiv.org/abs/2610.27275}
}
```

## License

This repository is licensed under the [PolyForm Noncommercial License 1.0.0](LICENSE).
