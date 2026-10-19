# Lean Proofs

Proofs of *On Maximum Clique and Maximum Consensus Formulations in Point Cloud Registration*.

## Build and check

With Lean installed, run from this directory:

```sh
lake exe cache get
lake build
```

This builds the project and checks the proofs. To use them in Lean:

```lean
import CliqueCertificate
```

## Organization

```text
CliqueCertificate/
  Definitions.lean    Shared definitions
  Basic.lean          Shared lemmas
  External/           Supporting mathematics (Jung's theorem, Helly's theorem, etc.)
  TranslationOnly/    Translation-only results
  HigherOrder/        Rigid motions allowing reflections
  ProperMotion/       Proper rigid motions
```
