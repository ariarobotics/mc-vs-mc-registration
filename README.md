<h1 align="center">
  On Maximum Clique and Maximum Consensus Formulations<br>
  in Point Cloud Registration
</h1>

Supplementary website, interactive examples, and Lean proofs.

## Website

Requires Node.js 22.12+ and pnpm 10.19.0.
```sh
cd website
pnpm install --frozen-lockfile
pnpm dev
```

Open http://localhost:4321.


## Lean proofs

With Lean installed through [elan](https://github.com/leanprover/elan), run:
```sh
cd lean
lake exe cache get
lake build
```
