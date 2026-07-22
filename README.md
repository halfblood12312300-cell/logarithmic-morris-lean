# An Unconditional Proof of the Logarithmic Morris Constant-Term Identity

[![Lean proof audit](https://github.com/halfblood12312300-cell/logarithmic-morris-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/halfblood12312300-cell/logarithmic-morris-lean/actions/workflows/lean.yml)

This repository contains a complete Lean 4 formalization of the logarithmic
Morris constant-term identity for

\[
n=2m+1, \qquad K=2k+1, \qquad a,b,k,m\in\mathbb Z_{\ge 0}.
\]

The final theorem is

```lean
LogarithmicMorrisFull.logarithmicMorris_full
  (S : LogarithmicMorrisFull.Setup) :
  LogarithmicMorrisFull.LogarithmicMorrisStatement S
```

The proof is unconditional: it does not assume the complex Morris
constant-term identity. Its Dyson base case is obtained from Good's finite
Dyson identity, a beta-product moment formula, and moment determinacy on a
compact interval.

## Reproduce the build from a fresh clone

The repository pins Lean and Mathlib through `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`.

```bash
git clone https://github.com/halfblood12312300-cell/logarithmic-morris-lean.git
cd logarithmic-morris-lean
lake update
lake exe cache get
lake build logarithmicmorris.LogarithmicMorrisFull
lake env lean --trust=0 logarithmicmorris/LogarithmicMorrisAudit.lean
```

Pinned versions:

- Lean: `v4.28.0`
- Mathlib: `v4.28.0`

The audit command reports only:

```text
[propext, Classical.choice, Quot.sound]
```

In particular, the final theorem does not depend on `sorryAx` or on an
external Morris, Dyson, Selberg, or integral-evaluation axiom.

## Repository scope

The `logarithmicmorris/` and `laurent/` directories contain the exact local
transitive import closure of `LogarithmicMorrisFull.lean`, together with the
kernel audit file. The top-level `logarithmicmorris.lean` is a public entry
point importing the final theorem. No Lean file in this release snapshot
contains a `sorry` declaration. Historical `Scratch...` and `Aristotle...`
filenames are retained so that the verified module graph is not changed merely
for presentation.

Key entry points:

- `logarithmicmorris/LogarithmicMorrisFull.lean`: final theorem;
- `logarithmicmorris/LogarithmicMorrisAudit.lean`: kernel axiom report;
- `logarithmicmorris/LogarithmicMorrisParameterReduction.lean`: endpoint
  recurrence and reduction;
- `logarithmicmorris/LogarithmicMorrisDysonMomentEvaluation.lean`:
  unconditional Dyson base-case evaluation.

The accompanying English manuscript is stored in `paper/`.

## Continuous verification

The GitHub Actions workflow builds the final target, runs an independent
`nanoda` check with `sorryAx` disallowed, and prints the final theorem's axiom
closure under `--trust=0`.

## Author

Yongcheng Hu  
Central South University  
<252111040@csu.edu.cn>
