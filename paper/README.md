# Paper and formal proof package

This directory contains the manuscript for the exact determination

```text
L_2(12,4) = 6
```

in the ordinary ordered binary deletion model.

## Build the paper

From this directory:

```bash
tectonic main.tex
```

The generated paper is `main.pdf`.

## Verify the mathematical artifacts

From the `formalization` directory:

```bash
python3 research/deletion_code_attempt/verify_code.py
python3 research/deletion_code_attempt/proof/verify_upper_certificate.py
python3 research/deletion_code_attempt/proof/test_upper_certificate_mutations.py
```

## Complete Lean source inventory

The formalization uses these repository files:

- `DeletionCodes/Conjectures/DeletionCode124.lean`: model, finite checks,
  weighted-packing proof, and main theorem.
- `DeletionCodes/Conjectures/DeletionCode124Data.lean`: transparent generated
  certificate weights, clique cuts, and lower code.
- `DeletionCodes/Basic.lean`: the Mathlib import.
- `DeletionCodes.lean`: root module importing the formal theorem.
- `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`: reproducible Lean
  and Mathlib environment.

Build only the formal theorem, then the whole repository:

```bash
lake build DeletionCodes.Conjectures.DeletionCode124
lake build
```

The current theorem uses four `native_decide` leaves for the finite data
checks. The generic weighted-sum implication is proved in Lean, but the leaf
checks inherit Lean's native compiler/runtime trust boundary. The repository
does not claim that this version passes SafeVerify or is a kernel-only proof.

The transparent data module is regenerated from the checked JSON certificate
with:

```bash
python3 research/deletion_code_attempt/proof/export_lean_certificate.py \
  research/deletion_code_attempt/proof/upper_certificate.json \
  DeletionCodes/Conjectures/DeletionCode124Data.lean
```

## Claim boundary

Kolev's published 2016 table already records the lower bound 6 and the upper
bound 10. A 2008 variable-length insertion/deletion table lists `D_2(12,10) = 7`,
which implies `L_2(12,4) <= 7`. The contribution claimed here is the exact upper
bound 6. The literature search found no earlier exact
determination, but search absence is not an unconditional proof of priority.
