# Smale's mean value constant equals 4: a Lean 4 proof

## What is proved

For a complex polynomial p of degree d with p(0) = 0 and p'(0) = 1, let m(p) be the least value of |p(b)|/|b| over the critical points b of p (the zeros of p'). Let K(d) be the supremum of m(p) over all such p of degree d, and let K* be the supremum of K(d) over all d >= 2. K* is Smale's mean value constant.

Two theorems, both in `Smale/P030/Contract.lean`:

1. `Smale.P030.kstar_eq_four`: the constant K* equals 4.

   ```lean
   theorem kstar_eq_four : Kstar = ((4 : ℝ) : EReal)
   ```

2. `Smale.P030.tendsto_Kd_four`: K(d) tends to 4 as d tends to infinity.

   ```lean
   theorem tendsto_Kd_four : Filter.Tendsto Smale.Kd Filter.atTop (nhds ((4 : ℝ) : EReal))
   ```

The definitions `Smale.Kd` and `Smale.Kstar` are in `Smale/Defs/Basic.lean`. They are taken in `EReal`, the extended real numbers, where every supremum exists.

## Taken as given

Nothing beyond Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The proof has no `sorry` and adds no axiom. The upper bound K* <= 4 (Smale's theorem) is proved here too, not assumed.

## How to check

You need `elan`. The toolchain is fixed in `lean-toolchain` (Lean v4.35.0), and Mathlib is fixed at v4.35.0 in `lake-manifest.json`.

```
git clone https://github.com/david44hello/paper_smale-mean-value-constant-equals-4
cd paper_smale-mean-value-constant-equals-4/lean
lake exe cache get
lake build
```

Then, in a file that imports `Smale`, run:

```lean
#print axioms Smale.P030.kstar_eq_four
#print axioms Smale.P030.tendsto_Kd_four
```

Each must print `[propext, Classical.choice, Quot.sound]`.

## Status

This repository is private for now. The other statements of the paper are not yet in Lean. The proof has had one independent check, by an AI.
