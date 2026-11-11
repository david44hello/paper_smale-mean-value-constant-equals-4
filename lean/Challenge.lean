/-
Challenge.lean — the statement of Theorem 1.1 of the paper "Smale's mean value constant (1981) equals 4", for the
Palomar registry: the definitions it needs and the three Lean forms of the theorem, each proof left open.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import Mathlib

@[expose] public section

/-!
# Smale's mean value constant equals 4: the statement

Let `p` be a complex polynomial of degree `d ≥ 2` with `p(0) = 0` and `p'(0) ≠ 0`. Let `S(p)` be the least value of
`|p(c)/(c p'(0))|` over the critical points `c` of `p` (the zeros of `p'`). Let `K(d)` be the supremum of `S(p)` over
all such `p` of degree `d`, and let `K* = sup_{d ≥ 2} K(d)`, Smale's mean value constant. Smale proved `K* ≤ 4` in 1981
and asked whether `4` can be replaced by `1`. Theorem 1.1 of the paper: `K* = lim_{d → ∞} K(d) = 4`.

This file states it in two normalizations, with the definitions written out:
* `Smale.IsPd`, `Smale.critRatios`, `Smale.mval`, `Smale.Kd`, `Smale.Kstar`: the class `𝓟_d` with `p'(0) = 1`, where
  the ratio is `|p(β)|/|β|` (these definitions are those of [G, Definition 2.1]);
* `Smale.P030.Rows.IsPdGen`, `critRatiosGen`, `Sval`, `KdGen`, `KstarGen`: the paper's own class, `p'(0) ≠ 0`, and the
  paper's `S(p)` (Section 1 of the paper).

The suprema are taken in `EReal`, the extended real numbers, where every supremum exists; `K(d) ≤ 4` is part of what
is proved, not assumed. The three theorems below are `Smale.P030.Rows.thm_1_1` (Theorem 1.1 in the paper's own
normalization), `Smale.P030.kstar_eq_four` and `Smale.P030.tendsto_Kd_four` (the same facts for `p'(0) = 1`).

Every definition below is copied word for word from the project's definition files `Smale/Defs/Basic.lean` and
`Smale/P030/Rows/DefsGen.lean`; `lake comparator` checks that the definitions here and there are the same.

[G] D. Goel, Smale's mean value constant exceeds 1.1559, and other miscellanea, Zenodo, 2026, version 6.08,
https://doi.org/10.5281/zenodo.23729510.
[Smale1981] S. Smale, The fundamental theorem of algebra and complexity theory, Bull. Amer. Math. Soc. (N.S.) 4 (1981),
1–36.
-/

namespace Smale

open Polynomial Complex Metric ComplexConjugate

/-- `p ∈ 𝓟_d` ([G, Definition 2.1]): a complex polynomial of degree `d` with `p(0) = 0` and `p'(0) = 1`. -/
def IsPd (d : ℕ) (p : ℂ[X]) : Prop :=
  p.natDegree = d ∧ p.eval 0 = 0 ∧ p.derivative.eval 0 = 1

/-- The numbers `|p(β)|/|β|` over the critical points `β` of `p` ([G, Definition 2.1]). -/
def critRatios (p : ℂ[X]) : Set ℝ :=
  {r | ∃ β : ℂ, p.derivative.eval β = 0 ∧ r = ‖p.eval β‖ / ‖β‖}

/-- `m(p) = min_{p'(β) = 0} |p(β)|/|β|` ([G, Definition 2.1]). For `p ∈ 𝓟_d` with `d ≥ 2` the set `critRatios p` is finite and
nonempty, so this infimum is attained (`sec1_m_attained_proved` in `Smale/Proofs/Lemma53.lean`). -/
noncomputable def mval (p : ℂ[X]) : ℝ := sInf (critRatios p)

/-- `K(d) = sup_{p ∈ 𝓟_d} m(p)` ([G, Definition 2.1]). Taken in `EReal`, where every supremum exists (that `K(d) ≤ 4` is Smale's
theorem [Smale1981], background the proof does not use). -/
noncomputable def Kd (d : ℕ) : EReal := ⨆ p : {p : ℂ[X] // IsPd d p}, ((mval p.1 : ℝ) : EReal)

/-- Smale's mean value constant `K* = sup_{d ≥ 2} K(d)` ([G, Definition 2.1]). -/
noncomputable def Kstar : EReal := ⨆ d : {d : ℕ // 2 ≤ d}, Kd d.1

end Smale

namespace Smale.P030.Rows

open Polynomial

/-- The paper's class (Section 1, first sentence): `p` of degree `d` with `p(0) = 0` and `p'(0) ≠ 0`. -/
def IsPdGen (d : ℕ) (p : ℂ[X]) : Prop :=
  p.natDegree = d ∧ p.eval 0 = 0 ∧ p.derivative.eval 0 ≠ 0

/-- The numbers `|p(c)/(c p'(0))|` over the critical points `c` of `p` (Section 1, the definition of `S(p)`). -/
def critRatiosGen (p : ℂ[X]) : Set ℝ :=
  {r | ∃ c : ℂ, p.derivative.eval c = 0 ∧ r = ‖p.eval c / (c * p.derivative.eval 0)‖}

/-- `S(p)`, the least of those numbers (Section 1, the definition of `S(p)`). -/
noncomputable def Sval (p : ℂ[X]) : ℝ := sInf (critRatiosGen p)

/-- `K(d) = sup S(p)` over the paper's class (Section 1, the definition of `K(d)`). -/
noncomputable def KdGen (d : ℕ) : EReal := ⨆ p : {p : ℂ[X] // IsPdGen d p}, ((Sval p.1 : ℝ) : EReal)

/-- `K* = sup_{d ≥ 2} K(d)` in the paper's normalization (Section 1, the definition of `K*`). -/
noncomputable def KstarGen : EReal := ⨆ d : {d : ℕ // 2 ≤ d}, KdGen d.1

end Smale.P030.Rows

namespace Smale.P030.Rows

open Polynomial Filter Topology

/-- **Theorem 1.1** of the paper, in its own normalization (`p'(0) ≠ 0`): `K(d)` tends to `4` as `d` tends to
infinity, and `K* = sup_{d ≥ 2} K(d) = 4`. -/
theorem thm_1_1 : Tendsto KdGen atTop (𝓝 ((4 : ℝ) : EReal)) ∧ KstarGen = ((4 : ℝ) : EReal) := by
  sorry

end Smale.P030.Rows

namespace Smale.P030

open Polynomial Complex Metric Set Filter Topology

/-- `K* = 4` for the class `𝓟_d` (`p'(0) = 1`). -/
theorem kstar_eq_four : Kstar = ((4 : ℝ) : EReal) := by
  sorry

/-- `K(d)` tends to `4` as `d` tends to infinity, for the class `𝓟_d` (`p'(0) = 1`). -/
theorem tendsto_Kd_four : Filter.Tendsto Smale.Kd Filter.atTop (nhds ((4 : ℝ) : EReal)) := by
  sorry

end Smale.P030
