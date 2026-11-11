/-
Smale/P030/Rows/DefsGen.lean — the definitions of `K(d)` and `K*` in the paper's own normalization: a polynomial `p` of
degree `d` with `p(0) = 0` and `p'(0) ≠ 0`, and the ratio `|p(c)/(c p'(0))|` at its critical points `c`. All of them
are in Section 1 of the paper "Smale's mean value constant (1981) equals 4".
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import Smale.Defs.Basic

@[expose] public section

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
