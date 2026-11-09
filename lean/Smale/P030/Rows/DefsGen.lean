/-
Smale/P030/Rows/DefsGen.lean — the definitions of `K(d)` and `K*` in the paper's own normalization: a polynomial `p` of
degree `d` with `p(0) = 0` and `p'(0) ≠ 0`, and the ratio `|p(c)/(c p'(0))|` at its critical points `c`. Line numbers are
those of the TeX source of the paper "Smale's mean value constant equals 4", version 0.90.
-/
import Smale.Defs.Basic

namespace Smale.P030.Rows

open Polynomial

/-- The paper's class (l.37, l.41-43): `p` of degree `d` with `p(0) = 0` and `p'(0) ≠ 0`. -/
def IsPdGen (d : ℕ) (p : ℂ[X]) : Prop :=
  p.natDegree = d ∧ p.eval 0 = 0 ∧ p.derivative.eval 0 ≠ 0

/-- The numbers `|p(c)/(c p'(0))|` over the critical points `c` of `p` (l.39). -/
def critRatiosGen (p : ℂ[X]) : Set ℝ :=
  {r | ∃ c : ℂ, p.derivative.eval c = 0 ∧ r = ‖p.eval c / (c * p.derivative.eval 0)‖}

/-- `S(p)`, the least of those numbers (l.39). -/
noncomputable def Sval (p : ℂ[X]) : ℝ := sInf (critRatiosGen p)

/-- `K(d) = sup S(p)` over the paper's class (l.43). -/
noncomputable def KdGen (d : ℕ) : EReal := ⨆ p : {p : ℂ[X] // IsPdGen d p}, ((Sval p.1 : ℝ) : EReal)

/-- `K* = sup_{d ≥ 2} K(d)` in the paper's normalization (l.43). -/
noncomputable def KstarGen : EReal := ⨆ d : {d : ℕ // 2 ≤ d}, KdGen d.1

end Smale.P030.Rows
