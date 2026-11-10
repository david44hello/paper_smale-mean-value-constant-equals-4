/-
Smale/P030/Rows/Thm11.lean — Theorem 1.1 of the paper in the paper's own normalization (`p'(0) ≠ 0`, the definitions of
`Smale/P030/Rows/DefsGen.lean`). `S(p)` is unchanged when `p` is multiplied by a nonzero constant (the definition of
`S(p)`); proved here, not cited. So dividing `p` by `p'(0)` turns the paper's class into the class `𝓟_d` of
`Smale/Defs/Basic.lean` (`p'(0) = 1`, ratio `|p(c)|/|c|`), so `K(d)` and `K*` are the same in both normalizations,
and Theorem 1.1 follows from `kstar_eq_four` and `tendsto_Kd_four`.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Smale.P030.Contract
import Smale.P030.Rows.DefsGen

namespace Smale.P030.Rows

open Polynomial Filter Topology

/-- The ratios of `p` in the paper's normalization are the ratios of `p / p'(0)` in the class `𝓟_d`. -/
theorem critRatiosGen_eq (p : ℂ[X]) {a : ℂ} (ha : p.derivative.eval 0 = a) (ha0 : a ≠ 0) :
    critRatiosGen p = critRatios (C a⁻¹ * p) := by
  ext r
  simp only [critRatiosGen, critRatios, Set.mem_ofPred_eq, derivative_mul, derivative_C, zero_mul, zero_add,
    eval_mul, eval_C, ha]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c, by rw [hc, mul_zero], ?_⟩
    simp only [norm_div, norm_mul, norm_inv]
    ring
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c, ?_, ?_⟩
    · exact (mul_eq_zero.mp hc).resolve_left (inv_ne_zero ha0)
    · simp only [norm_div, norm_mul, norm_inv]
      ring

/-- `p / p'(0)` lies in `𝓟_d` when `p` lies in the paper's class. -/
theorem IsPdGen.toIsPd {d : ℕ} {p : ℂ[X]} (h : IsPdGen d p) : IsPd d (C (p.derivative.eval 0)⁻¹ * p) := by
  obtain ⟨hdeg, h0, h1⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [natDegree_C_mul (inv_ne_zero h1), hdeg]
  · simp [h0]
  · simp only [derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C]
    exact inv_mul_cancel₀ h1

/-- `𝓟_d` lies in the paper's class. -/
theorem IsPd.toIsPdGen {d : ℕ} {p : ℂ[X]} (h : IsPd d p) : IsPdGen d p :=
  ⟨h.1, h.2.1, by rw [h.2.2]; exact one_ne_zero⟩

/-- For `p'(0) = 1` the two ratios agree, so `S(p) = m(p)`. -/
theorem Sval_eq_mval {p : ℂ[X]} (h1 : p.derivative.eval 0 = 1) : Sval p = mval p := by
  have h := critRatiosGen_eq p h1 one_ne_zero
  rw [inv_one, map_one, one_mul] at h
  unfold Sval mval
  rw [h]

/-- `S(p) = m(p / p'(0))`. -/
theorem Sval_eq_mval_div {p : ℂ[X]} (h1 : p.derivative.eval 0 ≠ 0) :
    Sval p = mval (C (p.derivative.eval 0)⁻¹ * p) := by
  unfold Sval mval
  rw [critRatiosGen_eq p rfl h1]

/-- `S(p)` is unchanged when `p` is multiplied by a nonzero constant (the definition of `S(p)`); proved here, not
cited. Hence `K(d)` is the same for `p'(0) ≠ 0` and for `p'(0) = 1`. It lets the rows use the paper's normalization
while the proved `kstar_eq_four` uses `p'(0) = 1`. -/
theorem KdGen_eq_Kd (d : ℕ) : KdGen d = Kd d := by
  apply le_antisymm
  · refine iSup_le fun p => ?_
    rw [Sval_eq_mval_div p.2.2.2]
    exact le_iSup (fun q : {q : ℂ[X] // IsPd d q} => ((mval q.1 : ℝ) : EReal)) ⟨_, IsPdGen.toIsPd p.2⟩
  · refine iSup_le fun p => ?_
    rw [← Sval_eq_mval p.2.2.2]
    exact le_iSup (fun q : {q : ℂ[X] // IsPdGen d q} => ((Sval q.1 : ℝ) : EReal)) ⟨p.1, IsPd.toIsPdGen p.2⟩

/-- `K*` is the same in both normalizations. -/
theorem KstarGen_eq_Kstar : KstarGen = Kstar := by
  unfold KstarGen Kstar
  simp only [KdGen_eq_Kd]

/-- **Theorem 1.1**: `K* = lim_{d → ∞} K(d) = 4`, where `K* = sup_{d ≥ 2} K(d)`. -/
theorem thm_1_1 : Tendsto KdGen atTop (𝓝 ((4 : ℝ) : EReal)) ∧ KstarGen = ((4 : ℝ) : EReal) := by
  have hfun : KdGen = Kd := funext KdGen_eq_Kd
  exact ⟨hfun ▸ tendsto_Kd_four, KstarGen_eq_Kstar ▸ kstar_eq_four⟩

end Smale.P030.Rows
