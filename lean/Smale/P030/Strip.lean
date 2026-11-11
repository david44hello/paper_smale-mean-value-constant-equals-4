/-
Smale/P030/Strip.lean — the explicit map `stripY` of the unit disk into the half strip `{Re y < a, |Im y| < C}`, with its left
inverse `stripT`: elementary functions only, no Riemann map and no boundary theory.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import Smale.P030.Defs

@[expose] public section

namespace Smale.P030

open Complex Metric Set Filter Topology

theorem stripBeta_pos {C : ℝ} (hC : 0 < C) : 0 < stripBeta C := div_pos Real.pi_pos (by positivity)

theorem stripBeta_mul {C : ℝ} (hC : 0 < C) : stripBeta C * C = Real.pi / 2 := by
  rw [stripBeta]
  field_simp

theorem strip_s_pos {a C : ℝ} (ha : 0 < a) (hC : 0 < C) : 0 < Real.sinh (stripBeta C * a) :=
  Real.sinh_pos_iff.2 (mul_pos (stripBeta_pos hC) ha)

/-! ### The disk to the left half plane -/

theorem one_add_ne_zero_of_mem {u : ℂ} (hu : u ∈ disk) : 1 + u ≠ 0 := by
  intro h
  have h1 : u = -1 := by linear_combination h
  have h2 : ‖u‖ < 1 := by simpa using hu
  rw [h1, norm_neg, norm_one] at h2
  exact lt_irrefl _ h2

theorem stripW_re_neg {a C : ℝ} (ha : 0 < a) (hC : 0 < C) {u : ℂ} (hu : u ∈ disk) : (stripW a C u).re < 0 := by
  have hne := one_add_ne_zero_of_mem hu
  have hN : 0 < normSq (1 + u) := normSq_pos.2 hne
  have hu2 : u.re * u.re + u.im * u.im < 1 := by
    have h1 : ‖u‖ < 1 := by simpa using hu
    have h2 : ‖u‖ ^ 2 < 1 := by nlinarith [norm_nonneg u]
    rwa [Complex.sq_norm, normSq_apply] at h2
  have hs := strip_s_pos ha hC
  have heq : (stripW a C u).re = -Real.sinh (stripBeta C * a) * ((1 - u.re * u.re - u.im * u.im) / normSq (1 + u)) := by
    rw [stripW, mul_div_assoc, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_re]
    simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.sub_im, Complex.one_im, Complex.add_im]
    field_simp
    ring
  rw [heq]
  exact mul_neg_of_neg_of_pos (by linarith) (div_pos (by linarith) hN)

/-! ### The square root in the first quadrant -/

/-- `m = (w - i)/(w + i)` lies in the upper half plane for `Re w < 0`. -/
theorem stripM_im_pos {w : ℂ} (hw : w.re < 0) : 0 < ((w - I) / (w + I)).im := by
  have hne : w + I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hN : 0 < normSq (w + I) := normSq_pos.2 hne
  have heq : ((w - I) / (w + I)).im = -2 * w.re / normSq (w + I) := by
    rw [Complex.div_im]
    simp only [Complex.sub_re, Complex.I_re, Complex.add_re, Complex.sub_im, Complex.I_im, Complex.add_im, sub_zero,
      add_zero]
    field_simp
    ring
  rw [heq]
  exact div_pos (by linarith) hN

theorem stripW_add_I_ne {w : ℂ} (hw : w.re < 0) : w + I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

/-- The principal square root of a point of the upper half plane lies in the first quadrant. -/
theorem sqrt_first_quadrant {m : ℂ} (hm : 0 < m.im) :
    (m ^ (1 / 2 : ℂ)) ^ 2 = m ∧ 0 < (m ^ (1 / 2 : ℂ)).re ∧ 0 < (m ^ (1 / 2 : ℂ)).im := by
  have hne : m ≠ 0 := by
    intro h
    rw [h] at hm
    simp at hm
  have harg0 : 0 < arg m := by
    refine lt_of_le_of_ne (Complex.arg_nonneg_iff.2 hm.le) fun h => ?_
    have := (Complex.arg_eq_zero_iff.1 h.symm).2
    linarith
  have hargπ : arg m < Real.pi := by
    refine lt_of_le_of_ne (Complex.arg_le_pi m) fun h => ?_
    have := (Complex.arg_eq_pi_iff.1 h).2
    linarith
  have hform : m ^ (1 / 2 : ℂ) = Complex.exp (Complex.log m / 2) := by
    rw [Complex.cpow_def_of_ne_zero hne]
    ring_nf
  have him : (Complex.log m / 2).im = arg m / 2 := by
    have h1 : Complex.log m / 2 = Complex.log m / ((2 : ℝ) : ℂ) := by norm_num
    rw [h1, Complex.div_ofReal_im, Complex.log_im]
  have hsq : (m ^ (1 / 2 : ℂ)) ^ 2 = m := by
    rw [hform, ← Complex.exp_nat_mul]
    push_cast
    rw [mul_div_cancel₀ _ (two_ne_zero : (2 : ℂ) ≠ 0), Complex.exp_log hne]
  refine ⟨hsq, ?_, ?_⟩
  · rw [hform, Complex.exp_re, him]
    refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩) <;> linarith
  · rw [hform, Complex.exp_im, him]
    refine mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi ?_ ?_) <;> linarith

/-! ### `z` -/

/-- With `p` in the first quadrant, `z = -i (p - 1)/(p + 1)` lies in the right half of the unit disk. -/
theorem stripZ_props {p : ℂ} (h1 : 0 < p.re) (h2 : 0 < p.im) :
    p + 1 ≠ 0 ∧ p - 1 ≠ 0 ∧ 0 < (-I * ((p - 1) / (p + 1))).re ∧ ‖-I * ((p - 1) / (p + 1))‖ < 1 := by
  have hp1 : p + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hp2 : p - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hN : 0 < normSq (p + 1) := normSq_pos.2 hp1
  refine ⟨hp1, hp2, ?_, ?_⟩
  · have heq : (-I * ((p - 1) / (p + 1))).re = 2 * p.im / normSq (p + 1) := by
      have h3 : (-I * ((p - 1) / (p + 1))).re = ((p - 1) / (p + 1)).im := by simp
      rw [h3, Complex.div_im]
      simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.sub_im, Complex.one_im, Complex.add_im, sub_zero,
        add_zero]
      field_simp
      ring
    rw [heq]
    exact div_pos (by linarith) hN
  · rw [norm_mul, norm_neg, norm_I, one_mul, norm_div, div_lt_one (norm_pos_iff.2 hp1)]
    refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
    rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.sub_im, Complex.one_im, Complex.add_im, sub_zero,
      add_zero]
    nlinarith

/-- `z - 1/z = 2w`. -/
theorem stripZ_sub_inv {w p : ℂ} (hw : w + I ≠ 0) (hp : p ^ 2 = (w - I) / (w + I)) (hp1 : p + 1 ≠ 0) (hp2 : p - 1 ≠ 0) :
    -I * ((p - 1) / (p + 1)) - (-I * ((p - 1) / (p + 1)))⁻¹ = 2 * w := by
  have hh : p ^ 2 * (w + I) = w - I := by rw [hp]; field_simp
  have hinv : (-I * ((p - 1) / (p + 1)))⁻¹ = I * ((p + 1) / (p - 1)) := by
    rw [mul_inv, inv_div, neg_eq_neg_one_mul, mul_inv, Complex.inv_I]
    norm_num
  rw [hinv]
  have h1 : -I * ((p - 1) / (p + 1)) - I * ((p + 1) / (p - 1)) =
      -I * ((p - 1) ^ 2 + (p + 1) ^ 2) / ((p + 1) * (p - 1)) := by
    field_simp
    ring
  rw [h1, div_eq_iff (mul_ne_zero hp1 hp2)]
  linear_combination (-2 : ℂ) * hh

/-- The point `z` of `u`, and everything known of it. -/
theorem stripZ_of_mem {a C : ℝ} (ha : 0 < a) (hC : 0 < C) {u : ℂ} (hu : u ∈ disk) :
    0 < (stripZ (stripW a C u)).re ∧ ‖stripZ (stripW a C u)‖ < 1 ∧
      stripZ (stripW a C u) - (stripZ (stripW a C u))⁻¹ = 2 * stripW a C u := by
  set w := stripW a C u with hw
  have hre := stripW_re_neg ha hC hu
  rw [← hw] at hre
  obtain ⟨hsq, hp1, hp2⟩ := sqrt_first_quadrant (stripM_im_pos hre)
  obtain ⟨h1, h2, h3, h4⟩ := stripZ_props hp1 hp2
  exact ⟨h3, h4, stripZ_sub_inv (stripW_add_I_ne hre) hsq h1 h2⟩

/-! ### The half strip -/

theorem stripZ_ne_zero {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := by
  rintro rfl
  simp at hz

theorem stripZ_slit {z : ℂ} (hz : 0 < z.re) : z ∈ slitPlane := Or.inl hz

theorem stripY_mem {a C : ℝ} (ha : 0 < a) (hC : 0 < C) {u : ℂ} (hu : u ∈ disk) : stripY a C u ∈ halfStrip a C := by
  obtain ⟨h1, h2, -⟩ := stripZ_of_mem ha hC hu
  have hβ := stripBeta_pos hC
  set z := stripZ (stripW a C u) with hz
  have hzne := stripZ_ne_zero h1
  have hre : (stripY a C u).re = a + Real.log ‖z‖ / stripBeta C := by
    rw [stripY, ← hz, Complex.add_re, Complex.ofReal_re, Complex.div_ofReal_re, Complex.log_re]
  have him : (stripY a C u).im = arg z / stripBeta C := by
    rw [stripY, ← hz, Complex.add_im, Complex.ofReal_im, zero_add, Complex.div_ofReal_im, Complex.log_im]
  constructor
  · rw [hre]
    have h3 : Real.log ‖z‖ < 0 := Real.log_neg (norm_pos_iff.2 hzne) h2
    have h4 := div_neg_of_neg_of_pos h3 hβ
    linarith
  · rw [him, abs_div, abs_of_pos hβ, div_lt_iff₀ hβ, mul_comm, stripBeta_mul hC]
    exact Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl h1)

theorem strip_sinh_eq {a C : ℝ} (ha : 0 < a) (hC : 0 < C) {u : ℂ} (hu : u ∈ disk) :
    Complex.sinh (stripBeta C * (stripY a C u - a)) = stripW a C u := by
  obtain ⟨h1, -, h3⟩ := stripZ_of_mem ha hC hu
  have hβ : (stripBeta C : ℂ) ≠ 0 := by exact_mod_cast (stripBeta_pos hC).ne'
  set z := stripZ (stripW a C u) with hz
  have hzne := stripZ_ne_zero h1
  have h4 : (stripBeta C : ℂ) * (stripY a C u - a) = Complex.log z := by
    rw [stripY, ← hz]
    field_simp
    ring
  rw [h4, Complex.sinh, Complex.exp_neg, Complex.exp_log hzne, h3]
  ring

theorem stripT_stripY {a C : ℝ} (ha : 0 < a) (hC : 0 < C) {u : ℂ} (hu : u ∈ disk) : stripT a C (stripY a C u) = u := by
  have hs : (Real.sinh (stripBeta C * a) : ℂ) ≠ 0 := by exact_mod_cast (strip_s_pos ha hC).ne'
  have hne := one_add_ne_zero_of_mem hu
  rw [stripT, strip_sinh_eq ha hC hu, stripW]
  field_simp
  ring

theorem stripY_differentiableOn {a C : ℝ} (ha : 0 < a) (hC : 0 < C) : DifferentiableOn ℂ (stripY a C) disk := by
  intro u hu
  have hu' : u ∈ disk := hu
  refine DifferentiableAt.differentiableWithinAt ?_
  have hne := one_add_ne_zero_of_mem hu'
  have hre := stripW_re_neg ha hC hu'
  have hw : DifferentiableAt ℂ (stripW a C) u := by
    unfold stripW
    exact ((differentiableAt_const _).mul ((differentiableAt_const _).sub differentiableAt_id)).div
      ((differentiableAt_const _).add differentiableAt_id) hne
  have hm : DifferentiableAt ℂ (fun u => (stripW a C u - I) / (stripW a C u + I)) u :=
    (hw.sub_const _).div (hw.add_const _) (stripW_add_I_ne hre)
  have hmim := stripM_im_pos hre
  obtain ⟨-, hp1, hp2⟩ := sqrt_first_quadrant hmim
  obtain ⟨h1, -, h3, -⟩ := stripZ_props hp1 hp2
  have hp : DifferentiableAt ℂ (fun u => ((stripW a C u - I) / (stripW a C u + I)) ^ (1 / 2 : ℂ)) u :=
    hm.cpow (differentiableAt_const _) (Or.inr hmim.ne')
  have hz : DifferentiableAt ℂ (fun u => stripZ (stripW a C u)) u := by
    unfold stripZ
    exact (differentiableAt_const _).mul ((hp.sub_const _).div (hp.add_const _) h1)
  have hslit : stripZ (stripW a C u) ∈ slitPlane := Or.inl h3
  unfold stripY
  exact (differentiableAt_const _).add ((hz.clog hslit).div_const _)

/-! ### `sinh` on the half strip -/

theorem sinh_strip (α γ : ℝ) :
    Complex.sinh ((α : ℂ) + γ * I) = ((Real.sinh α * Real.cos γ : ℝ) : ℂ) + ((Real.cosh α * Real.sin γ : ℝ) : ℂ) * I := by
  rw [Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I]
  push_cast
  ring

/-- The real and imaginary coordinates of `β (y - a)`. -/
theorem strip_coords (a C : ℝ) (y : ℂ) :
    (stripBeta C : ℂ) * (y - a) = ((stripBeta C * (y.re - a) : ℝ) : ℂ) + ((stripBeta C * y.im : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp

theorem strip_gamma_lt {a C : ℝ} (hC : 0 < C) {y : ℂ} (hy : y ∈ halfStrip a C) : |stripBeta C * y.im| < Real.pi / 2 := by
  rw [abs_mul, abs_of_pos (stripBeta_pos hC), ← stripBeta_mul hC]
  exact mul_lt_mul_of_pos_left hy.2 (stripBeta_pos hC)

theorem strip_sinh_re_neg {a C : ℝ} (hC : 0 < C) {y : ℂ} (hy : y ∈ halfStrip a C) :
    (Complex.sinh (stripBeta C * (y - a))).re < 0 := by
  have hβ := stripBeta_pos hC
  have hγ := strip_gamma_lt hC hy
  have h1 : Real.sinh (stripBeta C * (y.re - a)) < 0 :=
    Real.sinh_neg_iff.2 (mul_neg_of_pos_of_neg hβ (by linarith [hy.1]))
  have h2 : 0 < Real.cos (stripBeta C * y.im) :=
    Real.cos_pos_of_mem_Ioo ⟨(abs_lt.1 hγ).1, (abs_lt.1 hγ).2⟩
  have hline : ∀ A B : ℝ, ((A : ℂ) + (B : ℂ) * I).re = A := fun A B => by simp
  rw [strip_coords, sinh_strip, hline]
  exact mul_neg_of_neg_of_pos h1 h2

/-- `|-s - W| < |-s + W|` for `s > 0`, `Re W < 0`. -/
theorem norm_sub_lt_norm_add {s : ℝ} (hs : 0 < s) {W : ℂ} (hW : W.re < 0) :
    ‖-(s : ℂ) - W‖ < ‖-(s : ℂ) + W‖ := by
  refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
  rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
  simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.sub_im, Complex.add_im,
    Complex.neg_im, Complex.ofReal_im]
  nlinarith

theorem strip_denom_ne {s : ℝ} (hs : 0 < s) {W : ℂ} (hW : W.re < 0) : -(s : ℂ) + W ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

/-- `T` is holomorphic on the half strip. -/
theorem stripT_hasDerivAt {a C : ℝ} (ha : 0 < a) (hC : 0 < C) {y : ℂ} (hy : y ∈ halfStrip a C) :
    HasDerivAt (stripT a C)
      (2 * (Real.sinh (stripBeta C * a) : ℂ) * ((stripBeta C : ℂ) * Complex.cosh (stripBeta C * (y - a))) /
        (-(Real.sinh (stripBeta C * a) : ℂ) + Complex.sinh (stripBeta C * (y - a))) ^ 2) y := by
  have hs := strip_s_pos ha hC
  have hW := strip_sinh_re_neg hC hy
  have hdn := strip_denom_ne hs hW
  have h1 : HasDerivAt (fun y : ℂ => (stripBeta C : ℂ) * (y - a)) (stripBeta C : ℂ) y := by
    simpa using ((hasDerivAt_id y).sub_const (a : ℂ)).const_mul (stripBeta C : ℂ)
  have h2 : HasDerivAt (fun y : ℂ => Complex.sinh ((stripBeta C : ℂ) * (y - a)))
      (Complex.cosh ((stripBeta C : ℂ) * (y - a)) * (stripBeta C : ℂ)) y := (Complex.hasDerivAt_sinh _).comp y h1
  have h3 := (h2.const_sub (-(Real.sinh (stripBeta C * a) : ℂ))).div (h2.const_add (-(Real.sinh (stripBeta C * a) : ℂ))) hdn
  refine h3.congr_deriv ?_
  generalize Complex.sinh ((stripBeta C : ℂ) * (y - a)) = W at hdn ⊢
  field_simp
  ring

theorem stripY_deriv_ne_zero {a C : ℝ} (ha : 0 < a) (hC : 0 < C) {u : ℂ} (hu : u ∈ disk) :
    deriv (stripY a C) u ≠ 0 := by
  have hyat : HasDerivAt (stripY a C) (deriv (stripY a C) u) u :=
    ((stripY_differentiableOn ha hC).differentiableAt (isOpen_ball.mem_nhds hu)).hasDerivAt
  have h1 := (stripT_hasDerivAt ha hC (stripY_mem ha hC hu)).comp u hyat
  have h2 : (stripT a C ∘ stripY a C) =ᶠ[𝓝 u] id := by
    filter_upwards [isOpen_ball.mem_nhds hu] with v hv using stripT_stripY ha hC hv
  have h3 := (h1.congr_of_eventuallyEq h2.symm).unique (hasDerivAt_id u)
  intro h0
  rw [h0, mul_zero] at h3
  exact zero_ne_one h3

/-! ### At `0` -/

theorem stripY_zero {a C : ℝ} (ha : 0 < a) (hC : 0 < C) : stripY a C 0 = 0 := by
  have h0mem : (0 : ℂ) ∈ disk := mem_ball_self one_pos
  obtain ⟨h1, h2, h3⟩ := stripZ_of_mem ha hC h0mem
  have hβ := stripBeta_pos hC
  set z := stripZ (stripW a C 0) with hz
  have hzne := stripZ_ne_zero h1
  set e : ℝ := Real.exp (-(stripBeta C * a)) with he
  have hepos : 0 < e := Real.exp_pos _
  have he1 : e < 1 := by
    have h4 : -(stripBeta C * a) < 0 := by have := mul_pos hβ ha; linarith
    have h5 := Real.exp_lt_exp.2 h4
    rwa [Real.exp_zero] at h5
  have hw0 : stripW a C 0 = -(Real.sinh (stripBeta C * a) : ℂ) := by simp [stripW]
  have hsinh : ((e : ℂ) - (e : ℂ)⁻¹) = -2 * (Real.sinh (stripBeta C * a) : ℂ) := by
    rw [Complex.ofReal_sinh, Complex.sinh, he, Complex.ofReal_exp, ← Complex.exp_neg]
    push_cast
    ring_nf
  have hec : (e : ℂ) ≠ 0 := by exact_mod_cast hepos.ne'
  have heq : z - z⁻¹ = (e : ℂ) - (e : ℂ)⁻¹ := by rw [h3, hw0, hsinh]; ring
  have hfac : (z - e) * (z * e + 1) = 0 := by
    field_simp at heq
    linear_combination heq
  have hzev : z = e := by
    rcases mul_eq_zero.1 hfac with h | h
    · linear_combination h
    · exfalso
      have h4 : z * e = -1 := by linear_combination h
      have h5 : ‖z * (e : ℂ)‖ < 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hepos.le]
        nlinarith [norm_nonneg z]
      rw [h4, norm_neg, norm_one] at h5
      exact lt_irrefl _ h5
  have hβc : (stripBeta C : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  rw [stripY, ← hz, hzev, ← Complex.ofReal_log hepos.le, he, Real.log_exp]
  push_cast
  field_simp
  ring

theorem stripT_zero (a C : ℝ) : stripT a C 0 = 0 := by
  have h1 : Complex.sinh ((stripBeta C : ℂ) * (0 - a)) = -(Real.sinh (stripBeta C * a) : ℂ) := by
    rw [Complex.ofReal_sinh, ← Complex.sinh_neg]
    push_cast
    ring_nf
  rw [stripT, h1]
  simp

theorem stripY_ne_zero {a C : ℝ} (ha : 0 < a) (hC : 0 < C) {u : ℂ} (hu : u ∈ disk) (h0 : u ≠ 0) :
    stripY a C u ≠ 0 := by
  intro h
  have h1 := stripT_stripY ha hC hu
  rw [h, stripT_zero a C] at h1
  exact h0 h1.symm

/-- `sinh x ≤ x cosh x` for `x ≥ 0`. -/
theorem sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) : Real.sinh x ≤ x * Real.cosh x := by
  have h1 := Convex.image_sub_le_mul_sub_of_deriv_le (D := Icc 0 x) (f := Real.sinh) (C := Real.cosh x) (convex_Icc 0 x)
    Real.continuous_sinh.continuousOn Real.differentiable_sinh.differentiableOn (fun t ht => by
      rw [Real.deriv_sinh, interior_Icc] at *
      refine Real.cosh_le_cosh.2 ?_
      rw [abs_of_pos ht.1, abs_of_nonneg hx]
      exact ht.2.le)
    0 (left_mem_Icc.2 hx) x (right_mem_Icc.2 hx) hx
  simpa [mul_comm] using h1

/-- `y'(0) = 2 tanh(β a)/β ≤ 2 a`. -/
theorem stripY_deriv_zero {a C : ℝ} (ha : 0 < a) (hC : 0 < C) : ‖deriv (stripY a C) 0‖ ≤ 2 * a := by
  have h0mem : (0 : ℂ) ∈ disk := mem_ball_self one_pos
  have hβ := stripBeta_pos hC
  have hs := strip_s_pos ha hC
  set s : ℝ := Real.sinh (stripBeta C * a) with hsdef
  have hyat : HasDerivAt (stripY a C) (deriv (stripY a C) 0) 0 :=
    ((stripY_differentiableOn ha hC).differentiableAt (isOpen_ball.mem_nhds h0mem)).hasDerivAt
  have hy0 := stripY_zero ha hC
  have hmem := stripY_mem ha hC h0mem
  have hT := stripT_hasDerivAt ha hC hmem
  have h1 := hT.comp (0 : ℂ) hyat
  have h2 : (stripT a C ∘ stripY a C) =ᶠ[𝓝 (0 : ℂ)] id := by
    filter_upwards [isOpen_ball.mem_nhds h0mem] with v hv using stripT_stripY ha hC hv
  have h3 := (h1.congr_of_eventuallyEq h2.symm).unique (hasDerivAt_id (0 : ℂ))
  rw [hy0] at h3
  have hW : Complex.sinh ((stripBeta C : ℂ) * (0 - a)) = -(s : ℂ) := by
    rw [hsdef, Complex.ofReal_sinh, ← Complex.sinh_neg]
    push_cast
    ring_nf
  have hCh : Complex.cosh ((stripBeta C : ℂ) * (0 - a)) = (Real.cosh (stripBeta C * a) : ℂ) := by
    rw [Complex.ofReal_cosh, ← Complex.cosh_neg]
    push_cast
    ring_nf
  rw [hW, hCh, ← hsdef] at h3
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hβc : (stripBeta C : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  have hch : 0 < Real.cosh (stripBeta C * a) := Real.cosh_pos _
  have hchc : (Real.cosh (stripBeta C * a) : ℂ) ≠ 0 := by exact_mod_cast hch.ne'
  have h2s : (2 * (s : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hsc
  have h5 : -(s : ℂ) + -(s : ℂ) ≠ 0 := by
    intro h
    apply h2s
    linear_combination -h
  have hgen : ∀ Ch : ℝ, (Ch : ℂ) ≠ 0 →
      2 * (s : ℂ) * ((stripBeta C : ℂ) * (Ch : ℂ)) / (-(s : ℂ) + -(s : ℂ)) ^ 2 * deriv (stripY a C) 0 = 1 →
      deriv (stripY a C) 0 = ((2 * s / (stripBeta C * Ch) : ℝ) : ℂ) := by
    intro Ch hCh0 h6
    push_cast
    rw [eq_div_iff (mul_ne_zero hβc hCh0)]
    rw [div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 h5)] at h6
    refine mul_left_cancel₀ h2s ?_
    linear_combination h6
  have hd := hgen _ hchc h3
  rw [hd, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
  have h4 := sinh_le_mul_cosh (x := stripBeta C * a) (by positivity)
  rw [← hsdef] at h4
  nlinarith

/-! ### The low parts, and the collar -/

theorem norm_line_sq' (s t : ℝ) : ‖(s : ℂ) + (t : ℂ) * I‖ ^ 2 = s ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_add_mul_I]

/-- The low parts of the half strip go near `u = -1`. -/
theorem stripT_low {a C : ℝ} (ha : 0 < a) (hC : 1 ≤ C) {y : ℂ} (hy : y ∈ halfStrip a C)
    (h : y.re ≤ -C ∨ C - 1 / 2 ≤ |y.im|) :
    ‖stripT a C y + 1‖ ≤ 4 * Real.sinh (stripBeta C * a) := by
  have hC0 : 0 < C := by linarith
  have hβ := stripBeta_pos hC0
  have hs := strip_s_pos ha hC0
  set s : ℝ := Real.sinh (stripBeta C * a) with hsdef
  set W : ℂ := Complex.sinh (stripBeta C * (y - a)) with hW
  have hWre : W.re < 0 := strip_sinh_re_neg hC0 hy
  have hdn := strip_denom_ne hs hWre
  have hid : stripT a C y + 1 = -(2 * (s : ℂ)) / (-(s : ℂ) + W) := by
    rw [stripT, ← hsdef, ← hW]
    field_simp
    ring
  set α : ℝ := stripBeta C * (y.re - a) with hα
  set γ : ℝ := stripBeta C * y.im with hγ
  have hWform : W = ((Real.sinh α * Real.cos γ : ℝ) : ℂ) + ((Real.cosh α * Real.sin γ : ℝ) : ℂ) * I := by
    rw [hW, strip_coords, sinh_strip]
  have hWnsq : ‖W‖ ^ 2 = Real.sinh α ^ 2 + Real.sin γ ^ 2 := by
    rw [hWform, norm_line_sq']
    have h1 := Real.cosh_sq α
    have h2 := Real.sin_sq_add_cos_sq γ
    nlinarith
  -- `|W| ≥ 1/2`
  have hW12 : 1 / 2 ≤ ‖W‖ := by
    have hsq : (1 / 2 : ℝ) ^ 2 ≤ ‖W‖ ^ 2 := by
      rw [hWnsq]
      rcases h with h | h
      · have h1 : Real.pi / 2 ≤ -α := by
          rw [hα, ← stripBeta_mul hC0]
          nlinarith
        have h2 : -α ≤ Real.sinh (-α) := Real.self_le_sinh_iff.2 (by linarith [Real.pi_pos])
        rw [Real.sinh_neg] at h2
        have h3 : 1 ≤ -Real.sinh α := by linarith [Real.pi_gt_three]
        nlinarith [sq_nonneg (Real.sin γ)]
      · have h1 : Real.pi / 4 ≤ |γ| := by
          rw [hγ, abs_mul, abs_of_pos hβ]
          have h2 : stripBeta C * (C - 1 / 2) ≤ stripBeta C * |y.im| := mul_le_mul_of_nonneg_left h hβ.le
          have h3 : stripBeta C * (C - 1 / 2) = Real.pi / 2 - stripBeta C / 2 := by
            rw [mul_sub, stripBeta_mul hC0]
            ring
          have h4 : stripBeta C ≤ Real.pi / 2 := by
            rw [stripBeta, div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith [Real.pi_pos]
          linarith
        have h2 : |γ| < Real.pi / 2 := strip_gamma_lt hC0 hy
        have h3 : Real.sin (Real.pi / 6) ≤ Real.sin |γ| :=
          Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) h2.le (by linarith [Real.pi_pos])
        rw [Real.sin_pi_div_six] at h3
        have h4 : Real.sin γ ^ 2 = Real.sin |γ| ^ 2 := by
          rcases abs_cases γ with ⟨h5, -⟩ | ⟨h5, -⟩
          · rw [h5]
          · rw [h5, Real.sin_neg]
            ring
        rw [h4]
        nlinarith [sq_nonneg (Real.sinh α)]
    exact (pow_le_pow_iff_left₀ (by norm_num) (norm_nonneg _) two_ne_zero).1 hsq
  -- `|W - s| ≥ |W|`
  have hge : ‖W‖ ≤ ‖-(s : ℂ) + W‖ := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
    simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.add_im, Complex.neg_im, Complex.ofReal_im]
    nlinarith
  have hdpos : 0 < ‖-(s : ℂ) + W‖ := norm_pos_iff.2 hdn
  rw [hid, norm_div, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le, div_le_iff₀ hdpos]
  simp only [Complex.norm_ofNat]
  nlinarith

/-- The compact middle part of the half strip stays inside a smaller disk under `T`. -/
theorem stripT_collar {a C : ℝ} (ha : 0 < a) (hC : 1 ≤ C) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ y : ℂ, -C ≤ y.re → y.re ≤ a - 1 → |y.im| ≤ C - 1 / 2 → ‖stripT a C y‖ ≤ r := by
  have hC0 : 0 < C := by linarith
  have hs := strip_s_pos ha hC0
  set K : Set ℂ := Icc (-C) (a - 1) ×ℂ Icc (-(C - 1 / 2)) (C - 1 / 2) with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hKS : ∀ y ∈ K, y ∈ halfStrip a C := by
    intro y hy
    rw [hK, mem_reProdIm] at hy
    refine ⟨by linarith [hy.1.2], ?_⟩
    rw [abs_lt]
    constructor <;> linarith [hy.2.1, hy.2.2]
  have hcont : ContinuousOn (fun y => 1 - ‖stripT a C y‖) K := fun y hy =>
    (continuousAt_const.sub (stripT_hasDerivAt ha hC0 (hKS y hy)).continuousAt.norm).continuousWithinAt
  have hpos : ∀ y ∈ K, (0 : ℝ) < 1 - ‖stripT a C y‖ := by
    intro y hy
    have hW := strip_sinh_re_neg hC0 (hKS y hy)
    have hlt := norm_sub_lt_norm_add hs hW
    have hdn := norm_pos_iff.2 (strip_denom_ne hs hW)
    have h1 : ‖stripT a C y‖ < 1 := by
      rw [stripT, norm_div, div_lt_one hdn]
      exact hlt
    linarith
  obtain ⟨η, hη, hlow⟩ := hKc.exists_forall_le' hcont hpos
  refine ⟨max (1 - η) 0, le_max_right _ _, max_lt (by linarith) one_pos, fun y h1 h2 h3 => ?_⟩
  have hmem : y ∈ K := by
    rw [hK, mem_reProdIm]
    exact ⟨⟨h1, h2⟩, abs_le.1 h3⟩
  have := hlow y hmem
  exact le_max_of_le_left (by linarith)

end Smale.P030
