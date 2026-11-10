/-
Smale/P030/WSide.lean — the `W` side of the pair: the Koebe-type map `koebeD`, the comb `ζ + lam Σ log(ζ - x)`, the Cayley map
and its inverse, and their composition `combDisc`, near the identity at `0` for small `lam`. Elementary functions only.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Smale.P030.Defs

namespace Smale.P030

open Complex Metric Set Filter Topology

/-! ### `koebeD` -/

theorem koebe_den_ne {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1) {t : ℂ} (ht : t ∈ disk) : (1 : ℂ) + δ * t ≠ 0 := by
  intro h
  have ht1 : ‖t‖ < 1 := by simpa using ht
  have h2 : ‖(δ : ℂ) * t‖ = 1 := by
    have h3 : (δ : ℂ) * t = -1 := by linear_combination h
    rw [h3, norm_neg, norm_one]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0] at h2
  have h4 := mul_le_of_le_one_right h0 ht1.le
  linarith

theorem koebeD_hasDerivAt {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1) {t : ℂ} (ht : t ∈ disk) :
    HasDerivAt (koebeD δ) ((1 - δ * t) / (1 + δ * t) ^ 3) t := by
  have hne := koebe_den_ne h0 h1 ht
  have h2 : HasDerivAt (fun t : ℂ => 1 + (δ : ℂ) * t) (δ : ℂ) t := by
    simpa using ((hasDerivAt_id t).const_mul (δ : ℂ)).const_add 1
  have h3 := h2.fun_pow 2
  have h4 := (hasDerivAt_id t).div h3 (pow_ne_zero 2 hne)
  refine h4.congr_deriv ?_
  simp only [id]
  norm_num
  field_simp
  ring

theorem koebeD_differentiableOn {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1) : DifferentiableOn ℂ (koebeD δ) disk := fun _ ht =>
  (koebeD_hasDerivAt h0 h1 ht).differentiableAt.differentiableWithinAt

theorem koebeD_injOn {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1) : InjOn (koebeD δ) disk := by
  intro a ha b hb hab
  have hA := koebe_den_ne h0 h1 ha
  have hB := koebe_den_ne h0 h1 hb
  have ha1 : ‖a‖ < 1 := by simpa using ha
  have hb1 : ‖b‖ < 1 := by simpa using hb
  have hx : a * (1 + (δ : ℂ) * b) ^ 2 = b * (1 + (δ : ℂ) * a) ^ 2 := by
    have h2 : a / (1 + (δ : ℂ) * a) ^ 2 = b / (1 + (δ : ℂ) * b) ^ 2 := hab
    rwa [div_eq_div_iff (pow_ne_zero 2 hA) (pow_ne_zero 2 hB)] at h2
  have hfac : (a - b) * (1 - (δ : ℂ) ^ 2 * (a * b)) = 0 := by linear_combination hx
  rcases mul_eq_zero.1 hfac with h | h
  · exact sub_eq_zero.1 h
  · exfalso
    have h2 : (δ : ℂ) ^ 2 * (a * b) = 1 := by linear_combination -h
    have h3 := congrArg norm h2
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg h0, norm_one] at h3
    have h4 : ‖a‖ * ‖b‖ < 1 := by nlinarith [norm_nonneg a, norm_nonneg b]
    have h5 : δ ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (norm_nonneg a) (norm_nonneg b), sq_nonneg δ]

theorem koebeD_norm_le {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1) {t : ℂ} (ht : t ∈ disk) :
    ‖koebeD δ t‖ ≤ 1 / (1 - δ) ^ 2 := by
  have ht1 : ‖t‖ < 1 := by simpa using ht
  have hδ1 : 0 < 1 - δ := by linarith
  have h2 := norm_sub_norm_le (1 : ℂ) (-((δ : ℂ) * t))
  rw [sub_neg_eq_add, norm_one, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0] at h2
  have h3 := mul_le_of_le_one_right h0 ht1.le
  have hden : 1 - δ ≤ ‖(1 : ℂ) + δ * t‖ := by linarith
  have hdenpos : 0 < ‖(1 : ℂ) + δ * t‖ := by linarith
  rw [koebeD, norm_div, norm_pow, div_le_div_iff₀ (pow_pos hdenpos 2) (pow_pos hδ1 2)]
  have h4 : (1 - δ) ^ 2 ≤ ‖(1 : ℂ) + δ * t‖ ^ 2 := pow_le_pow_left₀ hδ1.le hden 2
  nlinarith [norm_nonneg t, pow_pos hδ1 2]

/-- Near `0`: `k_δ` is small and `k_δ'` is near `1`. -/
theorem koebeD_near_zero (δ : ℝ) {e : ℝ} (he : 0 < e) :
    ∃ e' : ℝ, 0 < e' ∧ e' ≤ 1 ∧ ∀ s : ℂ, ‖s‖ < e' → ‖koebeD δ s‖ < e ∧ ‖(1 - δ * s) / (1 + δ * s) ^ 3 - 1‖ < e := by
  have hc1 : ContinuousAt (fun s : ℂ => s / (1 + (δ : ℂ) * s) ^ 2) 0 :=
    ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)
  have hc2 : ContinuousAt (fun s : ℂ => (1 - (δ : ℂ) * s) / (1 + (δ : ℂ) * s) ^ 3) 0 :=
    ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)
  obtain ⟨d1, hd1, h1⟩ := Metric.continuousAt_iff.1 hc1 e he
  obtain ⟨d2, hd2, h2⟩ := Metric.continuousAt_iff.1 hc2 e he
  refine ⟨min (min d1 d2) 1, lt_min (lt_min hd1 hd2) one_pos, min_le_right _ _, fun s hs => ?_⟩
  have hs1 : dist s 0 < d1 := by
    rw [dist_zero_right]
    exact hs.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hs2 : dist s 0 < d2 := by
    rw [dist_zero_right]
    exact hs.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have ha := h1 hs1
  have hb := h2 hs2
  have h00 : (0 : ℂ) / (1 + (δ : ℂ) * 0) ^ 2 = 0 := by simp
  have h01 : (1 - (δ : ℂ) * 0) / (1 + (δ : ℂ) * 0) ^ 3 = 1 := by simp
  simp only [h00, h01] at ha hb
  rw [dist_zero_right] at ha
  rw [dist_eq_norm] at hb
  exact ⟨ha, hb⟩

/-- Near `1`, `|k_δ|` is near `k_δ(1) = 1/(1 + δ)²`. -/
theorem koebeD_near_one {δ : ℝ} (h0 : 0 ≤ δ) {e : ℝ} (he : 0 < e) :
    ∃ e' : ℝ, 0 < e' ∧ ∀ s : ℂ, ‖s - 1‖ < e' → ‖koebeD δ s‖ < 1 / (1 + δ) ^ 2 + e := by
  have hcast : (1 : ℂ) + (δ : ℂ) * 1 = ((1 + δ : ℝ) : ℂ) := by push_cast; ring
  have hne : (1 : ℂ) + (δ : ℂ) * 1 ≠ 0 := by
    rw [hcast]
    exact_mod_cast (by linarith : (1 + δ : ℝ) ≠ 0)
  have hc : ContinuousAt (fun s : ℂ => s / (1 + (δ : ℂ) * s) ^ 2) 1 :=
    ContinuousAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 2 hne)
  obtain ⟨d, hd, h⟩ := Metric.continuousAt_iff.1 hc e he
  refine ⟨d, hd, fun s hs => ?_⟩
  have ha := h (x := s) (by rwa [dist_eq_norm])
  have hn : ‖(1 : ℂ) / (1 + (δ : ℂ) * 1) ^ 2‖ = 1 / (1 + δ) ^ 2 := by
    rw [hcast, norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [dist_eq_norm] at ha
  have h2 := norm_sub_norm_le (s / (1 + (δ : ℂ) * s) ^ 2) ((1 : ℂ) / (1 + (δ : ℂ) * 1) ^ 2)
  rw [hn] at h2
  show ‖s / (1 + (δ : ℂ) * s) ^ 2‖ < _
  linarith

/-! ### The comb -/

theorem comb_hasDerivAt (lam : ℝ) (xs : Finset ℝ) {ζ : ℂ} (hζ : 0 < ζ.im) :
    HasDerivAt (comb lam xs) (1 + (lam : ℂ) * ∑ x ∈ xs, 1 / (ζ - x)) ζ := by
  have hmem : ∀ x : ℝ, ζ - x ∈ slitPlane := fun x => Or.inr (by simpa using hζ.ne')
  have h1 : ∀ x ∈ xs, HasDerivAt (fun z : ℂ => Complex.log (z - x)) (1 / (ζ - x)) ζ := fun x _ => by
    simpa using ((hasDerivAt_id ζ).sub_const (x : ℂ)).clog (hmem x)
  exact (hasDerivAt_id ζ).add ((HasDerivAt.fun_sum h1).const_mul (lam : ℂ))

theorem comb_differentiableOn (lam : ℝ) (xs : Finset ℝ) : DifferentiableOn ℂ (comb lam xs) {ζ | 0 < ζ.im} := fun _ hζ =>
  (comb_hasDerivAt lam xs hζ).differentiableAt.differentiableWithinAt

theorem comb_im_pos {lam : ℝ} (h : 0 ≤ lam) (xs : Finset ℝ) {ζ : ℂ} (hζ : 0 < ζ.im) : 0 < (comb lam xs ζ).im := by
  rw [comb, Complex.add_im, Complex.im_ofReal_mul, Complex.im_sum]
  have h1 : 0 ≤ ∑ x ∈ xs, (Complex.log (ζ - x)).im := Finset.sum_nonneg fun x _ => by
    rw [Complex.log_im]
    exact Complex.arg_nonneg_iff.2 (by simpa using hζ.le)
  have h2 := mul_nonneg h h1
  linarith

/-- `Im G' < 0` on the convex upper half plane, so `G` is injective there (Noshiro-Warschawski, rotated). -/
theorem comb_injOn {lam : ℝ} (h : 0 ≤ lam) (xs : Finset ℝ) : InjOn (comb lam xs) {ζ | 0 < ζ.im} := by
  intro z₁ h₁ z₂ h₂ heq
  by_contra hne
  have h₁' : 0 < z₁.im := h₁
  have h₂' : 0 < z₂.im := h₂
  by_cases hdeg : lam = 0 ∨ xs = ∅
  · rcases hdeg with hd | hd
    · simp [comb, hd] at heq
      exact hne heq
    · simp [comb, hd] at heq
      exact hne heq
  · push Not at hdeg
    obtain ⟨hl, hxs⟩ := hdeg
    have hlpos : 0 < lam := lt_of_le_of_ne h (Ne.symm hl)
    have hxsne : xs.Nonempty := hxs
    set d : ℂ := z₂ - z₁ with hd
    have hdne : d ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    have hline : ∀ τ ∈ Icc (0 : ℝ) 1, 0 < (z₁ + (τ : ℂ) * d).im := by
      intro τ hτ
      have h1 : (z₁ + (τ : ℂ) * d).im = z₁.im + τ * (z₂.im - z₁.im) := by simp [hd]
      rw [h1]
      rcases hτ.1.eq_or_lt with h0 | h0
      · rw [← h0]
        simpa using h₁'
      · have h2 : 0 < τ * z₂.im := mul_pos h0 h₂'
        have h3 : 0 ≤ (1 - τ) * z₁.im := mul_nonneg (by linarith [hτ.2]) h₁'.le
        nlinarith
    set f : ℝ → ℝ := fun τ => (comb lam xs (z₁ + (τ : ℂ) * d) / d).im with hf
    have hderiv : ∀ τ ∈ Icc (0 : ℝ) 1,
        HasDerivAt f ((1 + (lam : ℂ) * ∑ x ∈ xs, 1 / (z₁ + (τ : ℂ) * d - x)).im) τ := by
      intro τ hτ
      have h1 : HasDerivAt (fun w : ℂ => z₁ + w * d) d (τ : ℂ) := by
        simpa using ((hasDerivAt_id (τ : ℂ)).mul_const d).const_add z₁
      have h2 := (comb_hasDerivAt lam xs (hline τ hτ)).comp (τ : ℂ) h1
      have h3 := (h2.comp_ofReal).div_const d
      have h4 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt τ h3
      have h5 : Complex.imCLM ((1 + (lam : ℂ) * ∑ x ∈ xs, 1 / (z₁ + (τ : ℂ) * d - x)) * d / d) =
          (1 + (lam : ℂ) * ∑ x ∈ xs, 1 / (z₁ + (τ : ℂ) * d - x)).im := by
        rw [mul_div_cancel_right₀ _ hdne]
        rfl
      rw [← h5]
      exact h4
    have hneg : ∀ τ ∈ Icc (0 : ℝ) 1, (1 + (lam : ℂ) * ∑ x ∈ xs, 1 / (z₁ + (τ : ℂ) * d - x)).im < 0 := by
      intro τ hτ
      rw [Complex.add_im, Complex.one_im, zero_add, Complex.im_ofReal_mul, Complex.im_sum]
      refine mul_neg_of_pos_of_neg hlpos (Finset.sum_neg (fun x _ => ?_) hxsne)
      have him : 0 < (z₁ + (τ : ℂ) * d - x).im := by
        have := hline τ hτ
        simpa using this
      have hzne : z₁ + (τ : ℂ) * d - x ≠ 0 := by
        intro h0
        rw [h0] at him
        simp at him
      rw [one_div, Complex.inv_im]
      exact div_neg_of_neg_of_pos (by linarith) (normSq_pos.2 hzne)
    have hanti : StrictAntiOn f (Icc 0 1) := by
      refine strictAntiOn_of_deriv_neg (convex_Icc 0 1) (fun τ hτ => (hderiv τ hτ).continuousAt.continuousWithinAt) ?_
      intro τ hτ
      have hτ' : τ ∈ Icc (0 : ℝ) 1 := interior_subset hτ
      rw [(hderiv τ hτ').deriv]
      exact hneg τ hτ'
    have hlt := hanti (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) zero_lt_one
    have hf0 : f 0 = (comb lam xs z₁ / d).im := by simp [hf]
    have hf1 : f 1 = (comb lam xs z₂ / d).im := by simp [hf, hd]
    rw [hf0, hf1, heq] at hlt
    exact lt_irrefl _ hlt

/-- `G` tends to infinity at each `x ∈ xs`: `Re G = λ log|ζ - x| + bounded`. -/
theorem comb_large {lam x : ℝ} (h : 0 < lam) {xs : Finset ℝ} (hx : x ∈ xs) (L : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ζ : ℂ, 0 < ζ.im → ‖ζ - x‖ < ρ → L < ‖comb lam xs ζ‖ := by
  classical
  set Bd : ℝ := |x| + 1 + lam * ∑ x' ∈ xs.erase x, Real.log (|x - x'| + 1) with hBd
  set ρ : ℝ := min 1 (Real.exp ((-|L| - 1 - Bd) / lam)) with hρ
  have hρpos : 0 < ρ := lt_min one_pos (Real.exp_pos _)
  refine ⟨ρ, hρpos, fun ζ hζ hd => ?_⟩
  have hd1 : ‖ζ - x‖ < 1 := hd.trans_le (min_le_left _ _)
  have hne : ∀ y : ℝ, 0 < ‖ζ - y‖ := fun y => by
    refine norm_pos_iff.2 fun h0 => ?_
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hre : (comb lam xs ζ).re = ζ.re + lam * (Real.log ‖ζ - x‖ + ∑ x' ∈ xs.erase x, Real.log ‖ζ - x'‖) := by
    rw [comb, Complex.add_re, Complex.re_ofReal_mul, Complex.re_sum, Finset.add_sum_erase xs (fun y : ℝ => Real.log ‖ζ - y‖) hx]
    simp only [Complex.log_re]
  have hsum : ∑ x' ∈ xs.erase x, Real.log ‖ζ - x'‖ ≤ ∑ x' ∈ xs.erase x, Real.log (|x - x'| + 1) := by
    refine Finset.sum_le_sum fun y _ => Real.log_le_log (hne y) ?_
    have h1 : ζ - y = (ζ - x) + ((x - y : ℝ) : ℂ) := by push_cast; ring
    rw [h1]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hreζ : ζ.re ≤ |x| + 1 := by
    have h1 : ζ.re - x ≤ ‖ζ - x‖ := by
      have := Complex.re_le_norm (ζ - x)
      simpa using this
    have h2 := le_abs_self x
    linarith
  have hlog : Real.log ‖ζ - x‖ < (-|L| - 1 - Bd) / lam := by
    have h1 : ‖ζ - x‖ < Real.exp ((-|L| - 1 - Bd) / lam) := hd.trans_le (min_le_right _ _)
    exact (Real.log_lt_iff_lt_exp (hne x)).2 h1
  have hlog2 : lam * Real.log ‖ζ - x‖ < -|L| - 1 - Bd := by
    have := mul_lt_mul_of_pos_left hlog h
    rwa [mul_div_cancel₀ _ h.ne'] at this
  have hsum2 := mul_le_mul_of_nonneg_left hsum h.le
  have hReBound : (comb lam xs ζ).re < -|L| - 1 := by
    rw [hre, mul_add, hBd] at *
    linarith
  have hn := Complex.abs_re_le_norm (comb lam xs ζ)
  have hL := le_abs_self L
  have h3 := neg_abs_le (comb lam xs ζ).re
  linarith

/-! ### The Cayley map -/

theorem ne_one_of_mem_disk' {t : ℂ} (ht : t ∈ disk) : t ≠ 1 := by
  rintro rfl
  simp at ht

theorem cayley_im {t : ℂ} (ht : t ≠ 1) : (cayley t).im = (1 - t.re * t.re - t.im * t.im) / normSq (1 - t) := by
  have hne : 1 - t ≠ 0 := sub_ne_zero.2 (Ne.symm ht)
  have hN : normSq (1 - t) ≠ 0 := (normSq_pos.2 hne).ne'
  have h1 : cayley t = I * ((1 + t) / (1 - t)) := by rw [cayley, mul_div_assoc]
  rw [h1, Complex.I_mul_im, Complex.div_re]
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.sub_im, Complex.one_im, Complex.add_im]
  field_simp
  ring

theorem cayley_im_pos {t : ℂ} (ht : t ∈ disk) : 0 < (cayley t).im := by
  have hne := ne_one_of_mem_disk' ht
  have h1ne : 1 - t ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hu2 : t.re * t.re + t.im * t.im < 1 := by
    have h1 : ‖t‖ < 1 := by simpa using ht
    have h2 : ‖t‖ ^ 2 < 1 := by nlinarith [norm_nonneg t]
    rwa [Complex.sq_norm, normSq_apply] at h2
  rw [cayley_im hne]
  exact div_pos (by linarith) (normSq_pos.2 h1ne)

theorem cayley_unit_real {b : ℂ} (h1 : ‖b‖ = 1) (h2 : b ≠ 1) : (cayley b).im = 0 := by
  have h3 : b.re * b.re + b.im * b.im = 1 := by
    have h4 : ‖b‖ ^ 2 = 1 := by rw [h1]; norm_num
    rwa [Complex.sq_norm, normSq_apply] at h4
  rw [cayley_im h2]
  have h5 : 1 - b.re * b.re - b.im * b.im = 0 := by linarith
  rw [h5, zero_div]

theorem cayley_hasDerivAt {t : ℂ} (ht : t ≠ 1) : HasDerivAt cayley (2 * I / (1 - t) ^ 2) t := by
  have hne : 1 - t ≠ 0 := sub_ne_zero.2 (Ne.symm ht)
  have h1 : HasDerivAt (fun t : ℂ => I * (1 + t)) I t := by
    simpa using ((hasDerivAt_id t).const_add 1).const_mul I
  have h2 : HasDerivAt (fun t : ℂ => 1 - t) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub 1
  have h3 := h1.div h2 hne
  refine h3.congr_deriv ?_
  field_simp
  ring

theorem cayley_differentiableOn : DifferentiableOn ℂ cayley disk := fun _ ht =>
  (cayley_hasDerivAt (ne_one_of_mem_disk' ht)).differentiableAt.differentiableWithinAt

theorem cayley_continuousAt {b : ℂ} (h : b ≠ 1) : ContinuousAt cayley b := (cayley_hasDerivAt h).continuousAt

theorem cayleyInv_cayley {t : ℂ} (ht : t ≠ 1) : cayleyInv (cayley t) = t := by
  have hne : 1 - t ≠ 0 := sub_ne_zero.2 (Ne.symm ht)
  have h1 : I * (1 + t) / (1 - t) - I = 2 * I * t / (1 - t) := by
    field_simp
    ring
  have h2 : I * (1 + t) / (1 - t) + I = 2 * I / (1 - t) := by
    field_simp
    ring
  rw [cayleyInv, cayley, h1, h2]
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  field_simp

theorem cayley_injOn : InjOn cayley disk := by
  intro a ha b hb hab
  have h1 := cayleyInv_cayley (ne_one_of_mem_disk' ha)
  have h2 := cayleyInv_cayley (ne_one_of_mem_disk' hb)
  rw [← h1, ← h2, hab]

theorem add_I_ne_zero {w : ℂ} (hw : 0 < w.im) : w + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem cayleyInv_mem {w : ℂ} (hw : 0 < w.im) : cayleyInv w ∈ disk := by
  have hne := add_I_ne_zero hw
  rw [mem_ball_zero_iff, cayleyInv, norm_div, div_lt_one (norm_pos_iff.2 hne)]
  refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
  rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
  simp only [Complex.sub_re, Complex.I_re, Complex.add_re, Complex.sub_im, Complex.I_im, Complex.add_im, sub_zero, add_zero]
  nlinarith

theorem cayleyInv_hasDerivAt {w : ℂ} (hw : w + I ≠ 0) : HasDerivAt cayleyInv (2 * I / (w + I) ^ 2) w := by
  have h3 := ((hasDerivAt_id w).sub_const I).div ((hasDerivAt_id w).add_const I) hw
  refine h3.congr_deriv ?_
  simp only [id]
  field_simp
  ring

theorem cayleyInv_differentiableOn : DifferentiableOn ℂ cayleyInv {w | 0 < w.im} := fun _ hw =>
  (cayleyInv_hasDerivAt (add_I_ne_zero hw)).differentiableAt.differentiableWithinAt

theorem cayleyInv_injOn : InjOn cayleyInv {w | 0 < w.im} := by
  intro a ha b hb hab
  have hA := add_I_ne_zero ha
  have hB := add_I_ne_zero hb
  have h1 : (a - I) / (a + I) = (b - I) / (b + I) := hab
  rw [div_eq_div_iff hA hB] at h1
  have h2 : 2 * I * (a - b) = 0 := by linear_combination h1
  have h3 : a - b = 0 := by
    refine (mul_eq_zero.1 h2).resolve_left (mul_ne_zero two_ne_zero I_ne_zero)
  exact sub_eq_zero.1 h3

theorem cayleyInv_near_one {e : ℝ} (he : 0 < e) :
    ∃ L : ℝ, ∀ w : ℂ, 0 < w.im → L < ‖w‖ → ‖cayleyInv w - 1‖ < e := by
  refine ⟨2 / e + 1, fun w hw hL => ?_⟩
  have hne := add_I_ne_zero hw
  have h1 : cayleyInv w - 1 = -(2 * I) / (w + I) := by
    rw [cayleyInv]
    field_simp
    ring
  have h2 : ‖w‖ - 1 ≤ ‖w + I‖ := by
    have h3 := norm_sub_norm_le w (-I)
    rwa [norm_neg, norm_I, sub_neg_eq_add] at h3
  have h4 : 2 / e < ‖w + I‖ := by linarith
  have hpos : 0 < ‖w + I‖ := norm_pos_iff.2 hne
  rw [h1, norm_div, norm_neg, norm_mul, norm_I, Complex.norm_ofNat, mul_one, div_lt_iff₀ hpos]
  rw [div_lt_iff₀ he] at h4
  linarith

/-! ### The composition, for small `lam` -/

theorem combDisc_hasDerivAt_zero {lam : ℝ} (h : 0 ≤ lam) (xs : Finset ℝ) :
    HasDerivAt (combDisc lam xs)
      (2 * I / (comb lam xs I + I) ^ 2 * ((1 + (lam : ℂ) * ∑ x ∈ xs, 1 / (I - x)) * (2 * I / (1 - 0) ^ 2))) 0 := by
  have hc0 : cayley 0 = I := by simp [cayley]
  have h1 := cayley_hasDerivAt (zero_ne_one : (0 : ℂ) ≠ 1)
  have hIim : 0 < (I : ℂ).im := by simp
  have h2 : HasDerivAt (comb lam xs) (1 + (lam : ℂ) * ∑ x ∈ xs, 1 / (I - x)) (cayley 0) := by
    rw [hc0]
    exact comb_hasDerivAt lam xs hIim
  have h3 := h2.comp (0 : ℂ) h1
  have h4 : HasDerivAt cayleyInv (2 * I / (comb lam xs I + I) ^ 2) ((comb lam xs ∘ cayley) 0) := by
    simp only [Function.comp, hc0]
    exact cayleyInv_hasDerivAt (add_I_ne_zero (comb_im_pos h xs hIim))
  exact h4.comp (0 : ℂ) h3

/-- As `lam → 0`, `φ(0) → 0` and `φ'(0) → 1`, by the explicit formula. -/
theorem combDisc_small (xs : Finset ℝ) {e : ℝ} (he : 0 < e) :
    ∃ lam : ℝ, 0 < lam ∧ ‖combDisc lam xs 0‖ < e ∧ ‖deriv (combDisc lam xs) 0 - 1‖ < e := by
  set S : ℂ := ∑ x ∈ xs, Complex.log (I - x) with hS
  set S' : ℂ := ∑ x ∈ xs, 1 / (I - x) with hS'
  have h2I : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  have hden : (I + ((0 : ℝ) : ℂ) * S + I) ≠ 0 := by
    have : I + ((0 : ℝ) : ℂ) * S + I = 2 * I := by push_cast; ring
    rw [this]
    exact h2I
  have hA : ContinuousAt (fun l : ℝ => (I + (l : ℂ) * S - I) / (I + (l : ℂ) * S + I)) 0 :=
    ContinuousAt.div (by fun_prop) (by fun_prop) hden
  have hB : ContinuousAt (fun l : ℝ => 2 * I / (I + (l : ℂ) * S + I) ^ 2 * ((1 + (l : ℂ) * S') * (2 * I / (1 - 0) ^ 2))) 0 :=
    ContinuousAt.mul (ContinuousAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 2 hden)) (by fun_prop)
  obtain ⟨d1, hd1, h1⟩ := Metric.continuousAt_iff.1 hA e he
  obtain ⟨d2, hd2, h2⟩ := Metric.continuousAt_iff.1 hB e he
  set lam : ℝ := min d1 d2 / 2 with hlam
  have hlampos : 0 < lam := by
    have := lt_min hd1 hd2
    rw [hlam]
    linarith
  have hl1 : dist lam 0 < d1 := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hlampos, hlam]
    have := min_le_left d1 d2
    linarith [lt_min hd1 hd2]
  have hl2 : dist lam 0 < d2 := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hlampos, hlam]
    have := min_le_right d1 d2
    linarith [lt_min hd1 hd2]
  have hA0 : (I + ((0 : ℝ) : ℂ) * S - I) / (I + ((0 : ℝ) : ℂ) * S + I) = 0 := by simp
  have hB0 : 2 * I / (I + ((0 : ℝ) : ℂ) * S + I) ^ 2 * ((1 + ((0 : ℝ) : ℂ) * S') * (2 * I / (1 - 0) ^ 2)) = 1 := by
    have h3 : I + ((0 : ℝ) : ℂ) * S + I = 2 * I := by push_cast; ring
    rw [h3]
    push_cast
    field_simp
    ring
  have ha := h1 hl1
  have hb := h2 hl2
  simp only [hA0, hB0] at ha hb
  rw [dist_zero_right] at ha
  rw [dist_eq_norm] at hb
  have hc0 : cayley 0 = I := by simp [cayley]
  have hv : combDisc lam xs 0 = (I + (lam : ℂ) * S - I) / (I + (lam : ℂ) * S + I) := by
    rw [combDisc, hc0, cayleyInv, comb]
  refine ⟨lam, hlampos, by rw [hv]; exact ha, ?_⟩
  rw [(combDisc_hasDerivAt_zero hlampos.le xs).deriv]
  simpa [comb, hS, hS'] using hb

end Smale.P030
