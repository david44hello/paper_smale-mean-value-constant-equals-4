/-
Smale/P030/EE.lean — the entire function `E` and the three bounds of its modulus: far left, on the cross-cut,
on the exit. `rtU` is the branch of `y^{1/M}` holomorphic across the negative axis, so paths in the closed upper half plane
need no limit at a cut.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import Smale.P030.Defs

@[expose] public section

namespace Smale.P030

open Complex Metric Set Filter Topology

/-! ### `E₀` and `E` -/

theorem E₀_hasDerivAt (M : ℕ) (ξ₀ : ℂ) : HasDerivAt (E₀ M) (Complex.exp (ξ₀ ^ M)) ξ₀ := by
  set r : ℝ := ‖ξ₀‖ + 1 with hr
  have hr0 : 0 < r := by positivity
  have hg : DifferentiableOn ℂ (fun z : ℂ => Complex.exp (z ^ M)) (ball 0 r) :=
    (by fun_prop : Differentiable ℂ fun z : ℂ => Complex.exp (z ^ M)).differentiableOn
  obtain ⟨P, hP0, hP⟩ := hg.isExactOn_ball.with_val_at 0 0
  have hsame : ∀ ξ ∈ ball (0 : ℂ) r, E₀ M ξ = P ξ := by
    intro ξ hξ
    have hξ' : ‖ξ‖ < r := by simpa using hξ
    have hseg : ∀ τ ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun τ : ℝ => P (ξ * τ)) (Complex.exp ((ξ * τ) ^ M) * ξ) τ := by
      intro τ hτ
      rw [uIcc_of_le zero_le_one] at hτ
      have hmem : ξ * (τ : ℂ) ∈ ball (0 : ℂ) r := by
        have h1 : ‖ξ * (τ : ℂ)‖ ≤ ‖ξ‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ.1]
          exact mul_le_of_le_one_right (norm_nonneg _) hτ.2
        simpa using h1.trans_lt hξ'
      have h1 : HasDerivAt (fun z : ℂ => P (ξ * z)) (Complex.exp ((ξ * τ) ^ M) * ξ) (τ : ℂ) := by
        have h2 : HasDerivAt (fun z : ℂ => ξ * z) ξ (τ : ℂ) := by
          simpa using (hasDerivAt_id (τ : ℂ)).const_mul ξ
        exact (hP _ hmem).comp (τ : ℂ) h2
      exact h1.comp_ofReal
    have hint : IntervalIntegrable (fun τ : ℝ => Complex.exp ((ξ * τ) ^ M) * ξ) MeasureTheory.volume 0 1 :=
      (by fun_prop : Continuous fun τ : ℝ => Complex.exp ((ξ * τ) ^ M) * ξ).intervalIntegrable _ _
    have h3 := intervalIntegral.integral_eq_sub_of_hasDerivAt hseg hint
    simp only [ofReal_zero, mul_zero, ofReal_one, mul_one, hP0, sub_zero] at h3
    rw [E₀, ← h3, intervalIntegral.integral_mul_const, mul_comm]
  have hmem : ξ₀ ∈ ball (0 : ℂ) r := by simp [hr]
  refine (hP ξ₀ hmem).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ball.mem_nhds hmem] with ξ hξ using hsame ξ hξ

theorem EE_zero (M : ℕ) (c : ℝ) : EE M c 0 = 0 := by
  simp [EE, E₀]

theorem EE_hasDerivAt {M : ℕ} (hM : 1 ≤ M) {c : ℝ} (hc : c ≠ 0) (ξ : ℂ) :
    HasDerivAt (EE M c) (Complex.exp (ξ ^ M) * (1 - ξ ^ M / c)) ξ := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hMc : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero m)
  have h1 : HasDerivAt (fun ξ : ℂ => ξ ^ (m + 1)) (((m + 1 : ℕ) : ℂ) * ξ ^ m) ξ := by
    simpa using hasDerivAt_pow (m + 1) ξ
  have h2 := h1.cexp
  have h3 := (hasDerivAt_id ξ).mul h2
  have h4 := ((E₀_hasDerivAt (m + 1) ξ).const_mul (1 + 1 / ((c : ℂ) * ((m + 1 : ℕ) : ℂ)))).sub
    (h3.const_mul (1 / ((c : ℂ) * ((m + 1 : ℕ) : ℂ))))
  refine h4.congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- `E(ωξ) = ωE(ξ)` for `ω^M = 1`. -/
theorem EE_rot {M : ℕ} (c : ℝ) {ω : ℂ} (hω : ω ^ M = 1) (ξ : ℂ) : EE M c (ω * ξ) = ω * EE M c ξ := by
  have h1 : (ω * ξ) ^ M = ξ ^ M := by rw [mul_pow, hω, one_mul]
  have h2 : ∀ τ : ℝ, (ω * ξ * τ) ^ M = (ξ * τ) ^ M := fun τ => by rw [mul_assoc, mul_pow, hω, one_mul]
  simp only [EE, E₀, h1, h2]
  ring

/-- `E(ξ̄) = conj E(ξ)`. -/
theorem EE_conj (M : ℕ) (c : ℝ) (ξ : ℂ) : EE M c ((starRingEnd ℂ) ξ) = (starRingEnd ℂ) (EE M c ξ) := by
  have h1 : (∫ τ in (0 : ℝ)..1, Complex.exp (((starRingEnd ℂ) ξ * τ) ^ M)) =
      (starRingEnd ℂ) (∫ τ in (0 : ℝ)..1, Complex.exp ((ξ * τ) ^ M)) := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one, ← integral_conj]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only [← Complex.exp_conj, map_pow, map_mul, Complex.conj_ofReal]
  simp only [EE, E₀, h1, map_sub, map_mul, map_add, map_one, map_div₀, map_pow, ← Complex.exp_conj, Complex.conj_ofReal,
    map_natCast]

/-- `|E(ξ)|` depends only on `ξ^M`. -/
theorem norm_EE_eq_of_pow_eq {M : ℕ} (hM : M ≠ 0) (c : ℝ) {ξ₁ ξ₂ : ℂ} (h : ξ₁ ^ M = ξ₂ ^ M) :
    ‖EE M c ξ₁‖ = ‖EE M c ξ₂‖ := by
  by_cases h2 : ξ₂ = 0
  · have h1 : ξ₁ = 0 := by
      rw [h2, zero_pow hM] at h
      exact pow_eq_zero_iff hM |>.1 h
    rw [h1, h2]
  · have hω : (ξ₁ / ξ₂) ^ M = 1 := by rw [div_pow, h, div_self (pow_ne_zero M h2)]
    have hn : ‖ξ₁ / ξ₂‖ = 1 := by
      have h3 : ‖ξ₁ / ξ₂‖ ^ M = 1 := by rw [← norm_pow, hω, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hM).1 h3
    have h4 : ξ₁ = ξ₁ / ξ₂ * ξ₂ := by field_simp
    rw [h4, EE_rot c hω, norm_mul, hn, one_mul]

/-! ### The branch `rtU` -/

/-- `y^{1/M}`, with argument `arg y / M`, holomorphic on a neighbourhood of the closed upper half plane minus `0`. -/
noncomputable def rtU (M : ℕ) (y : ℂ) : ℂ := Complex.exp ((Complex.log (-I * y) + I * ((Real.pi : ℂ) / 2)) / M)

/-- `E(y^{1/M})`. -/
noncomputable def psi (M : ℕ) (c : ℝ) (y : ℂ) : ℂ := EE M c (rtU M y)

/-- `e^{iπ/M}`. -/
noncomputable def omega₀ (M : ℕ) : ℂ := Complex.exp (I * (Real.pi : ℂ) / M)

theorem neg_I_mul_mem_slitPlane {y : ℂ} (h0 : 0 ≤ y.im) (hne : y ≠ 0) : -I * y ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases h0.lt_or_eq with h | h
  · left
    simpa using h
  · right
    have hre : y.re ≠ 0 := fun hr => hne (Complex.ext hr h.symm)
    simpa using hre

theorem exp_I_pi_div_two : Complex.exp (I * ((Real.pi : ℂ) / 2)) = I := by
  rw [mul_comm, Complex.exp_mul_I, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  simp

theorem rtU_pow {M : ℕ} (hM : M ≠ 0) {y : ℂ} (hne : y ≠ 0) : rtU M y ^ M = y := by
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hne' : -I * y ≠ 0 := mul_ne_zero (neg_ne_zero.2 I_ne_zero) hne
  rw [rtU, ← Complex.exp_nat_mul, mul_div_cancel₀ _ hMc, Complex.exp_add, Complex.exp_log hne', exp_I_pi_div_two]
  linear_combination (-y) * I_sq

theorem rtU_norm_pow {M : ℕ} (hM : M ≠ 0) {y : ℂ} (hne : y ≠ 0) : ‖rtU M y‖ ^ M = ‖y‖ := by
  rw [← norm_pow, rtU_pow hM hne]

theorem rtU_ne_zero (M : ℕ) (y : ℂ) : rtU M y ≠ 0 := Complex.exp_ne_zero _

theorem rtU_hasDerivAt {M : ℕ} (hM : M ≠ 0) {y : ℂ} (h0 : 0 ≤ y.im) (hne : y ≠ 0) :
    HasDerivAt (rtU M) (rtU M y / (M * y)) y := by
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  have h1 : HasDerivAt (fun y : ℂ => -I * y) (-I) y := by simpa using (hasDerivAt_id y).const_mul (-I)
  have h2 := h1.clog (neg_I_mul_mem_slitPlane h0 hne)
  have h3 := ((h2.add_const (I * ((Real.pi : ℂ) / 2))).div_const (M : ℂ)).cexp
  refine h3.congr_deriv ?_
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  rw [rtU]
  field_simp

theorem rtU_norm_le_self {M : ℕ} (hM : M ≠ 0) {y : ℂ} (hne : y ≠ 0) (h1 : 1 ≤ ‖y‖) : ‖rtU M y‖ ≤ ‖y‖ := by
  have hp := rtU_norm_pow hM hne
  have hr1 : 1 ≤ ‖rtU M y‖ := by
    by_contra hlt
    have : ‖rtU M y‖ ^ M < 1 := pow_lt_one₀ (norm_nonneg _) (not_le.1 hlt) hM
    linarith
  rw [← hp]
  exact le_self_pow₀ hr1 hM

theorem one_le_rtU_norm {M : ℕ} (hM : M ≠ 0) {y : ℂ} (hne : y ≠ 0) (h1 : 1 ≤ ‖y‖) : 1 ≤ ‖rtU M y‖ := by
  by_contra hlt
  have h2 : ‖rtU M y‖ ^ M < 1 := pow_lt_one₀ (norm_nonneg _) (not_le.1 hlt) hM
  rw [rtU_norm_pow hM hne] at h2
  linarith

theorem rtU_norm_mono {M : ℕ} (hM : M ≠ 0) {u y : ℂ} (hu : u ≠ 0) (hy : y ≠ 0) (h : ‖u‖ ≤ ‖y‖) :
    ‖rtU M u‖ ≤ ‖rtU M y‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) hM).1 ?_
  rwa [rtU_norm_pow hM hu, rtU_norm_pow hM hy]

theorem psi_hasDerivAt {M : ℕ} (hM : 1 ≤ M) {c : ℝ} (hc : c ≠ 0) {y : ℂ} (h0 : 0 ≤ y.im) (hne : y ≠ 0) :
    HasDerivAt (psi M c) (Complex.exp y * (1 - y / c) * (rtU M y / (M * y))) y := by
  have hM0 : M ≠ 0 := by omega
  have h1 := (EE_hasDerivAt hM hc (rtU M y)).comp y (rtU_hasDerivAt hM0 h0 hne)
  rwa [rtU_pow hM0 hne] at h1

/-- Reduction to the closed upper half plane. -/
theorem norm_EE_eq_psi {M : ℕ} (hM : M ≠ 0) (c : ℝ) {ξ : ℂ} (hne : ξ ^ M ≠ 0) :
    ‖EE M c ξ‖ = ‖psi M c ⟨(ξ ^ M).re, |(ξ ^ M).im|⟩‖ := by
  set y := ξ ^ M with hy
  rcases le_or_gt 0 y.im with h | h
  · have heq : (⟨y.re, |y.im|⟩ : ℂ) = y := Complex.ext rfl (by simp [abs_of_nonneg h])
    rw [heq, psi]
    exact norm_EE_eq_of_pow_eq hM c (by rw [rtU_pow hM hne])
  · have heq : (⟨y.re, |y.im|⟩ : ℂ) = (starRingEnd ℂ) y := Complex.ext (by simp) (by simp [abs_of_neg h])
    have hne' : (starRingEnd ℂ) y ≠ 0 := (map_ne_zero _).2 hne
    rw [heq, psi]
    have h1 : ‖EE M c ((starRingEnd ℂ) ξ)‖ = ‖EE M c ξ‖ := by rw [EE_conj, Complex.norm_conj]
    rw [← h1]
    refine norm_EE_eq_of_pow_eq hM c ?_
    rw [rtU_pow hM hne', hy, map_pow]

/-! ### The negative ray -/

theorem omega₀_pow {M : ℕ} (hM : M ≠ 0) : omega₀ M ^ M = -1 := by
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  rw [omega₀, ← Complex.exp_nat_mul, mul_div_cancel₀ _ hMc, mul_comm, Complex.exp_pi_mul_I]

theorem omega₀_norm {M : ℕ} (hM : M ≠ 0) : ‖omega₀ M‖ = 1 := by
  have h3 : ‖omega₀ M‖ ^ M = 1 := by rw [← norm_pow, omega₀_pow hM, norm_neg, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hM).1 h3

/-- On the negative axis, `rtU` is on the ray of `e^{iπ/M}`. -/
theorem rtU_neg {M : ℕ} {s : ℝ} (hs : 1 ≤ s) :
    rtU M (-(s : ℂ)) = (Real.exp (Real.log s / M) : ℂ) * omega₀ M := by
  have hs0 : 0 < s := by linarith
  have hlog : Complex.log (-I * (-(s : ℂ))) = (Real.log s : ℂ) + I * ((Real.pi : ℂ) / 2) := by
    have h1 : -I * (-(s : ℂ)) = (s : ℂ) * I := by ring
    rw [h1, Complex.log_ofReal_mul hs0 I_ne_zero, Complex.log_I]
    ring
  rw [rtU, hlog, omega₀, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `∫_0^1 exp(-s^M) ds ≥ M/(M+1)`. -/
theorem integral_exp_neg_pow_ge (M : ℕ) : (M : ℝ) / (M + 1) ≤ ∫ s in (0 : ℝ)..1, Real.exp (-s ^ M) := by
  have h1 : ∫ s in (0 : ℝ)..1, (1 - s ^ M) = (M : ℝ) / (M + 1) := by
    rw [intervalIntegral.integral_sub (by simp) (by simp [intervalIntegral.intervalIntegrable_pow])]
    simp only [intervalIntegral.integral_const, integral_pow]
    have hM : ((M : ℝ) + 1) ≠ 0 := by positivity
    simp
    field_simp
    ring
  rw [← h1]
  refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ fun s _ => Real.one_sub_le_exp_neg _
  · exact (by fun_prop : Continuous fun s : ℝ => 1 - s ^ M).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun s : ℝ => Real.exp (-s ^ M)).intervalIntegrable _ _

/-- On the ray: `e^{-iπ/M} E(r e^{iπ/M}) ≥ M/(M+1)` for `r ≥ 1`. -/
theorem re_EE_ray {M : ℕ} (hM : 1 ≤ M) {c r : ℝ} (hc : 0 < c) (hr : 1 ≤ r) :
    (M : ℝ) / (M + 1) ≤ ((omega₀ M)⁻¹ * EE M c ((r : ℂ) * omega₀ M)).re := by
  have hM0 : M ≠ 0 := by omega
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM0
  have hr0 : 0 < r := by linarith
  have hω0 : omega₀ M ≠ 0 := Complex.exp_ne_zero _
  set f : ℝ → ℝ := fun s => Real.exp (-s ^ M) with hf
  set J : ℝ := ∫ τ in (0 : ℝ)..1, f (r * τ) with hJ
  have hpow : ∀ τ : ℝ, ((r : ℂ) * omega₀ M * τ) ^ M = ((-(r * τ) ^ M : ℝ) : ℂ) := fun τ => by
    have h1 : (r : ℂ) * omega₀ M * τ = ((r * τ : ℝ) : ℂ) * omega₀ M := by push_cast; ring
    rw [h1, mul_pow, omega₀_pow hM0]
    push_cast
    ring
  have hint : (∫ τ in (0 : ℝ)..1, Complex.exp (((r : ℂ) * omega₀ M * τ) ^ M)) = (J : ℂ) := by
    simp_rw [hpow, ← Complex.ofReal_exp]
    rw [hJ, intervalIntegral.integral_ofReal]
  have hpow1 : ((r : ℂ) * omega₀ M) ^ M = ((-r ^ M : ℝ) : ℂ) := by
    rw [mul_pow, omega₀_pow hM0]
    push_cast
    ring
  set k : ℝ := 1 / (c * M) with hk
  have hkpos : 0 < k := by
    have : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    positivity
  have hkc : (1 : ℂ) / ((c : ℂ) * M) = (k : ℂ) := by rw [hk]; push_cast; ring
  have heq : (omega₀ M)⁻¹ * EE M c ((r : ℂ) * omega₀ M) = (((1 + k) * (r * J) - k * (r * Real.exp (-r ^ M)) : ℝ) : ℂ) := by
    rw [EE, E₀, hint, hpow1, hkc, ← Complex.ofReal_exp]
    push_cast
    field_simp
  rw [heq, Complex.ofReal_re]
  -- `J ≥ exp(-r^M)`
  have hJ1 : Real.exp (-r ^ M) ≤ J := by
    have h1 : ∫ _τ in (0 : ℝ)..1, Real.exp (-r ^ M) = Real.exp (-r ^ M) := by simp
    rw [← h1]
    refine intervalIntegral.integral_mono_on zero_le_one (by simp) ?_ fun τ hτ => ?_
    · exact (by fun_prop : Continuous fun τ : ℝ => f (r * τ)).intervalIntegrable _ _
    · refine Real.exp_le_exp.2 (neg_le_neg ?_)
      exact pow_le_pow_left₀ (mul_nonneg hr0.le hτ.1) (mul_le_of_le_one_right hr0.le hτ.2) M
  -- `r J = ∫_0^r f ≥ ∫_0^1 f`
  have hJ2 : (M : ℝ) / (M + 1) ≤ r * J := by
    have h1 : r * J = ∫ s in (0 : ℝ)..r, f s := by
      simp [hJ]
    have hfint : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b := fun a b =>
      (by fun_prop : Continuous f).intervalIntegrable a b
    have h2 : ∫ s in (0 : ℝ)..r, f s = (∫ s in (0 : ℝ)..1, f s) + ∫ s in (1 : ℝ)..r, f s :=
      (intervalIntegral.integral_add_adjacent_intervals (hfint 0 1) (hfint 1 r)).symm
    have h3 : 0 ≤ ∫ s in (1 : ℝ)..r, f s :=
      intervalIntegral.integral_nonneg hr fun s _ => (Real.exp_pos _).le
    rw [h1, h2]
    linarith [integral_exp_neg_pow_ge M]
  have hJ3 : r * Real.exp (-r ^ M) ≤ r * J := mul_le_mul_of_nonneg_left hJ1 hr0.le
  nlinarith

/-! ### Far left -/

/-- `dE/dy`. -/
noncomputable def dPsi (M : ℕ) (c : ℝ) (y : ℂ) : ℂ := Complex.exp y * (1 - y / c) * (rtU M y / (M * y))

/-- `|dE/dy| ≤ (1/M) e^x (1 + (|x| + τ)/c)` on a vertical segment at `x ≤ -1`. -/
theorem norm_dPsi_left {M : ℕ} (hM : 1 ≤ M) {c x τ t : ℝ} (hc : 0 < c) (hx : x ≤ -1) (ht0 : 0 ≤ t) (ht : t ≤ τ) :
    ‖dPsi M c ((x : ℂ) + t * I)‖ ≤ 1 / M * Real.exp x * (1 + (-x + τ) / c) := by
  have hM0 : M ≠ 0 := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  set u : ℂ := (x : ℂ) + t * I with hu
  have hure : u.re = x := by simp [hu]
  have huim : u.im = t := by simp [hu]
  have hu1 : 1 ≤ ‖u‖ := by
    have h1 := Complex.abs_re_le_norm u
    rw [hure, abs_of_neg (by linarith)] at h1
    linarith
  have hune : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu1
    linarith
  have hu2 : ‖u‖ ≤ -x + τ := by
    have h1 := Complex.norm_le_abs_re_add_abs_im u
    rw [hure, huim, abs_of_neg (by linarith), abs_of_nonneg ht0] at h1
    linarith
  have h1 : ‖Complex.exp u‖ = Real.exp x := by rw [Complex.norm_exp, hure]
  have h2 : ‖1 - u / c‖ ≤ 1 + (-x + τ) / c := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_div, Complex.norm_real, Real.norm_of_nonneg hc.le]
    gcongr
  have h3 : ‖rtU M u / (M * u)‖ ≤ 1 / M := by
    rw [norm_div, norm_mul, Complex.norm_natCast]
    have hupos : 0 < ‖u‖ := by linarith
    rw [div_le_div_iff₀ (by positivity) hMpos]
    have := rtU_norm_le_self hM0 hune hu1
    nlinarith
  have hpos : 0 ≤ 1 + (-x + τ) / c := by
    have : 0 ≤ -x + τ := by linarith
    positivity
  rw [dPsi, norm_mul, norm_mul, h1]
  calc Real.exp x * ‖1 - u / c‖ * ‖rtU M u / (M * u)‖ ≤ Real.exp x * (1 + (-x + τ) / c) * (1 / M) := by
        gcongr
    _ = 1 / M * Real.exp x * (1 + (-x + τ) / c) := by ring

/-- `|E(x + iτ) - E(x)|` on a vertical segment at `x ≤ -1`. -/
theorem psi_vertical {M : ℕ} (hM : 1 ≤ M) {c x τ : ℝ} (hc : 0 < c) (hx : x ≤ -1) (hτ : 0 ≤ τ) :
    ‖psi M c ((x : ℂ) + τ * I) - psi M c x‖ ≤ 1 / M * Real.exp x * (1 + (-x + τ) / c) * τ := by
  have hf : ∀ t ∈ Icc (0 : ℝ) τ, HasDerivWithinAt (fun t : ℝ => psi M c ((x : ℂ) + t * I))
      (dPsi M c ((x : ℂ) + t * I) * I) (Icc 0 τ) t := by
    intro t ht
    have him : 0 ≤ ((x : ℂ) + t * I).im := by simpa using ht.1
    have hne : (x : ℂ) + t * I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have h1 : HasDerivAt (fun z : ℂ => (x : ℂ) + z * I) I (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const I).const_add (x : ℂ)
    have h2 := (psi_hasDerivAt hM hc.ne' him hne).comp (t : ℂ) h1
    exact (h2.comp_ofReal).hasDerivWithinAt
  have hbound : ∀ t ∈ Icc (0 : ℝ) τ, ‖dPsi M c ((x : ℂ) + t * I) * I‖ ≤ 1 / M * Real.exp x * (1 + (-x + τ) / c) := by
    intro t ht
    rw [norm_mul, norm_I, mul_one]
    exact norm_dPsi_left hM hc hx ht.1 ht.2
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hf hbound (convex_Icc 0 τ)
    (left_mem_Icc.2 hτ) (right_mem_Icc.2 hτ)
  simpa [abs_of_nonneg hτ] using key

/-- `Re(A) ≥ Re(B) - |A - B|`, after multiplying by a unit. -/
theorem re_mul_ge {ω A B : ℂ} (hω : ‖ω‖ = 1) : (ω * B).re - ‖A - B‖ ≤ (ω * A).re := by
  have h1 : (ω * A).re = (ω * B).re + (ω * (A - B)).re := by
    rw [← Complex.add_re]
    ring_nf
  have h2 : |(ω * (A - B)).re| ≤ ‖A - B‖ := by
    have := Complex.abs_re_le_norm (ω * (A - B))
    rwa [norm_mul, hω, one_mul] at this
  have h3 := (abs_le.1 h2).1
  linarith

/-- Far left: `Re(e^{-iπ/M} E(x + iτ)) ≥ M/(M+1)` up to the vertical error. -/
theorem re_psi_left {M : ℕ} (hM : 1 ≤ M) {c x τ : ℝ} (hc : 0 < c) (hx : x ≤ -1) (hτ : 0 ≤ τ) :
    (M : ℝ) / (M + 1) - 1 / M * Real.exp x * (1 + (-x + τ) / c) * τ ≤ ((omega₀ M)⁻¹ * psi M c ((x : ℂ) + τ * I)).re := by
  have hM0 : M ≠ 0 := by omega
  set s : ℝ := -x with hs
  have hs1 : 1 ≤ s := by rw [hs]; linarith
  have hxs : (x : ℂ) = -(s : ℂ) := by rw [hs]; push_cast; ring
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hr1 : 1 ≤ Real.exp (Real.log s / M) := by
    refine Real.one_le_exp (div_nonneg (Real.log_nonneg hs1) hMpos.le)
  have hray := re_EE_ray hM hc hr1
  have hpsi : psi M c x = EE M c ((Real.exp (Real.log s / M) : ℂ) * omega₀ M) := by
    rw [psi, hxs, rtU_neg hs1]
  have hunit : ‖(omega₀ M)⁻¹‖ = 1 := by rw [norm_inv, omega₀_norm hM0, inv_one]
  have h1 := re_mul_ge (ω := (omega₀ M)⁻¹) (A := psi M c ((x : ℂ) + τ * I)) (B := psi M c x) hunit
  have h2 := psi_vertical hM hc hx hτ
  rw [hpsi] at h1 h2
  linarith

/-- **Far left.** -/
theorem norm_EE_left {M : ℕ} (hM : 8 ≤ M) {c C : ℝ} (hc : 1 ≤ c) (hC : 1 ≤ C) (ξ : ℂ) (h1 : (ξ ^ M).re ≤ -C)
    (h2 : |(ξ ^ M).im| ≤ C) :
    (M : ℝ) / (M + 1) - C / M * Real.exp (-C) * (1 + 2 * C / c) ≤ ‖EE M c ξ‖ := by
  have hM1 : 1 ≤ M := by omega
  have hM0 : M ≠ 0 := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hcpos : 0 < c := by linarith
  set x : ℝ := (ξ ^ M).re with hx
  set τ : ℝ := |(ξ ^ M).im| with hτ
  have hτ0 : 0 ≤ τ := abs_nonneg _
  have hne : ξ ^ M ≠ 0 := by
    intro h
    rw [hx, h] at h1
    simp at h1
    linarith
  have hy : (⟨x, τ⟩ : ℂ) = (x : ℂ) + τ * I := by
    apply Complex.ext <;> simp
  have hnorm := norm_EE_eq_psi hM0 c hne
  rw [← hx, ← hτ, hy] at hnorm
  have hx1 : x ≤ -1 := by linarith
  have hre := re_psi_left hM1 hcpos hx1 hτ0
  have hle : ((omega₀ M)⁻¹ * psi M c ((x : ℂ) + τ * I)).re ≤ ‖psi M c ((x : ℂ) + τ * I)‖ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, norm_inv, omega₀_norm hM0, inv_one, one_mul]
  -- the error at `x` against the error at `-C`
  set t : ℝ := -x - C with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have hexp : Real.exp x * (1 + t) ≤ Real.exp (-C) := by
    have h3 : x = -C - t := by rw [ht]; ring
    have h4 : Real.exp x = Real.exp (-C) * Real.exp (-t) := by rw [h3, ← Real.exp_add]; ring_nf
    have h5 : Real.exp (-t) * (1 + t) ≤ 1 := by
      have h6 := Real.add_one_le_exp t
      have h7 : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
      have h8 : Real.exp (-t) * (t + 1) ≤ Real.exp (-t) * Real.exp t :=
        mul_le_mul_of_nonneg_left h6 (Real.exp_pos _).le
      rw [h7] at h8
      linarith
    rw [h4, mul_assoc]
    exact mul_le_of_le_one_right (Real.exp_pos _).le h5
  have hA : 0 ≤ 1 + 2 * C / c := by positivity
  have hfac : 1 + (-x + τ) / c ≤ (1 + 2 * C / c) * (1 + t) := by
    have h3 : -x + τ ≤ 2 * C + t := by rw [ht]; linarith
    have h4 : (-x + τ) / c ≤ (2 * C + t) / c := div_le_div_of_nonneg_right h3 hcpos.le
    have h5 : t / c ≤ t := div_le_self ht0 hc
    have h6 : (2 * C + t) / c = 2 * C / c + t / c := add_div _ _ _
    have h7 : 0 ≤ 2 * C / c * t := by positivity
    nlinarith
  have herr : 1 / M * Real.exp x * (1 + (-x + τ) / c) * τ ≤ C / M * Real.exp (-C) * (1 + 2 * C / c) := by
    have h3 : Real.exp x * (1 + (-x + τ) / c) ≤ Real.exp (-C) * (1 + 2 * C / c) := by
      calc Real.exp x * (1 + (-x + τ) / c) ≤ Real.exp x * ((1 + 2 * C / c) * (1 + t)) :=
            mul_le_mul_of_nonneg_left hfac (Real.exp_pos _).le
        _ = (Real.exp x * (1 + t)) * (1 + 2 * C / c) := by ring
        _ ≤ Real.exp (-C) * (1 + 2 * C / c) := mul_le_mul_of_nonneg_right hexp hA
    have h4 : 0 ≤ Real.exp x * (1 + (-x + τ) / c) := by
      have : 0 ≤ -x + τ := by linarith
      positivity
    calc 1 / M * Real.exp x * (1 + (-x + τ) / c) * τ = 1 / M * (Real.exp x * (1 + (-x + τ) / c)) * τ := by ring
      _ ≤ 1 / M * (Real.exp (-C) * (1 + 2 * C / c)) * C := by gcongr
      _ = C / M * Real.exp (-C) * (1 + 2 * C / c) := by ring
  rw [hnorm]
  linarith

/-! ### The cross-cut -/

/-- On a line at height `τ ∈ [C - 1/2, C]`, `C` an odd multiple of `π`: `dE/dy` points within `π/2` of `e^{iπ/M}`. -/
theorem re_dPsi_cross {M n : ℕ} (hM : 8 ≤ M) {c C τ : ℝ} (hc : 0 < c) (hC : C = (2 * n + 1) * Real.pi)
    (hcC : 10 * c ≤ C - 1 / 2) (h1 : C - 1 / 2 ≤ τ) (h2 : τ ≤ C) (s : ℝ) :
    0 ≤ ((omega₀ M)⁻¹ * dPsi M c ((s : ℂ) + τ * I)).re := by
  have hM0 : M ≠ 0 := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM0
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hτpos : 0 < τ := by linarith
  set y : ℂ := (s : ℂ) + τ * I with hy
  have hyre : y.re = s := by simp [hy]
  have hyim : y.im = τ := by simp [hy]
  have hyne : y ≠ 0 := by
    intro h
    rw [h] at hyim
    simp at hyim
    linarith
  set τ' : ℝ := C - τ with hτ'
  have hτ'0 : 0 ≤ τ' := by rw [hτ']; linarith
  have hτ'1 : τ' ≤ 1 / 2 := by rw [hτ']; linarith
  -- the argument of `-I * y`
  set L : ℂ := Complex.log (-I * y) with hL
  have hLim : |L.im| ≤ Real.pi / 2 := by
    rw [hL, Complex.log_im]
    refine Complex.abs_arg_le_pi_div_two_iff.2 ?_
    simp [hyim, hτpos.le]
  set β : ℝ := (L.im - Real.pi / 2) / M with hβ
  set ρ : ℝ := Real.exp (L.re / M) with hρ
  have hρpos : 0 < ρ := Real.exp_pos _
  have hβ0 : β ≤ 0 := by
    rw [hβ]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [(abs_le.1 hLim).2]) hMpos.le
  have hβ1 : -(Real.pi / M) ≤ β := by
    rw [hβ, neg_le_iff_add_nonneg, ← add_div]
    apply div_nonneg _ hMpos.le
    linarith [(abs_le.1 hLim).1]
  -- the identity
  have hrt : (omega₀ M)⁻¹ * rtU M y = (ρ : ℂ) * Complex.exp (I * β) := by
    have hdecomp : L = (L.re : ℂ) + (L.im : ℂ) * I := (Complex.re_add_im L).symm
    rw [omega₀, rtU, ← hL, ← Complex.exp_neg, ← Complex.exp_add, hρ, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    rw [hβ]
    conv_lhs => rw [hdecomp]
    push_cast
    field_simp
    ring
  have hexpy : Complex.exp y = (Real.exp s : ℂ) * -Complex.exp (I * ((-τ' : ℝ) : ℂ)) := by
    have h3 : y = (s : ℂ) + I * (C : ℂ) + I * ((-τ' : ℝ) : ℂ) := by
      rw [hy, hτ']
      push_cast
      ring
    have h4 : Complex.exp (I * (C : ℂ)) = -1 := by
      rw [hC]
      push_cast
      have h5 : I * ((2 * (n : ℂ) + 1) * (Real.pi : ℂ)) = (n : ℂ) * (2 * (Real.pi : ℂ) * I) + (Real.pi : ℂ) * I := by ring
      rw [h5, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_nat_mul_two_pi_mul_I]
      simp
    rw [h3, Complex.exp_add, Complex.exp_add, h4, Complex.ofReal_exp]
    ring
  have hfrac : (1 - y / c) * (1 / y) = -(1 / (c : ℂ)) * (1 - c / y) := by
    field_simp
    ring
  set α : ℝ := β + -τ' with hα
  have hexpα : Complex.exp (I * (α : ℂ)) = Complex.exp (I * (β : ℂ)) * Complex.exp (I * ((-τ' : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, hα]
    push_cast
    ring_nf
  set R₀ : ℝ := Real.exp s * ρ / (c * M) with hR₀
  have hR₀pos : 0 < R₀ := by positivity
  have hid : (omega₀ M)⁻¹ * dPsi M c y = (R₀ : ℂ) * (Complex.exp (I * (α : ℂ)) * (1 - c / y)) := by
    have h3 : (omega₀ M)⁻¹ * dPsi M c y =
        Complex.exp y * ((1 - y / c) * (1 / y)) * ((omega₀ M)⁻¹ * rtU M y) / M := by
      rw [dPsi]
      field_simp
    rw [h3, hexpy, hfrac, hrt, hexpα, hR₀]
    push_cast
    field_simp
  rw [hid, Complex.re_ofReal_mul]
  refine mul_nonneg hR₀pos.le ?_
  -- `cos α - |c/y| ≥ 0`
  have hπ : Real.pi / M ≤ 2 / 5 := by
    have h3 : (M : ℝ) ≥ 8 := by exact_mod_cast hM
    rw [div_le_iff₀ hMpos]
    nlinarith [Real.pi_lt_d2]
  have hαabs : |α| ≤ 9 / 10 := by
    rw [hα, abs_le]
    constructor <;> linarith
  have hcos : 1 / 2 ≤ Real.cos α := by
    have h3 := Real.one_sub_sq_div_two_le_cos (x := α)
    have h4 : α ^ 2 ≤ (9 / 10) ^ 2 := sq_le_sq' (abs_le.1 hαabs).1 (abs_le.1 hαabs).2
    linarith
  have hv : ‖(c : ℂ) / y‖ ≤ 1 / 10 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hc.le]
    have hyn : τ ≤ ‖y‖ := by
      have := Complex.abs_im_le_norm y
      rwa [hyim, abs_of_pos hτpos] at this
    have hypos : 0 < ‖y‖ := by linarith
    rw [div_le_iff₀ hypos]
    linarith
  have hre : (Complex.exp (I * (α : ℂ)) * (1 - c / y)).re =
      Real.cos α - (Complex.exp (I * (α : ℂ)) * (c / y)).re := by
    rw [mul_sub, mul_one, Complex.sub_re, mul_comm I, Complex.exp_ofReal_mul_I_re]
  have hre2 : (Complex.exp (I * (α : ℂ)) * (c / y)).re ≤ 1 / 10 := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, mul_comm I, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact hv
  rw [hre]
  linarith

/-- The vertical error tends to `0` as `x → -∞`. -/
theorem tendsto_left_err (M : ℕ) (c τ : ℝ) :
    Tendsto (fun u : ℝ => 1 / (M : ℝ) * Real.exp (-u) * (1 + (u + τ) / c) * τ) atTop (𝓝 0) := by
  have h1 := Real.tendsto_exp_neg_atTop_nhds_zero
  have h2 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h3 : Tendsto (fun u : ℝ => 1 / (M : ℝ) * τ * ((1 + τ / c) * Real.exp (-u) + 1 / c * (u ^ 1 * Real.exp (-u))))
      atTop (𝓝 (1 / (M : ℝ) * τ * ((1 + τ / c) * 0 + 1 / c * 0))) :=
    (((h1.const_mul _).add (h2.const_mul _)).const_mul _)
  simp only [mul_zero, add_zero] at h3
  refine h3.congr fun u => ?_
  ring

/-- **Cross-cut.** -/
theorem norm_EE_cross {M n : ℕ} (hM : 8 ≤ M) {c C : ℝ} (hc : 0 < c) (hC : C = (2 * n + 1) * Real.pi)
    (hcC : 10 * c ≤ C - 1 / 2) (ξ : ℂ) (h1 : C - 1 / 2 ≤ |(ξ ^ M).im|) (h2 : |(ξ ^ M).im| ≤ C) :
    (M : ℝ) / (M + 1) ≤ ‖EE M c ξ‖ := by
  have hM1 : 1 ≤ M := by omega
  have hM0 : M ≠ 0 := by omega
  set x : ℝ := (ξ ^ M).re with hx
  set τ : ℝ := |(ξ ^ M).im| with hτ
  have hτpos : 0 < τ := by linarith
  have hne : ξ ^ M ≠ 0 := by
    intro h
    rw [hτ, h] at hτpos
    simp at hτpos
  have hy : (⟨x, τ⟩ : ℂ) = (x : ℂ) + τ * I := by
    apply Complex.ext <;> simp
  have hnorm := norm_EE_eq_psi hM0 c hne
  rw [← hx, ← hτ, hy] at hnorm
  rw [hnorm]
  -- monotone along the line
  set g : ℝ → ℝ := fun s => ((omega₀ M)⁻¹ * psi M c ((s : ℂ) + τ * I)).re with hg
  have hline : ∀ s : ℝ, (s : ℂ) + τ * I ≠ 0 ∧ 0 ≤ ((s : ℂ) + τ * I).im := fun s => by
    refine ⟨fun h => ?_, by simpa using hτpos.le⟩
    have := congrArg Complex.im h
    simp at this
    linarith
  have hgd : ∀ s : ℝ, HasDerivAt g ((omega₀ M)⁻¹ * dPsi M c ((s : ℂ) + τ * I)).re s := by
    intro s
    have h4 : HasDerivAt (fun z : ℂ => psi M c (z + (τ : ℂ) * I)) (dPsi M c ((s : ℂ) + τ * I)) (s : ℂ) :=
      HasDerivAt.comp_add_const (s : ℂ) ((τ : ℂ) * I) (psi_hasDerivAt hM1 hc.ne' (hline s).2 (hline s).1)
    have h5 := (h4.comp_ofReal).const_mul (omega₀ M)⁻¹
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s h5
  have hmono : Monotone g := by
    refine monotone_of_deriv_nonneg (fun s => (hgd s).differentiableAt) fun s => ?_
    rw [(hgd s).deriv]
    exact re_dPsi_cross hM hc hC hcC h1 h2 s
  -- let the start of the line go to the far left
  have hlim := (tendsto_left_err M c τ).const_sub ((M : ℝ) / (M + 1))
  rw [sub_zero] at hlim
  have hge : (M : ℝ) / (M + 1) ≤ g x := by
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (max 1 (-x))] with u hu
    have hu1 : 1 ≤ u := (le_max_left _ _).trans hu
    have hu2 : -x ≤ u := (le_max_right _ _).trans hu
    have h3 := re_psi_left hM1 hc (x := -u) (τ := τ) (by linarith) hτpos.le
    have h4 : g (-u) ≤ g x := hmono (by linarith)
    have h5 : g (-u) = ((omega₀ M)⁻¹ * psi M c (((-u : ℝ) : ℂ) + τ * I)).re := rfl
    simp only [neg_neg] at h3
    rw [← h5] at h3
    linarith
  refine hge.trans ?_
  refine (Complex.re_le_norm _).trans ?_
  rw [norm_mul, norm_inv, omega₀_norm hM0, inv_one, one_mul]

/-! ### The exit -/

/-- `h(u) = u^{1/M - 1} (1 - u/c)`. -/
noncomputable def hhf (M : ℕ) (c : ℝ) (u : ℂ) : ℂ := rtU M u / u * (1 - u / c)

/-- `E - (1/M) e^u h(u)`: the rest after one integration by parts. -/
noncomputable def Qf (M : ℕ) (c : ℝ) (u : ℂ) : ℂ := psi M c u - 1 / (M : ℂ) * (Complex.exp u * hhf M c u)

/-- `h'`. -/
noncomputable def Dfn (M : ℕ) (c : ℝ) (u : ℂ) : ℂ :=
  rtU M u / u ^ 2 * (1 / (M : ℂ) - 1) * (1 - u / c) - rtU M u / (u * c)

theorem Qf_hasDerivAt {M : ℕ} (hM : 1 ≤ M) {c : ℝ} (hc : c ≠ 0) {u : ℂ} (h0 : 0 ≤ u.im) (hne : u ≠ 0) :
    HasDerivAt (Qf M c) (-(1 / (M : ℂ)) * (Complex.exp u * Dfn M c u)) u := by
  have hM0 : M ≠ 0 := by omega
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM0
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hr := rtU_hasDerivAt hM0 h0 hne
  have h1 := hr.div (hasDerivAt_id u) hne
  have h2 : HasDerivAt (fun u : ℂ => 1 - u / c) (-(1 / (c : ℂ))) u := by
    simpa using ((hasDerivAt_id u).div_const (c : ℂ)).const_sub 1
  have h3 := h1.mul h2
  have h4 := (Complex.hasDerivAt_exp u).mul h3
  have h5 := (psi_hasDerivAt hM hc h0 hne).sub (h4.const_mul (1 / (M : ℂ)))
  refine h5.congr_deriv ?_
  simp only [id, Dfn, Pi.mul_apply, Pi.div_apply]
  field_simp
  ring

theorem norm_Dfn_le {M : ℕ} (hM : 1 ≤ M) {c : ℝ} (hc : 0 < c) {u : ℂ} (hne : u ≠ 0) :
    ‖Dfn M c u‖ ≤ ‖rtU M u‖ / ‖u‖ * (1 / ‖u‖ + 2 / c) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hupos : 0 < ‖u‖ := norm_pos_iff.2 hne
  have h1 : ‖1 / (M : ℂ) - 1‖ ≤ 1 := by
    have h2 : (1 / (M : ℂ) - 1) = ((1 / (M : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [h2, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have h3 : 1 / (M : ℝ) ≤ 1 := (div_le_one hMpos).2 hM1
    have h4 : 0 ≤ 1 / (M : ℝ) := by positivity
    constructor <;> linarith
  have h5 : ‖1 - u / c‖ ≤ 1 + ‖u‖ / c := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_div, Complex.norm_real, Real.norm_of_nonneg hc.le]
  have hA : ‖rtU M u / u ^ 2 * (1 / (M : ℂ) - 1) * (1 - u / c)‖ ≤ ‖rtU M u‖ / ‖u‖ ^ 2 * 1 * (1 + ‖u‖ / c) := by
    rw [norm_mul, norm_mul, norm_div, norm_pow]
    gcongr
  have hB : ‖rtU M u / (u * c)‖ = ‖rtU M u‖ / (‖u‖ * c) := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
  refine (norm_sub_le _ _).trans ?_
  rw [hB]
  refine (add_le_add_left hA _).trans (le_of_eq ?_)
  field_simp
  ring

/-- `|E| ≤ 2 |ξ| e^{Re ξ^M}` where `Re ξ^M ≥ 0`. -/
theorem norm_EE_upper {M : ℕ} {c : ℝ} (hcM : 2 ≤ c * M) {ξ : ℂ} (h0 : 0 ≤ (ξ ^ M).re) :
    ‖EE M c ξ‖ ≤ 2 * ‖ξ‖ * Real.exp (ξ ^ M).re := by
  have hk0 : 0 < c * M := by linarith
  set k : ℝ := 1 / (c * M) with hk
  have hk1 : k ≤ 1 / 2 := by
    rw [hk]
    exact one_div_le_one_div_of_le (by norm_num) hcM
  have hkpos : 0 < k := by rw [hk]; positivity
  have hkc : 1 / ((c : ℂ) * M) = (k : ℂ) := by rw [hk]; push_cast; ring
  have hint : ‖∫ τ in (0 : ℝ)..1, Complex.exp ((ξ * τ) ^ M)‖ ≤ Real.exp (ξ ^ M).re := by
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun τ : ℝ => Complex.exp ((ξ * τ) ^ M)) (C := Real.exp (ξ ^ M).re) (fun τ hτ => by
        rw [uIoc_of_le zero_le_one] at hτ
        rw [Complex.norm_exp]
        refine Real.exp_le_exp.2 ?_
        have h2 : (ξ * (τ : ℂ)) ^ M = ξ ^ M * ((τ ^ M : ℝ) : ℂ) := by rw [mul_pow]; push_cast; rfl
        rw [h2, Complex.re_mul_ofReal]
        exact mul_le_of_le_one_right h0 (pow_le_one₀ hτ.1.le hτ.2))
    simpa using h1
  have hE₀ : ‖E₀ M ξ‖ ≤ ‖ξ‖ * Real.exp (ξ ^ M).re := by
    rw [E₀, norm_mul]
    exact mul_le_mul_of_nonneg_left hint (norm_nonneg _)
  have h1k : ‖(1 : ℂ) + (k : ℂ)‖ ≤ 1 + k := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, Complex.norm_real, Real.norm_of_nonneg hkpos.le]
  have hlast : ‖(k : ℂ) * (ξ * Complex.exp (ξ ^ M))‖ = k * (‖ξ‖ * Real.exp (ξ ^ M).re) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hkpos.le, Complex.norm_exp]
  rw [EE, hkc]
  refine (norm_sub_le _ _).trans ?_
  rw [hlast, norm_mul]
  have h3 : ‖(1 : ℂ) + (k : ℂ)‖ * ‖E₀ M ξ‖ ≤ (1 + k) * (‖ξ‖ * Real.exp (ξ ^ M).re) :=
    mul_le_mul h1k hE₀ (norm_nonneg _) (by positivity)
  have h4 : 0 ≤ ‖ξ‖ * Real.exp (ξ ^ M).re := by positivity
  nlinarith

theorem norm_line_sq (s τ : ℝ) : ‖(s : ℂ) + τ * I‖ ^ 2 = s ^ 2 + τ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_add_mul_I]

set_option maxHeartbeats 2000000 in
/-- The core of the exit bound, in the closed upper half plane. -/
theorem exit_core {M : ℕ} (hM : 8 ≤ M) {a c R x τ : ℝ} (ha : 100 ≤ a) (hc : c = 2 * a)
    (h1 : 200 * a * M ≤ Real.exp ((a - 1) / 2)) (h2 : R ≤ Real.exp ((a - 1) / 2)) (hx1 : a - 1 ≤ x) (hx2 : x ≤ a)
    (hτ : 0 ≤ τ) : R ≤ ‖psi M c ((x : ℂ) + τ * I)‖ := by
  have hM1 : 1 ≤ M := by omega
  have hM0 : M ≠ 0 := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hM8 : (8 : ℝ) ≤ M := by exact_mod_cast hM
  have hapos : 0 < a := by linarith
  have ha1 : 0 < a - 1 := by linarith
  have hcpos : 0 < c := by rw [hc]; linarith
  have hxpos : 0 < x := by linarith
  set y : ℂ := (x : ℂ) + τ * I with hy
  have hyre : y.re = x := by simp [hy]
  have hyim : y.im = τ := by simp [hy]
  have hyne : y ≠ 0 := by
    intro h
    rw [h] at hyre
    simp at hyre
    linarith
  set rr : ℝ := ‖rtU M y‖ with hrr
  set ny : ℝ := ‖y‖ with hny
  set nn : ℝ := ‖1 - y / c‖ with hnn
  have hnyx : x ≤ ny := by
    have := Complex.abs_re_le_norm y
    rw [hyre, abs_of_pos hxpos] at this
    exact this
  have hnypos : 0 < ny := by linarith
  have hny1 : 1 ≤ ny := by linarith
  have hrr1 : 1 ≤ rr := one_le_rtU_norm hM0 hyne hny1
  have hnn1 : 1 / 2 ≤ nn := by
    have h3 := Complex.re_le_norm (1 - y / c)
    have h4 : (1 - y / c).re = 1 - x / c := by
      rw [Complex.sub_re, Complex.one_re, Complex.div_ofReal_re, hyre]
    rw [h4] at h3
    have h5 : x / c ≤ 1 / 2 := by
      rw [div_le_iff₀ hcpos, hc]
      linarith
    linarith
  have hnn2 : ny / (3 * c) ≤ nn := by
    by_cases hcase : ny ≤ 3 / 2 * c
    · have : ny / (3 * c) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      linarith
    · have h3 : ny / c - 1 ≤ nn := by
        have h4 := norm_sub_norm_le (y / c) (1 : ℂ)
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hcpos.le, norm_one, norm_sub_rev] at h4
        exact h4
      have h5 : ny / (3 * c) ≤ ny / c - 1 := by
        have h6 : 3 / 2 < ny / c := by
          rw [lt_div_iff₀ hcpos]
          linarith [not_le.1 hcase]
        have h7 : ny / (3 * c) = ny / c / 3 := by field_simp
        rw [h7]
        linarith
      linarith
  -- the line
  have hline : ∀ s : ℝ, x / 2 ≤ s → s ≤ x →
      (s : ℂ) + τ * I ≠ 0 ∧ 0 ≤ ((s : ℂ) + τ * I).im ∧ ‖(s : ℂ) + τ * I‖ ≤ ny ∧ ny ≤ 2 * ‖(s : ℂ) + τ * I‖ := by
    intro s hs1 hs2
    have hs0 : 0 < s := by linarith
    refine ⟨fun h => ?_, by simpa using hτ, ?_, ?_⟩
    · have := congrArg Complex.re h
      simp at this
      linarith
    · refine (pow_le_pow_iff_left₀ (norm_nonneg _) hnypos.le two_ne_zero).1 ?_
      rw [norm_line_sq, hny, hy, norm_line_sq]
      nlinarith
    · refine (pow_le_pow_iff_left₀ hnypos.le (by positivity) two_ne_zero).1 ?_
      rw [mul_pow, norm_line_sq, norm_line_sq]
      nlinarith
  set K₀ : ℝ := rr / ny * (6 / (a - 1)) with hK₀
  have hK₀pos : 0 ≤ K₀ := by positivity
  set g : ℝ → ℂ := fun s => Qf M c ((s : ℂ) + τ * I) with hg
  have hgd : ∀ s : ℝ, x / 2 ≤ s → s ≤ x →
      HasDerivAt g (-(1 / (M : ℂ)) * (Complex.exp ((s : ℂ) + τ * I) * Dfn M c ((s : ℂ) + τ * I))) s := by
    intro s hs1 hs2
    obtain ⟨h3, h4, -, -⟩ := hline s hs1 hs2
    have h5 : HasDerivAt (fun z : ℂ => Qf M c (z + (τ : ℂ) * I)) _ (s : ℂ) :=
      HasDerivAt.comp_add_const (s : ℂ) ((τ : ℂ) * I) (Qf_hasDerivAt hM1 hcpos.ne' h4 h3)
    exact h5.comp_ofReal
  have hbound : ∀ s : ℝ, x / 2 ≤ s → s ≤ x →
      ‖-(1 / (M : ℂ)) * (Complex.exp ((s : ℂ) + τ * I) * Dfn M c ((s : ℂ) + τ * I))‖ ≤ K₀ / M * Real.exp s := by
    intro s hs1 hs2
    obtain ⟨h3, -, h5, h6⟩ := hline s hs1 hs2
    set u : ℂ := (s : ℂ) + τ * I with hu
    have hunorm : 0 < ‖u‖ := norm_pos_iff.2 h3
    have hD := norm_Dfn_le hM1 hcpos h3
    have hru : ‖rtU M u‖ ≤ rr := rtU_norm_mono hM0 h3 hyne h5
    have h7 : 1 / ‖u‖ ≤ 2 / ny := by
      rw [div_le_div_iff₀ hunorm hnypos]
      linarith
    have h8 : 2 / ny ≤ 2 / (a - 1) := div_le_div_of_nonneg_left (by norm_num) ha1 (by linarith)
    have h9 : 2 / c ≤ 1 / (a - 1) := by
      rw [hc, div_le_div_iff₀ (by positivity) ha1]
      linarith
    have h10 : 1 / ‖u‖ + 2 / c ≤ 3 / (a - 1) := by
      have h11 : 3 / (a - 1) = 2 / (a - 1) + 1 / (a - 1) := by ring
      rw [h11]
      linarith
    have h12 : ‖rtU M u‖ / ‖u‖ ≤ rr * (2 / ny) := by
      calc ‖rtU M u‖ / ‖u‖ = ‖rtU M u‖ * (1 / ‖u‖) := by ring
        _ ≤ rr * (2 / ny) := mul_le_mul hru h7 (by positivity) (by positivity)
    have hDle : ‖Dfn M c u‖ ≤ K₀ := by
      refine hD.trans ?_
      calc ‖rtU M u‖ / ‖u‖ * (1 / ‖u‖ + 2 / c) ≤ rr * (2 / ny) * (3 / (a - 1)) :=
            mul_le_mul h12 h10 (by positivity) (by positivity)
        _ = K₀ := by rw [hK₀]; ring
    have hexp : ‖Complex.exp u‖ = Real.exp s := by
      rw [Complex.norm_exp]
      simp [hu]
    rw [norm_mul, norm_neg, norm_div, norm_one, Complex.norm_natCast, norm_mul, hexp]
    calc 1 / (M : ℝ) * (Real.exp s * ‖Dfn M c u‖) ≤ 1 / (M : ℝ) * (Real.exp s * K₀) := by gcongr
      _ = K₀ / M * Real.exp s := by ring
  -- integrate along the line
  have hx2' : x / 2 ≤ x := by linarith
  have hpath : ‖g x - g (x / 2)‖ ≤ K₀ / M * (Real.exp x - Real.exp (x / 2)) := by
    have hcont : ContinuousOn (fun s => g s - g (x / 2)) (Icc (x / 2) x) := fun s hs =>
      ((hgd s hs.1 hs.2).continuousAt.sub continuousAt_const).continuousWithinAt
    have hder : ∀ s ∈ Ico (x / 2) x, HasDerivWithinAt (fun s => g s - g (x / 2))
        (-(1 / (M : ℂ)) * (Complex.exp ((s : ℂ) + τ * I) * Dfn M c ((s : ℂ) + τ * I))) (Ici s) s := fun s hs =>
      ((hgd s hs.1 hs.2.le).sub_const _).hasDerivWithinAt
    have hB : ∀ s : ℝ, HasDerivAt (fun s => K₀ / M * (Real.exp s - Real.exp (x / 2))) (K₀ / M * Real.exp s) s := fun s =>
      ((Real.hasDerivAt_exp s).sub_const _).const_mul _
    exact image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont hder (by simp) hB
      (fun s hs => hbound s hs.1 hs.2.le) (right_mem_Icc.2 hx2')
  -- the far end
  have hxh : x / 2 + 0 = x / 2 := add_zero _
  obtain ⟨hy₂ne, hy₂im, hy₂le, hy₂ge⟩ := hline (x / 2) le_rfl hx2'
  set y₂ : ℂ := ((x / 2 : ℝ) : ℂ) + τ * I with hy₂
  have hy₂re : y₂.re = x / 2 := by simp [hy₂]
  have hny₂ : 49 ≤ ‖y₂‖ := by
    have := Complex.abs_re_le_norm y₂
    rw [hy₂re, abs_of_pos (by linarith)] at this
    linarith
  set Xh : ℝ := Real.exp (x / 2) with hXh
  set X : ℝ := Real.exp x with hX
  have hXX : X = Xh * Xh := by rw [hX, hXh, ← Real.exp_add]; ring_nf
  have hXhpos : 0 < Xh := Real.exp_pos _
  have hcM : 2 ≤ c * M := by rw [hc]; nlinarith
  have hfar1 : ‖psi M c y₂‖ ≤ 2 * rr * Xh := by
    have h3 := norm_EE_upper (ξ := rtU M y₂) hcM (by rw [rtU_pow hM0 hy₂ne, hy₂re]; linarith)
    rw [rtU_pow hM0 hy₂ne, hy₂re] at h3
    have h4 : ‖rtU M y₂‖ ≤ rr := rtU_norm_mono hM0 hy₂ne hyne hy₂le
    calc ‖psi M c y₂‖ ≤ 2 * ‖rtU M y₂‖ * Xh := h3
      _ ≤ 2 * rr * Xh := by gcongr
  have hfar2 : ‖1 / (M : ℂ) * (Complex.exp y₂ * hhf M c y₂)‖ ≤ rr * Xh := by
    have hexp : ‖Complex.exp y₂‖ = Xh := by rw [Complex.norm_exp, hy₂re]
    have hypos : 0 < ‖y₂‖ := by linarith
    have h3 : ‖hhf M c y₂‖ ≤ rr := by
      rw [hhf, norm_mul, norm_div]
      have h4 : ‖rtU M y₂‖ ≤ rr := rtU_norm_mono hM0 hy₂ne hyne hy₂le
      have h5 : ‖1 - y₂ / c‖ ≤ 1 + ‖y₂‖ / c := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_one, norm_div, Complex.norm_real, Real.norm_of_nonneg hcpos.le]
      have h6 : (1 + ‖y₂‖ / c) / ‖y₂‖ ≤ 1 := by
        rw [div_le_one hypos]
        have h7 : ‖y₂‖ / c ≤ ‖y₂‖ / 2 := by
          refine div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) ?_
          rw [hc]
          linarith
        linarith
      calc ‖rtU M y₂‖ / ‖y₂‖ * ‖1 - y₂ / c‖ ≤ rr / ‖y₂‖ * (1 + ‖y₂‖ / c) := by gcongr
        _ = rr * ((1 + ‖y₂‖ / c) / ‖y₂‖) := by ring
        _ ≤ rr * 1 := by gcongr
        _ = rr := mul_one _
    rw [norm_mul, norm_mul, norm_div, norm_one, Complex.norm_natCast, hexp]
    have h4 : 1 / (M : ℝ) ≤ 1 := (div_le_one hMpos).2 (by linarith)
    calc 1 / (M : ℝ) * (Xh * ‖hhf M c y₂‖) ≤ 1 * (Xh * rr) := by gcongr
      _ = rr * Xh := by ring
  have hgfar : ‖g (x / 2)‖ ≤ 3 * rr * Xh := by
    have h3 : g (x / 2) = psi M c y₂ - 1 / (M : ℂ) * (Complex.exp y₂ * hhf M c y₂) := rfl
    rw [h3]
    refine (norm_sub_le _ _).trans ?_
    linarith
  -- the main term
  set Mn : ℝ := 1 / M * X * (rr / ny) * nn with hMn
  have hmain : ‖1 / (M : ℂ) * (Complex.exp y * hhf M c y)‖ = Mn := by
    have hexp : ‖Complex.exp y‖ = X := by rw [Complex.norm_exp, hyre]
    rw [norm_mul, norm_mul, norm_div, norm_one, Complex.norm_natCast, hexp, hhf, norm_mul, norm_div, hMn]
    ring
  have hQy : g x = psi M c y - 1 / (M : ℂ) * (Complex.exp y * hhf M c y) := rfl
  have hpsi : Mn - ‖g x‖ ≤ ‖psi M c y‖ := by
    have h3 := norm_sub_norm_le (1 / (M : ℂ) * (Complex.exp y * hhf M c y)) (-(g x))
    rw [hmain, norm_neg, sub_neg_eq_add, hQy] at h3
    have h4 : 1 / (M : ℂ) * (Complex.exp y * hhf M c y) +
        (psi M c y - 1 / (M : ℂ) * (Complex.exp y * hhf M c y)) = psi M c y := by ring
    rw [h4] at h3
    rw [hQy]
    exact h3
  have hXpos : 0 < X := Real.exp_pos _
  have hMn1 : X * rr / (3 * c * M) ≤ Mn := by
    calc X * rr / (3 * c * M) = 1 / M * X * (rr / ny) * (ny / (3 * c)) := by field_simp
      _ ≤ Mn := by rw [hMn]; gcongr
  have hg1 : K₀ / M * (X - Xh) ≤ 12 / 99 * Mn := by
    have h3 : K₀ / M * (X - Xh) ≤ K₀ / M * X := by
      have : 0 ≤ K₀ / M := by positivity
      nlinarith
    have h4 : 6 / (a - 1) ≤ 6 / 99 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have h5 : K₀ / M * X ≤ 1 / M * X * (rr / ny) * (6 / 99) := by
      rw [hK₀]
      have h6 : rr / ny * (6 / (a - 1)) / M * X = 1 / M * X * (rr / ny) * (6 / (a - 1)) := by ring
      rw [h6]
      gcongr
    have h6 : 1 / M * X * (rr / ny) * (6 / 99) ≤ 12 / 99 * Mn := by
      have h7 : 0 ≤ 1 / M * X * (rr / ny) := by positivity
      rw [hMn]
      nlinarith
    linarith
  have hE : Real.exp ((a - 1) / 2) ≤ Xh := Real.exp_le_exp.2 (by linarith)
  have hXhbig : 100 * c * M ≤ Xh := by
    rw [hc]
    nlinarith
  have hg2 : 3 * rr * Xh ≤ 9 / 100 * Mn := by
    have h3 : (100 / 3) * (rr * Xh) ≤ X * rr / (3 * c * M) := by
      have hcMpos : 0 < c * M := by positivity
      rw [le_div_iff₀ (by positivity), hXX]
      have h4 : 0 ≤ rr * Xh := by positivity
      nlinarith
    nlinarith
  have hgx : ‖g x‖ ≤ (12 / 99 + 9 / 100) * Mn := by
    have h3 : ‖g x‖ ≤ ‖g x - g (x / 2)‖ + ‖g (x / 2)‖ := by
      have := norm_add_le (g x - g (x / 2)) (g (x / 2))
      rwa [sub_add_cancel] at this
    linarith
  have hMnpos : 0 < Mn := by rw [hMn]; positivity
  have hfinal : Mn / 2 ≤ ‖psi M c y‖ := by nlinarith
  set E : ℝ := Real.exp ((a - 1) / 2) with hEdef
  have hEpos : 0 < E := Real.exp_pos _
  have hXE : E * E ≤ X := by
    rw [hXX]
    exact mul_le_mul hE hE hEpos.le hXhpos.le
  have hMnE : 2 * E ≤ Mn := by
    have hcMpos : 0 < c * M := by positivity
    have h3 : 2 * E ≤ X * rr / (3 * c * M) := by
      rw [le_div_iff₀ (by positivity), hc]
      have h4 : (200 * a * M) * E ≤ E * E := by nlinarith
      nlinarith
    linarith
  linarith

/-- **Exit.** -/
theorem norm_EE_exit {M : ℕ} (hM : 8 ≤ M) {a R : ℝ} (ha : 100 ≤ a) (h1 : 200 * a * M ≤ Real.exp ((a - 1) / 2))
    (h2 : R ≤ Real.exp ((a - 1) / 2)) (ξ : ℂ) (h3 : a - 1 ≤ (ξ ^ M).re) (h4 : (ξ ^ M).re ≤ a) :
    R ≤ ‖EE M (2 * a) ξ‖ := by
  have hM0 : M ≠ 0 := by omega
  have hne : ξ ^ M ≠ 0 := by
    intro h
    rw [h] at h3
    simp at h3
    linarith
  have hy : (⟨(ξ ^ M).re, |(ξ ^ M).im|⟩ : ℂ) = (((ξ ^ M).re : ℝ) : ℂ) + (|(ξ ^ M).im| : ℝ) * I := by
    apply Complex.ext <;> simp
  rw [norm_EE_eq_psi hM0 _ hne, hy]
  exact exit_core hM ha rfl h1 h2 h3 h4 (abs_nonneg _)

end Smale.P030
