/-
Smale/P030/Params.lean — the `M`-th root transform `ξ(t)^M = y(t^M)` of a univalent map with `y(0) = 0`, and the choice of the
numbers `M`, `a`, then `C`.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import Smale.P030.Defs

@[expose] public section

namespace Smale.P030

open Complex Metric Set Filter Topology

/-- A holomorphic nonvanishing `q` on the disk has a holomorphic `M`-th root. -/
theorem exists_root_on_disk {M : ℕ} (hM : M ≠ 0) {q : ℂ → ℂ} (hq : DifferentiableOn ℂ q (ball 0 1))
    (hne : ∀ u ∈ ball (0 : ℂ) 1, q u ≠ 0) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball 0 1) ∧ ∀ u ∈ ball (0 : ℂ) 1, h u ^ M = q u := by
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  have h0mem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hdq : DifferentiableOn ℂ (deriv q) (ball 0 1) := hq.deriv isOpen_ball
  have hf : DifferentiableOn ℂ (fun u => deriv q u / q u) (ball 0 1) := hdq.div hq hne
  obtain ⟨L, hL0, hL⟩ := hf.isExactOn_ball.with_val_at 0 (Complex.log (q 0))
  have hLd : DifferentiableOn ℂ L (ball 0 1) := fun u hu => (hL u hu).differentiableAt.differentiableWithinAt
  have hqat : ∀ u ∈ ball (0 : ℂ) 1, HasDerivAt q (deriv q u) u := fun u hu =>
    ((hq u hu).differentiableAt (isOpen_ball.mem_nhds hu)).hasDerivAt
  have hPd : ∀ u ∈ ball (0 : ℂ) 1, HasDerivAt (fun u => q u * Complex.exp (-L u)) 0 u := by
    intro u hu
    have h1 := (hqat u hu).mul ((hL u hu).neg.cexp)
    convert h1 using 1
    have hqu := hne u hu
    field_simp
    ring
  have hPconst : ∀ u ∈ ball (0 : ℂ) 1, q u * Complex.exp (-L u) = 1 := by
    intro u hu
    have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
      (fun v hv => (hPd v hv).differentiableAt.differentiableWithinAt)
      (fun v hv => (hPd v hv).deriv) hu h0mem
    rw [hconst, hL0, Complex.exp_neg, Complex.exp_log (hne 0 h0mem)]
    exact mul_inv_cancel₀ (hne 0 h0mem)
  refine ⟨fun u => Complex.exp (L u / M), fun u hu => ((hLd u hu).div_const _).cexp, fun u hu => ?_⟩
  have hP := hPconst u hu
  simp only
  rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ hMc]
  rw [Complex.exp_neg] at hP
  have hexp := Complex.exp_ne_zero (L u)
  field_simp at hP
  exact hP.symm

/-- The `M`-th root transform: `ξ(t)^M = y(t^M)`. -/
theorem exists_root_transform {M : ℕ} (hM : 1 ≤ M) {y : ℂ → ℂ} (hy : DifferentiableOn ℂ y disk) (hy0 : y 0 = 0)
    (hy1 : ∀ u ∈ disk, deriv y u ≠ 0) (hyne : ∀ u ∈ disk, u ≠ 0 → y u ≠ 0) :
    ∃ ξ : ℂ → ℂ, DifferentiableOn ℂ ξ disk ∧ ξ 0 = 0 ∧ (∀ t ∈ disk, ξ t ^ M = y (t ^ M)) ∧
      (∀ t ∈ disk, deriv ξ t ≠ 0) ∧ ‖deriv ξ 0‖ ^ M = ‖deriv y 0‖ := by
  have hM0 : M ≠ 0 := by omega
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM0
  have h0mem : (0 : ℂ) ∈ disk := mem_ball_self one_pos
  set q : ℂ → ℂ := dslope y 0 with hqdef
  have hqd : DifferentiableOn ℂ q disk := (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds h0mem)).2 hy
  have hqu : ∀ u, u * q u = y u := by
    intro u
    have h1 := sub_smul_dslope y 0 u
    rw [hy0, sub_zero, sub_zero, smul_eq_mul] at h1
    exact h1
  have hq0 : q 0 = deriv y 0 := dslope_same y 0
  have hqne : ∀ u ∈ disk, q u ≠ 0 := by
    intro u hu h0
    by_cases hu0 : u = 0
    · rw [hu0, hq0] at h0
      exact hy1 0 h0mem h0
    · have h1 := hqu u
      rw [h0, mul_zero] at h1
      exact hyne u hu hu0 h1.symm
  obtain ⟨h, hhd, hhpow⟩ := exists_root_on_disk hM0 hqd hqne
  have hpowmem : ∀ t ∈ disk, t ^ M ∈ disk := by
    intro t ht
    have ht1 : ‖t‖ < 1 := by simpa using ht
    have h1 : ‖t ^ M‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) ht1 hM0
    simpa using h1
  have hpowd : ∀ t : ℂ, HasDerivAt (fun t : ℂ => t ^ M) ((M : ℂ) * t ^ (M - 1)) t := fun t => hasDerivAt_pow M t
  have hhat : ∀ u ∈ disk, HasDerivAt h (deriv h u) u := fun u hu =>
    ((hhd u hu).differentiableAt (isOpen_ball.mem_nhds hu)).hasDerivAt
  have hyat : ∀ u ∈ disk, HasDerivAt y (deriv y u) u := fun u hu =>
    ((hy u hu).differentiableAt (isOpen_ball.mem_nhds hu)).hasDerivAt
  have hξat : ∀ t ∈ disk, HasDerivAt (fun t => t * h (t ^ M))
      (1 * h (t ^ M) + t * (deriv h (t ^ M) * ((M : ℂ) * t ^ (M - 1)))) t := fun t ht =>
    (hasDerivAt_id t).mul ((hhat _ (hpowmem t ht)).comp t (hpowd t))
  have hξpow : ∀ t ∈ disk, (t * h (t ^ M)) ^ M = y (t ^ M) := by
    intro t ht
    rw [mul_pow, hhpow _ (hpowmem t ht), hqu]
  have hzero : (0 : ℂ) ^ M = 0 := zero_pow hM0
  have hderiv0 : deriv (fun t => t * h (t ^ M)) 0 = h 0 := by
    rw [(hξat 0 h0mem).deriv, hzero]
    simp
  have hh0 : h 0 ^ M = deriv y 0 := by rw [hhpow 0 h0mem, hq0]
  refine ⟨fun t => t * h (t ^ M), fun t ht => (hξat t ht).differentiableAt.differentiableWithinAt, by simp, hξpow,
    fun t ht => ?_, ?_⟩
  · by_cases ht0 : t = 0
    · rw [ht0, hderiv0]
      intro h0
      apply hy1 0 h0mem
      rw [← hh0, h0, zero_pow hM0]
    · intro h0
      have hLeft : HasDerivAt (fun t => (t * h (t ^ M)) ^ M)
          ((M : ℂ) * (t * h (t ^ M)) ^ (M - 1) * deriv (fun t => t * h (t ^ M)) t) t :=
        ((hξat t ht).differentiableAt.hasDerivAt).fun_pow M
      have hRight : HasDerivAt (fun t => y (t ^ M)) (deriv y (t ^ M) * ((M : ℂ) * t ^ (M - 1))) t :=
        (hyat _ (hpowmem t ht)).comp t (hpowd t)
      have hEq : (fun t => (t * h (t ^ M)) ^ M) =ᶠ[𝓝 t] fun t => y (t ^ M) := by
        filter_upwards [isOpen_ball.mem_nhds ht] with s hs using hξpow s hs
      have huniq := (hLeft.congr_of_eventuallyEq hEq.symm).unique hRight
      rw [h0, mul_zero] at huniq
      have hne : deriv y (t ^ M) * ((M : ℂ) * t ^ (M - 1)) ≠ 0 :=
        mul_ne_zero (hy1 _ (hpowmem t ht)) (mul_ne_zero hMc (pow_ne_zero _ ht0))
      exact hne huniq.symm
  · rw [hderiv0, ← norm_pow, hh0]

/-- The numbers: `a = n`, `M = n²`, `n` large. `2a ≤ (1 + ε)^M` by Bernoulli. -/
theorem exists_params {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ (M : ℕ) (a : ℝ), 8 ≤ M ∧ 100 ≤ a ∧ 200 * a * M ≤ Real.exp ((a - 1) / 2) ∧ R ≤ Real.exp ((a - 1) / 2) ∧
      2 * a ≤ (1 + ε) ^ M ∧ 1 - ε / 2 ≤ (M : ℝ) / (M + 1) := by
  have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3
  have h2 : ∀ᶠ t : ℝ in atTop, t ^ 3 * Real.exp (-t) < 1 / 5400 := h1.eventually (gt_mem_nhds (by norm_num))
  have h3 : ∀ᶠ t : ℝ in atTop, R ≤ Real.exp t := Real.tendsto_exp_atTop.eventually_ge_atTop R
  obtain ⟨T, hT⟩ := eventually_atTop.1 (h2.and h3)
  set n : ℕ := ⌈max (max 100 (2 / ε)) (2 * max T 1 + 1)⌉₊ with hn
  have hnbig : max (max 100 (2 / ε)) (2 * max T 1 + 1) ≤ (n : ℝ) := Nat.le_ceil _
  have hn100 : (100 : ℝ) ≤ n := ((le_max_left _ _).trans (le_max_left _ _)).trans hnbig
  have hnε : 2 / ε ≤ (n : ℝ) := ((le_max_right _ _).trans (le_max_left _ _)).trans hnbig
  have hnT : 2 * max T 1 + 1 ≤ (n : ℝ) := (le_max_right _ _).trans hnbig
  have hnpos : (0 : ℝ) < n := by linarith
  set t : ℝ := ((n : ℝ) - 1) / 2 with ht
  have htT : T ≤ t := by
    have := le_max_left T 1
    rw [ht]
    linarith
  have ht1 : 1 ≤ t := by
    have := le_max_right T 1
    rw [ht]
    linarith
  obtain ⟨hexp, hRe⟩ := hT t htT
  have hnt : (n : ℝ) ≤ 3 * t := by
    have : (n : ℝ) = 2 * t + 1 := by rw [ht]; ring
    linarith
  have hM8 : 8 ≤ n * n := by
    have h100 : 100 ≤ n := by exact_mod_cast hn100
    nlinarith
  have hMcast : ((n * n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by push_cast; ring
  refine ⟨n * n, n, hM8, hn100, ?_, hRe, ?_, ?_⟩
  · rw [hMcast]
    have h4 : t ^ 3 * Real.exp (-t) * Real.exp t = t ^ 3 := by
      rw [mul_assoc, ← Real.exp_add]
      simp
    have h5 : t ^ 3 ≤ 1 / 5400 * Real.exp t := by
      rw [← h4]
      exact mul_le_mul_of_nonneg_right hexp.le (Real.exp_pos _).le
    have h6 : (n : ℝ) ^ 3 ≤ (3 * t) ^ 3 := pow_le_pow_left₀ hnpos.le hnt 3
    have h7 : (3 * t) ^ 3 = 27 * t ^ 3 := by ring
    have h8 : 200 * (n : ℝ) * (n : ℝ) ^ 2 = 200 * (n : ℝ) ^ 3 := by ring
    rw [h8]
    linarith
  · have hb := one_add_mul_le_pow (a := ε) (n := n * n) (by linarith)
    have h4 : (2 : ℝ) ≤ n * ε := by
      rwa [div_le_iff₀ hε] at hnε
    rw [hMcast] at hb
    nlinarith
  · rw [hMcast]
    have hnε' : 1 ≤ (n : ℝ) ^ 2 * (ε / 2) := by
      have h4 : (2 : ℝ) ≤ n * ε := by
        rwa [div_le_iff₀ hε] at hnε
      nlinarith
    rw [le_div_iff₀ (by positivity)]
    nlinarith

/-- The choice of `C`, last of all. -/
theorem exists_C {a c ε η : ℝ} {M : ℕ} (ha : 0 < a) (hc : 0 < c) (hM : 1 ≤ M) (hε : 0 < ε) (hη : 0 < η) :
    ∃ (n : ℕ) (C : ℝ), C = (2 * n + 1) * Real.pi ∧ 1 ≤ C ∧ 10 * c ≤ C - 1 / 2 ∧
      C / M * Real.exp (-C) * (1 + 2 * C / c) ≤ ε / 2 ∧ 4 * Real.sinh (stripBeta C * a) < η := by
  have hC : Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1) * Real.pi) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (2 : ℝ) * n + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
    exact h1.atTop_mul_const Real.pi_pos
  have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h2 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  have hf₁ : Tendsto (fun C : ℝ => C / M * Real.exp (-C) * (1 + 2 * C / c)) atTop (𝓝 0) := by
    have h3 : Tendsto (fun C : ℝ => 1 / (M : ℝ) * (C ^ 1 * Real.exp (-C)) + 2 / (c * M) * (C ^ 2 * Real.exp (-C))) atTop
        (𝓝 (1 / (M : ℝ) * 0 + 2 / (c * M) * 0)) := (h1.const_mul _).add (h2.const_mul _)
    simp only [mul_zero, add_zero] at h3
    refine h3.congr fun C => ?_
    have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
    field_simp
  have hf₂ : Tendsto (fun C : ℝ => 4 * Real.sinh (stripBeta C * a)) atTop (𝓝 0) := by
    have h3 : Tendsto (fun C : ℝ => stripBeta C * a) atTop (𝓝 0) := by
      have h4 : Tendsto (fun C : ℝ => Real.pi * a / 2 / C) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
      refine h4.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with C hC0
      rw [stripBeta]
      field_simp
    have h5 := (Real.continuous_sinh.tendsto 0).comp h3
    have h6 := h5.const_mul 4
    simpa [Function.comp_def] using h6
  have hev : ∀ᶠ C : ℝ in atTop, 1 ≤ C ∧ 10 * c ≤ C - 1 / 2 ∧ C / M * Real.exp (-C) * (1 + 2 * C / c) ≤ ε / 2 ∧
      4 * Real.sinh (stripBeta C * a) < η := by
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (10 * c + 1 / 2),
      hf₁.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < ε / 2)), hf₂.eventually (gt_mem_nhds hη)] with C h3 h4 h5 h6
    exact ⟨h3, by linarith, h5, h6⟩
  obtain ⟨n, hn1, hn2, hn3, hn4⟩ := (hC.eventually hev).exists
  exact ⟨n, _, rfl, hn1, hn2, hn3, hn4⟩

end Smale.P030
