/-
Smale/Proofs/Koebe.lean — Bieberbach's theorem for the second coefficient (1916) and Koebe's omitted-value bounds, from
the area theorem (Smale/Proofs/AreaThm.lean).
Bieberbach: for `G ∈ 𝒮`, the function `q(w) = G(w)/w` has a holomorphic square root `s` on the disk, `s(0) = 1`, and
`g(u) = u s(u²)` is odd and injective with `g(u)² = G(u²)`. So `F(z) = 1/g(1/z) = z + h(1/z)` is injective on `|z| > 1`,
with `h'(0) = -a₂/2`; the area theorem gives `|a₂| ≤ 2`.
Koebe: if `G` omits `w`, the Koebe transform `G/(1 - G/w)` is in `𝒮` with second coefficient `a₂ + 1/w`.
Sanity rows: `area_b1_sharp`, `koebe_function_sharp` show that the hypotheses can be met and the constants are best possible.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import Smale.Proofs.AreaThm

@[expose] public section

namespace Smale.Koebe

open Metric Set Filter Topology Complex

/-! ### A holomorphic square root on the disk -/

/-- A nonvanishing holomorphic function on the unit disk with value `1` at `0` has a holomorphic square root with
value `1` at `0`. -/
lemma exists_sqrt_on_disk {q : ℂ → ℂ} (hq : DifferentiableOn ℂ q (ball 0 1))
    (hne : ∀ u ∈ ball (0 : ℂ) 1, q u ≠ 0) (h0 : q 0 = 1) :
    ∃ s : ℂ → ℂ, DifferentiableOn ℂ s (ball 0 1) ∧ s 0 = 1 ∧ ∀ u ∈ ball (0 : ℂ) 1, s u ^ 2 = q u := by
  have hdq : DifferentiableOn ℂ (deriv q) (ball 0 1) := hq.deriv isOpen_ball
  have hf : DifferentiableOn ℂ (fun u => deriv q u / q u) (ball 0 1) := hdq.div hq hne
  obtain ⟨L, hL0, hL⟩ := hf.isExactOn_ball.with_val_at 0 0
  have hLd : DifferentiableOn ℂ L (ball 0 1) := fun u hu => (hL u hu).differentiableAt.differentiableWithinAt
  have hqat : ∀ u ∈ ball (0 : ℂ) 1, HasDerivAt q (deriv q u) u := fun u hu =>
    ((hq u hu).differentiableAt (isOpen_ball.mem_nhds hu)).hasDerivAt
  -- `q * exp (-L)` has zero derivative
  have hPd : ∀ u ∈ ball (0 : ℂ) 1, HasDerivAt (fun u => q u * cexp (-L u)) 0 u := by
    intro u hu
    have h1 := (hqat u hu).mul ((hL u hu).neg.cexp)
    convert h1 using 1
    have hqu := hne u hu
    field_simp
    ring
  have hPconst : ∀ u ∈ ball (0 : ℂ) 1, q u * cexp (-L u) = 1 := by
    intro u hu
    have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
      (fun v hv => (hPd v hv).differentiableAt.differentiableWithinAt)
      (fun v hv => (hPd v hv).deriv) hu (mem_ball_self one_pos)
    rw [hconst, h0, hL0]
    simp
  refine ⟨fun u => cexp (L u / 2), ?_, ?_, ?_⟩
  · exact fun u hu => ((hLd u hu).div_const 2).cexp
  · simp [hL0]
  · intro u hu
    have hP := hPconst u hu
    rw [← Complex.exp_nat_mul]
    have he : ((2 : ℕ) : ℂ) * (L u / 2) = L u := by push_cast; ring
    rw [he]
    rw [Complex.exp_neg] at hP
    have hexp := Complex.exp_ne_zero (L u)
    field_simp at hP
    exact hP.symm

/-! ### Facts about `G ∈ 𝒮` -/

section ClassS

variable {G : ℂ → ℂ}

lemma inClassS_differentiableAt (hG : InClassS G) {u : ℂ} (hu : u ∈ ball (0 : ℂ) 1) :
    DifferentiableAt ℂ G u :=
  (hG.1.1 u hu).differentiableAt (isOpen_ball.mem_nhds hu)

/-- `G''(0) = 2 q'(0)` when `G(u) = u q(u)` on the disk. -/
lemma deriv_deriv_of_eq_mul {q : ℂ → ℂ} (hq : DifferentiableOn ℂ q (ball 0 1))
    (hGq : ∀ u ∈ ball (0 : ℂ) 1, G u = u * q u) : deriv (deriv G) 0 = 2 * deriv q 0 := by
  have hmem : ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := ball_mem_nhds _ one_pos
  have hqat : ∀ u ∈ ball (0 : ℂ) 1, HasDerivAt q (deriv q u) u := fun u hu =>
    ((hq u hu).differentiableAt (isOpen_ball.mem_nhds hu)).hasDerivAt
  have hdq : DifferentiableOn ℂ (deriv q) (ball 0 1) := hq.deriv isOpen_ball
  have hGev : ∀ u ∈ ball (0 : ℂ) 1, deriv G u = q u + u * deriv q u := by
    intro u hu
    have hev : G =ᶠ[𝓝 u] fun v => v * q v := by
      filter_upwards [isOpen_ball.mem_nhds hu] with v hv using hGq v hv
    have h1 : HasDerivAt (fun v => v * q v) (1 * q u + u * deriv q u) u :=
      (hasDerivAt_id u).mul (hqat u hu)
    rw [hev.deriv_eq, h1.deriv, one_mul]
  have hevd : deriv G =ᶠ[𝓝 0] fun u => q u + u * deriv q u := by
    filter_upwards [hmem] with u hu using hGev u hu
  rw [hevd.deriv_eq]
  have h0 := mem_ball_self (x := (0 : ℂ)) one_pos
  have hdq0 : HasDerivAt (deriv q) (deriv (deriv q) 0) 0 :=
    ((hdq 0 h0).differentiableAt hmem).hasDerivAt
  have hsum : HasDerivAt (fun u => q u + u * deriv q u)
      (deriv q 0 + (1 * deriv q 0 + 0 * deriv (deriv q) 0)) 0 :=
    (hqat 0 h0).add ((hasDerivAt_id (0 : ℂ)).mul hdq0)
  rw [hsum.deriv]
  ring

/-- **Bieberbach's theorem for the second coefficient** (Bieberbach 1916): for `G ∈ 𝒮`, `G(z) = z + a₂ z² + ⋯`, one has
`|a₂| ≤ 2`. Here `a₂ = G''(0)/2`. -/
theorem bieberbach_a2 (hG : InClassS G) : ‖deriv (deriv G) 0 / 2‖ ≤ 2 := by
  obtain ⟨⟨hGd, hGinj⟩, hG0, hG1⟩ := hG
  have h0mem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hnhds : ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := ball_mem_nhds _ one_pos
  -- `q(w) = G(w)/w`
  set q := dslope G 0 with hqdef
  have hqd : DifferentiableOn ℂ q (ball 0 1) := (Complex.differentiableOn_dslope hnhds).mpr hGd
  have hGq : ∀ u ∈ ball (0 : ℂ) 1, G u = u * q u := fun u _ => by
    have := sub_smul_dslope G 0 u
    simpa [hG0, smul_eq_mul] using this.symm
  have hq0 : q 0 = 1 := by rw [hqdef, dslope_same, hG1]
  have hqne : ∀ u ∈ ball (0 : ℂ) 1, q u ≠ 0 := by
    intro u hu hzero
    by_cases hu0 : u = 0
    · rw [hu0, hq0] at hzero
      exact one_ne_zero hzero
    · have hGu : G u = G 0 := by rw [hGq u hu, hzero, mul_zero, hG0]
      exact hu0 (hGinj hu h0mem hGu)
  have hA2 : deriv (deriv G) 0 / 2 = deriv q 0 := by
    rw [deriv_deriv_of_eq_mul hqd hGq]
    ring
  obtain ⟨s, hsd, hs0, hs2⟩ := exists_sqrt_on_disk hqd hqne hq0
  have hsne : ∀ u ∈ ball (0 : ℂ) 1, s u ≠ 0 := fun u hu hzero =>
    hqne u hu (by rw [← hs2 u hu, hzero]; simp)
  have hsat : HasDerivAt s (deriv s 0) 0 := ((hsd 0 h0mem).differentiableAt hnhds).hasDerivAt
  -- `s'(0) = a₂/2`
  have hs' : deriv s 0 = deriv q 0 / 2 := by
    have hev : (fun u => s u ^ 2) =ᶠ[𝓝 0] q := by
      filter_upwards [hnhds] with u hu using hs2 u hu
    have h1 := (hsat.pow 2).deriv
    have h2 : deriv (fun u => s u ^ 2) 0 = deriv q 0 := hev.deriv_eq
    have h3 : deriv (fun u => s u ^ 2) 0 = ((2 : ℕ) : ℂ) * s 0 ^ (2 - 1) * deriv s 0 := h1
    rw [h2, hs0] at h3
    rw [h3]
    simp
  -- `v = 1/s = 1 + w t(w)`
  set v : ℂ → ℂ := fun u => (s u)⁻¹ with hvdef
  have hvd : DifferentiableOn ℂ v (ball 0 1) := hsd.inv hsne
  have hv0 : v 0 = 1 := by simp [hvdef, hs0]
  have hvat : HasDerivAt v (-deriv s 0 / s 0 ^ 2) 0 := hsat.inv (by rw [hs0]; exact one_ne_zero)
  set t := dslope v 0 with htdef
  have htd : DifferentiableOn ℂ t (ball 0 1) := (Complex.differentiableOn_dslope hnhds).mpr hvd
  have hvt : ∀ u, v u = 1 + u * t u := fun u => by
    have := sub_smul_dslope v 0 u
    simp only [sub_zero, smul_eq_mul, hv0] at this
    rw [this.symm.symm]
    ring
  have ht0 : t 0 = -(deriv q 0 / 2) := by
    rw [htdef, dslope_same, hvat.deriv, hs0, hs']
    simp
  -- the exterior map: `h(u) = u t(u²)`
  set hh : ℂ → ℂ := fun u => u * t (u ^ 2) with hhdef
  have hsqmem : ∀ u ∈ ball (0 : ℂ) 1, u ^ 2 ∈ ball (0 : ℂ) 1 := fun u hu => by
    have hu1 : ‖u‖ < 1 := by simpa using hu
    have : ‖u‖ ^ 2 < 1 := by nlinarith [norm_nonneg u]
    simpa using this
  have hhd : DifferentiableOn ℂ hh (ball 0 1) := by
    refine differentiableOn_id.mul ?_
    exact htd.comp (differentiableOn_id.pow 2) hsqmem
  have hhder : deriv hh 0 = t 0 := by
    have htat : HasDerivAt t (deriv t (0 ^ 2)) (0 ^ 2) := by
      have h00 : (0 : ℂ) ^ 2 = 0 := by norm_num
      rw [h00]
      exact ((htd 0 h0mem).differentiableAt hnhds).hasDerivAt
    have h1 : HasDerivAt (fun u : ℂ => t (u ^ 2)) (deriv t (0 ^ 2) * (((2 : ℕ) : ℂ) * 0 ^ (2 - 1))) 0 :=
      htat.comp (h := fun u : ℂ => u ^ 2) (0 : ℂ) (hasDerivAt_pow 2 (0 : ℂ))
    have h2 : HasDerivAt hh (1 * t (0 ^ 2) + 0 * (deriv t (0 ^ 2) * (((2 : ℕ) : ℂ) * 0 ^ (2 - 1)))) 0 :=
      (hasDerivAt_id (0 : ℂ)).mul h1
    rw [h2.deriv]
    simp
  -- the identity `F · g = 1`
  have hFg : ∀ u : ℂ, u ≠ 0 → u ∈ ball (0 : ℂ) 1 → (u⁻¹ + hh u) * (u * s (u ^ 2)) = 1 := by
    intro u hu0 hu
    have hsu := hsne _ (hsqmem u hu)
    have hvu := hvt (u ^ 2)
    have hvs : v (u ^ 2) * s (u ^ 2) = 1 := by simp [hvdef, hsu]
    rw [hvu] at hvs
    simp only [hhdef]
    field_simp
    linear_combination hvs
  -- injectivity on the exterior
  have hinj : InjOn (fun z : ℂ => z + hh z⁻¹) {z : ℂ | 1 < ‖z‖} := by
    intro z1 hz1 z2 hz2 heq
    have hz1' : 1 < ‖z1‖ := hz1
    have hz2' : 1 < ‖z2‖ := hz2
    have hz10 : z1 ≠ 0 := norm_pos_iff.mp (by linarith)
    have hz20 : z2 ≠ 0 := norm_pos_iff.mp (by linarith)
    set u1 := z1⁻¹ with hu1
    set u2 := z2⁻¹ with hu2
    have hu10 : u1 ≠ 0 := inv_ne_zero hz10
    have hu20 : u2 ≠ 0 := inv_ne_zero hz20
    have hm1 : u1 ∈ ball (0 : ℂ) 1 := by
      simp only [mem_ball, dist_zero_right, hu1, norm_inv]
      exact inv_lt_one_of_one_lt₀ hz1'
    have hm2 : u2 ∈ ball (0 : ℂ) 1 := by
      simp only [mem_ball, dist_zero_right, hu2, norm_inv]
      exact inv_lt_one_of_one_lt₀ hz2'
    have hF1 := hFg u1 hu10 hm1
    have hF2 := hFg u2 hu20 hm2
    have hz1u : u1⁻¹ = z1 := by rw [hu1, inv_inv]
    have hz2u : u2⁻¹ = z2 := by rw [hu2, inv_inv]
    rw [hz1u] at hF1
    rw [hz2u] at hF2
    have heq' : z1 + hh u1 = z2 + hh u2 := heq
    -- `g(u₁) = g(u₂)`
    have hgeq : u1 * s (u1 ^ 2) = u2 * s (u2 ^ 2) := by
      have hne1 : z1 + hh u1 ≠ 0 := left_ne_zero_of_mul_eq_one hF1
      have h1 : u1 * s (u1 ^ 2) = (z1 + hh u1)⁻¹ := eq_inv_of_mul_eq_one_right hF1
      have h2 : u2 * s (u2 ^ 2) = (z2 + hh u2)⁻¹ := eq_inv_of_mul_eq_one_right hF2
      rw [h1, h2, heq']
    -- `g² = G(u²)`
    have hgsq : ∀ u ∈ ball (0 : ℂ) 1, (u * s (u ^ 2)) ^ 2 = G (u ^ 2) := by
      intro u hu
      rw [mul_pow, hs2 _ (hsqmem u hu), hGq _ (hsqmem u hu)]
    have hGeq : G (u1 ^ 2) = G (u2 ^ 2) := by
      rw [← hgsq u1 hm1, ← hgsq u2 hm2, hgeq]
    have hsqeq : u1 ^ 2 = u2 ^ 2 := hGinj (hsqmem u1 hm1) (hsqmem u2 hm2) hGeq
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsqeq with hsame | hneg
    · have : z1 = z2 := by
        rw [← hz1u, ← hz2u, hsame]
      exact this
    · exfalso
      have hg0 : u1 * s (u1 ^ 2) = -(u1 * s (u1 ^ 2)) := by
        have hsq' : u1 ^ 2 = u2 ^ 2 := hsqeq
        calc u1 * s (u1 ^ 2) = u2 * s (u2 ^ 2) := hgeq
          _ = -u1 * s (u1 ^ 2) := by rw [← hsq', hneg]; simp
          _ = -(u1 * s (u1 ^ 2)) := by ring
      have hgz : u1 * s (u1 ^ 2) = 0 := by
        have h2 : (2 : ℂ) * (u1 * s (u1 ^ 2)) = 0 := by linear_combination hg0
        simpa using h2
      rw [hgz, mul_zero] at hF1
      exact zero_ne_one hF1
  have harea := area_b1 hhd hinj
  rw [hhder, ht0, norm_neg] at harea
  rw [hA2]
  have hn : ‖deriv q 0 / 2‖ = ‖deriv q 0‖ / 2 := by simp
  rw [hn] at harea
  linarith

end ClassS

section Transform

variable {G : ℂ → ℂ} {w : ℂ}

lemma omitted_ne_zero (hG : InClassS G) (hw : ∀ z ∈ disk, G z ≠ w) : w ≠ 0 := by
  intro hzero
  exact hw 0 (mem_ball_self one_pos) (by rw [hG.2.1, hzero])

/-- The denominator of the Koebe transform. -/
lemma koebeDen_ne_zero (hw0 : w ≠ 0) (hw : ∀ z ∈ disk, G z ≠ w) {z : ℂ} (hz : z ∈ disk) :
    1 - G z * w⁻¹ ≠ 0 := by
  intro hzero
  apply hw z hz
  field_simp at hzero
  linear_combination -hzero

/-- The derivative of the Koebe transform `G/(1 - G/w)` is `G'/(1 - G/w)²`. -/
lemma koebeTransform_hasDerivAt (hG : InClassS G) (hw0 : w ≠ 0) (hw : ∀ z ∈ disk, G z ≠ w) {z : ℂ}
    (hz : z ∈ disk) :
    HasDerivAt (fun z => G z / (1 - G z * w⁻¹)) (deriv G z / (1 - G z * w⁻¹) ^ 2) z := by
  have hd : HasDerivAt G (deriv G z) z := (inClassS_differentiableAt hG hz).hasDerivAt
  have hden : HasDerivAt (fun z => 1 - G z * w⁻¹) (-(deriv G z * w⁻¹)) z := by
    simpa using (hd.mul_const w⁻¹).const_sub 1
  have hne := koebeDen_ne_zero hw0 hw hz
  have hdiv := hd.div hden hne
  convert hdiv using 1
  field_simp
  ring

/-- The Koebe transform of `G ∈ 𝒮` by an omitted value is in `𝒮`. -/
lemma koebeTransform_inClassS (hG : InClassS G) (hw : ∀ z ∈ disk, G z ≠ w) :
    InClassS (fun z => G z / (1 - G z * w⁻¹)) := by
  have hw0 := omitted_ne_zero hG hw
  have h0mem : (0 : ℂ) ∈ disk := mem_ball_self one_pos
  refine ⟨⟨fun z hz => (koebeTransform_hasDerivAt hG hw0 hw hz).differentiableAt.differentiableWithinAt, ?_⟩,
    ?_, ?_⟩
  · intro a ha b hb hab
    have hna := koebeDen_ne_zero hw0 hw ha
    have hnb := koebeDen_ne_zero hw0 hw hb
    simp only at hab
    rw [div_eq_div_iff hna hnb] at hab
    have : G a = G b := by linear_combination hab
    exact hG.1.2 ha hb this
  · simp [hG.2.1]
  · rw [(koebeTransform_hasDerivAt hG hw0 hw h0mem).deriv, hG.2.1, hG.2.2]
    simp

/-- The second derivative at `0` of the Koebe transform. -/
lemma koebeTransform_deriv_deriv (hG : InClassS G) (hw0 : w ≠ 0) (hw : ∀ z ∈ disk, G z ≠ w) :
    deriv (deriv fun z => G z / (1 - G z * w⁻¹)) 0 = deriv (deriv G) 0 + 2 * w⁻¹ := by
  have h0mem : (0 : ℂ) ∈ disk := mem_ball_self one_pos
  have hnhds : disk ∈ 𝓝 (0 : ℂ) := ball_mem_nhds _ one_pos
  have hev : (deriv fun z => G z / (1 - G z * w⁻¹)) =ᶠ[𝓝 0]
      fun z => deriv G z / (1 - G z * w⁻¹) ^ 2 := by
    filter_upwards [hnhds] with z hz using (koebeTransform_hasDerivAt hG hw0 hw hz).deriv
  rw [hev.deriv_eq]
  have hd : HasDerivAt G (deriv G 0) 0 := (inClassS_differentiableAt hG h0mem).hasDerivAt
  have hd2 : HasDerivAt (deriv G) (deriv (deriv G) 0) 0 :=
    ((hG.1.1.deriv isOpen_ball 0 h0mem).differentiableAt hnhds).hasDerivAt
  have hden : HasDerivAt (fun z => 1 - G z * w⁻¹) (-(deriv G 0 * w⁻¹)) 0 := by
    simpa using (hd.mul_const w⁻¹).const_sub 1
  have hden0 : (1 - G 0 * w⁻¹) = 1 := by simp [hG.2.1]
  have hsq : HasDerivAt (fun z => (1 - G z * w⁻¹) ^ 2)
      (((2 : ℕ) : ℂ) * (1 - G 0 * w⁻¹) ^ (2 - 1) * (-(deriv G 0 * w⁻¹))) 0 := hden.pow 2
  have hne : (1 - G 0 * w⁻¹) ^ 2 ≠ 0 := by rw [hden0]; simp
  have hdiv : HasDerivAt (fun z => deriv G z / (1 - G z * w⁻¹) ^ 2) _ 0 := hd2.div hsq hne
  rw [hdiv.deriv, hden0, hG.2.2]
  simp only [one_pow, mul_one, div_one, one_mul]
  norm_num

end Transform

/-- **Omitted values, coefficient form**: if `G ∈ 𝒮` omits `w` on the disk, then `|a₂ + 1/w| ≤ 2`. (`w ≠ 0` holds
automatically, since `G 0 = 0` and `0 ∈ disk`.) -/
theorem koebe_omit {G : ℂ → ℂ} (hG : InClassS G) {w : ℂ} (hw : ∀ z ∈ disk, G z ≠ w) :
    ‖deriv (deriv G) 0 / 2 + w⁻¹‖ ≤ 2 := by
  have hw0 := omitted_ne_zero hG hw
  have hb := bieberbach_a2 (koebeTransform_inClassS hG hw)
  rw [koebeTransform_deriv_deriv hG hw0 hw] at hb
  have hval : (deriv (deriv G) 0 + 2 * w⁻¹) / 2 = deriv (deriv G) 0 / 2 + w⁻¹ := by ring
  rwa [hval] at hb

/-- **Two omitted values**: if `G ∈ 𝒮` omits `w` and `w'`, then `|1/w - 1/w'| ≤ 4`. -/
theorem koebe_omit_pair {G : ℂ → ℂ} (hG : InClassS G) {w w' : ℂ} (hw : ∀ z ∈ disk, G z ≠ w)
    (hw' : ∀ z ∈ disk, G z ≠ w') : ‖w⁻¹ - w'⁻¹‖ ≤ 4 := by
  have h1 := koebe_omit hG hw
  have h2 := koebe_omit hG hw'
  have heq : w⁻¹ - w'⁻¹ = (deriv (deriv G) 0 / 2 + w⁻¹) - (deriv (deriv G) 0 / 2 + w'⁻¹) := by ring
  rw [heq]
  linarith [norm_sub_le (deriv (deriv G) 0 / 2 + w⁻¹) (deriv (deriv G) 0 / 2 + w'⁻¹)]

/-- **Koebe's one-quarter theorem, omitted-value form** (Koebe 1907, Bieberbach 1916). -/
theorem koebe_quarter {G : ℂ → ℂ} (hG : InClassS G) {w : ℂ} (hw : ∀ z ∈ disk, G z ≠ w) : 1 / 4 ≤ ‖w‖ := by
  have hw0 := omitted_ne_zero hG hw
  have h1 := koebe_omit hG hw
  have h2 := bieberbach_a2 hG
  have heq : w⁻¹ = (deriv (deriv G) 0 / 2 + w⁻¹) - deriv (deriv G) 0 / 2 := by ring
  have h3 : ‖w⁻¹‖ ≤ 4 := by
    rw [heq]
    linarith [norm_sub_le (deriv (deriv G) 0 / 2 + w⁻¹) (deriv (deriv G) 0 / 2)]
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  rw [norm_inv, inv_le_comm₀ hpos (by norm_num)] at h3
  linarith

/-- **Koebe's one-quarter theorem, covering form**: the image of the disk contains the disk of radius `1/4`. -/
theorem koebe_quarter_cover {G : ℂ → ℂ} (hG : InClassS G) : ball (0 : ℂ) (1 / 4) ⊆ G '' disk := by
  intro w hw
  by_contra hnot
  have hom : ∀ z ∈ disk, G z ≠ w := fun z hz heq => hnot ⟨z, hz, heq⟩
  have h1 := koebe_quarter hG hom
  have h2 : ‖w‖ < 1 / 4 := by simpa using hw
  linarith

section General

variable {g : ℂ → ℂ}

/-- The normalization of a univalent map with `g(0) = 0`, `g'(0) ≠ 0`. -/
lemma normalized_inClassS (hg : IsUnivalentOn g disk) (h0 : g 0 = 0) (hne : deriv g 0 ≠ 0) :
    InClassS (fun z => g z / deriv g 0) := by
  refine ⟨⟨hg.1.div_const _, ?_⟩, by simp [h0], ?_⟩
  · intro a ha b hb hab
    simp only at hab
    exact hg.2 ha hb ((div_left_inj' hne).mp hab)
  · rw [deriv_div_const]
    exact div_self hne

/-- **Koebe without normalization**: `g` univalent on the disk, `g 0 = 0`, `g` omits `w`: then `|g'(0)| ≤ 4 |w|`. -/
theorem koebe_quarter_general (hg : IsUnivalentOn g disk) (h0 : g 0 = 0) {w : ℂ}
    (hw : ∀ z ∈ disk, g z ≠ w) : ‖deriv g 0‖ ≤ 4 * ‖w‖ := by
  by_cases hne : deriv g 0 = 0
  · rw [hne, norm_zero]
    positivity
  · have hom : ∀ z ∈ disk, g z / deriv g 0 ≠ w / deriv g 0 := fun z hz heq =>
      hw z hz ((div_left_inj' hne).mp heq)
    have h1 := koebe_quarter (normalized_inClassS hg h0 hne) hom
    have hpos : 0 < ‖deriv g 0‖ := norm_pos_iff.mpr hne
    rw [norm_div, le_div_iff₀ hpos] at h1
    linarith

/-- **Two omitted values without normalization**: `|g'(0)| |1/w - 1/w'| ≤ 4`. -/
theorem koebe_omit_pair_general (hg : IsUnivalentOn g disk) (h0 : g 0 = 0) {w w' : ℂ}
    (hw : ∀ z ∈ disk, g z ≠ w) (hw' : ∀ z ∈ disk, g z ≠ w') :
    ‖deriv g 0‖ * ‖w⁻¹ - w'⁻¹‖ ≤ 4 := by
  by_cases hne : deriv g 0 = 0
  · rw [hne, norm_zero, zero_mul]
    norm_num
  · have hom : ∀ z ∈ disk, g z / deriv g 0 ≠ w / deriv g 0 := fun z hz heq =>
      hw z hz ((div_left_inj' hne).mp heq)
    have hom' : ∀ z ∈ disk, g z / deriv g 0 ≠ w' / deriv g 0 := fun z hz heq =>
      hw' z hz ((div_left_inj' hne).mp heq)
    have h1 := koebe_omit_pair (normalized_inClassS hg h0 hne) hom hom'
    have heq : (w / deriv g 0)⁻¹ - (w' / deriv g 0)⁻¹ = deriv g 0 * (w⁻¹ - w'⁻¹) := by
      rw [inv_div, inv_div]
      ring
    rwa [heq, norm_mul] at h1

end General

/-! ### Sanity rows: the hypotheses are satisfiable and the constants are best possible -/

/-- `h(u) = u` gives `F(z) = z + 1/z`, injective on `|z| > 1`, with `b₁ = 1`: `area_b1` is sharp. -/
theorem area_b1_sharp :
    DifferentiableOn ℂ (fun u : ℂ => u) disk ∧
      InjOn (fun z : ℂ => z + (fun u : ℂ => u) z⁻¹) {z : ℂ | 1 < ‖z‖} ∧
      ‖deriv (fun u : ℂ => u) 0‖ = 1 := by
  refine ⟨differentiableOn_id, ?_, by simp⟩
  intro a ha b hb hab
  have ha' : 1 < ‖a‖ := ha
  have hb' : 1 < ‖b‖ := hb
  have ha0 : a ≠ 0 := norm_pos_iff.mp (by linarith)
  have hb0 : b ≠ 0 := norm_pos_iff.mp (by linarith)
  simp only at hab
  have hprod : (a - b) * (a * b - 1) = 0 := by
    field_simp at hab
    linear_combination hab
  rcases mul_eq_zero.mp hprod with h1 | h2
  · exact sub_eq_zero.mp h1
  · exfalso
    have hab1 : a * b = 1 := sub_eq_zero.mp h2
    have hn : ‖a‖ * ‖b‖ = 1 := by rw [← norm_mul, hab1, norm_one]
    nlinarith

/-- The derivative of the Koebe function. -/
lemma koebeFn_hasDerivAt {z : ℂ} (hz : z ≠ 1) :
    HasDerivAt (fun z : ℂ => z / (1 - z) ^ 2) ((1 + z) / (1 - z) ^ 3) z := by
  have hne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hsub : HasDerivAt (fun z : ℂ => 1 - z) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub 1
  have hden : HasDerivAt (fun z : ℂ => (1 - z) ^ 2)
      (((2 : ℕ) : ℂ) * (1 - z) ^ (2 - 1) * (-1)) z := hsub.pow 2
  have hdiv : HasDerivAt (fun z : ℂ => z / (1 - z) ^ 2)
      ((1 * (1 - z) ^ 2 - z * (((2 : ℕ) : ℂ) * (1 - z) ^ (2 - 1) * (-1))) / ((1 - z) ^ 2) ^ 2) z :=
    (hasDerivAt_id z).div hden (pow_ne_zero 2 hne)
  have hval : (1 * (1 - z) ^ 2 - z * (((2 : ℕ) : ℂ) * (1 - z) ^ (2 - 1) * (-1))) / ((1 - z) ^ 2) ^ 2 =
      (1 + z) / (1 - z) ^ 3 := by
    simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat]
    field_simp
    ring
  rwa [hval] at hdiv

lemma ne_one_of_mem_disk {z : ℂ} (hz : z ∈ disk) : z ≠ 1 := by
  rintro rfl
  simp at hz

/-- **Sanity check of the constants**: the Koebe function `z/(1-z)²` is in `𝒮`, has `a₂ = 2`, and omits `-1/4`. -/
theorem koebe_function_sharp :
    InClassS (fun z : ℂ => z / (1 - z) ^ 2) ∧
      deriv (deriv (fun z : ℂ => z / (1 - z) ^ 2)) 0 / 2 = 2 ∧
      ∀ z ∈ disk, z / (1 - z) ^ 2 ≠ -(1 / 4 : ℂ) := by
  have hnhds : disk ∈ 𝓝 (0 : ℂ) := ball_mem_nhds _ one_pos
  have hd : ∀ z ∈ disk, HasDerivAt (fun z : ℂ => z / (1 - z) ^ 2) ((1 + z) / (1 - z) ^ 3) z :=
    fun z hz => koebeFn_hasDerivAt (ne_one_of_mem_disk hz)
  have hnorm : ∀ z ∈ disk, ‖z‖ < 1 := fun z hz => by simpa using hz
  refine ⟨⟨⟨fun z hz => (hd z hz).differentiableAt.differentiableWithinAt, ?_⟩, by simp, ?_⟩, ?_, ?_⟩
  · intro a ha b hb hab
    have hane : (1 : ℂ) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_one_of_mem_disk ha))
    have hbne : (1 : ℂ) - b ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_one_of_mem_disk hb))
    simp only at hab
    rw [div_eq_div_iff (pow_ne_zero 2 hane) (pow_ne_zero 2 hbne)] at hab
    have hprod : (a - b) * (1 - a * b) = 0 := by linear_combination hab
    rcases mul_eq_zero.mp hprod with h1 | h2
    · exact sub_eq_zero.mp h1
    · exfalso
      have hab1 : a * b = 1 := (sub_eq_zero.mp h2).symm
      have hn : ‖a‖ * ‖b‖ = 1 := by rw [← norm_mul, hab1, norm_one]
      nlinarith [hnorm a ha, hnorm b hb, norm_nonneg a, norm_nonneg b]
  · rw [(hd 0 (mem_ball_self one_pos)).deriv]
    simp
  · have hev : (deriv fun z : ℂ => z / (1 - z) ^ 2) =ᶠ[𝓝 0] fun z => (1 + z) / (1 - z) ^ 3 := by
      filter_upwards [hnhds] with z hz using (hd z hz).deriv
    rw [hev.deriv_eq]
    have hne : ((1 : ℂ) - 0) ^ 3 ≠ 0 := by simp
    have hnum : HasDerivAt (fun z : ℂ => 1 + z) 1 (0 : ℂ) := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_add 1
    have hsub : HasDerivAt (fun z : ℂ => 1 - z) (-1) (0 : ℂ) := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_sub 1
    have hden : HasDerivAt (fun z : ℂ => (1 - z) ^ 3)
        (((3 : ℕ) : ℂ) * (1 - 0) ^ (3 - 1) * (-1)) (0 : ℂ) := hsub.pow 3
    have hdiv : HasDerivAt (fun z : ℂ => (1 + z) / (1 - z) ^ 3) _ (0 : ℂ) := hnum.div hden hne
    rw [hdiv.deriv]
    norm_num
  · intro z hz heq
    have hzne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_one_of_mem_disk hz))
    rw [div_eq_iff (pow_ne_zero 2 hzne)] at heq
    have hsq : (1 + z) ^ 2 = 0 := by linear_combination 4 * heq
    have hz1 : z = -1 := by
      have := pow_eq_zero_iff (two_ne_zero) |>.mp hsq
      linear_combination this
    have := hnorm z hz
    rw [hz1, norm_neg, norm_one] at this
    exact lt_irrefl _ this

end Smale.Koebe
