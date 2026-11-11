/-
Smale/P030/Contract.lean — `Kstar = 4`. The assemblies `pair_W`, `pair_F`, `exists_poly_gt`,
`kstar_eq_four` are proved from `Bridge`, `EE`, `Strip`, `WSide`, `Params`, and the upper bound `K* ≤ 4` from `CFLBound`.
No hypothesis on any classical fact appears.
The reduction from a domain to a pair of functions on the disc, together with the bridge, is `bridge_pair`.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import Smale.P030.Bridge
public import Smale.P030.Defs
public import Smale.P030.EE
public import Smale.P030.Params
public import Smale.P030.Strip
public import Smale.P030.WSide
public import Smale.Proofs.CFLBound

@[expose] public section

namespace Smale.P030

open Polynomial Complex Metric Set Filter Topology

/-! ### The `W` side: assembly -/

theorem combDisc_mapsTo {lam : ℝ} (h : 0 ≤ lam) (xs : Finset ℝ) {t : ℂ} (ht : t ∈ disk) : combDisc lam xs t ∈ disk :=
  cayleyInv_mem (comb_im_pos h xs (cayley_im_pos ht))

theorem combDisc_injOn {lam : ℝ} (h : 0 ≤ lam) (xs : Finset ℝ) : InjOn (combDisc lam xs) disk := by
  intro a ha b hb hab
  have h1 := cayleyInv_injOn (comb_im_pos h xs (cayley_im_pos ha)) (comb_im_pos h xs (cayley_im_pos hb)) hab
  exact cayley_injOn ha hb (comb_injOn h xs (cayley_im_pos ha) (cayley_im_pos hb) h1)

theorem combDisc_differentiableOn {lam : ℝ} (h : 0 ≤ lam) (xs : Finset ℝ) : DifferentiableOn ℂ (combDisc lam xs) disk := by
  have h1 : DifferentiableOn ℂ (fun t => comb lam xs (cayley t)) disk :=
    (comb_differentiableOn lam xs).comp cayley_differentiableOn fun t ht => cayley_im_pos ht
  exact cayleyInv_differentiableOn.comp h1 fun t ht => comb_im_pos h xs (cayley_im_pos ht)

/-- **The `W` of the pair.** Univalent on the disk, `W(0) = 0`, `|W'(0)| ≥ 1 - ε`, `|W| ≤ 2/(1 - δ)²` (a bound that does
not see `P`), and near each `b ∈ P`, `|W| < (1 + ε)/(1 + δ)²`, where `1/(1 + δ)²` is the value of `k_δ` at the point `1`. -/
theorem pair_W {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (P : Finset ℂ) (hP : ∀ b ∈ P, ‖b‖ = 1 ∧ b ≠ 1) :
    ∃ W : ℂ → ℂ, IsUnivalentOn W disk ∧ W 0 = 0 ∧ 1 - ε ≤ ‖deriv W 0‖ ∧ (∀ t ∈ disk, ‖W t‖ ≤ 2 / (1 - δ) ^ 2) ∧
      ∀ b ∈ P, ∃ ρ : ℝ, 0 < ρ ∧ ∀ t ∈ disk, ‖t - b‖ < ρ → ‖W t‖ < (1 + ε) / (1 + δ) ^ 2 := by
  classical
  have hrpos : 0 < 1 / (1 + δ) ^ 2 := by positivity
  set r : ℝ := 1 / (1 + δ) ^ 2 with hr
  set e₀ : ℝ := min (ε * r / 2) (min ε 1 / 4) with he₀
  have he₀pos : 0 < e₀ := by
    have : 0 < min ε 1 := lt_min hε one_pos
    exact lt_min (by positivity) (by positivity)
  have he₀a : e₀ ≤ ε * r / 2 := min_le_left _ _
  have he₀b : e₀ ≤ min ε 1 / 4 := min_le_right _ _
  obtain ⟨e₁, he₁, he₁1, hnear0⟩ := koebeD_near_zero δ he₀pos
  set xs : Finset ℝ := P.image fun b => (cayley b).re with hxs
  obtain ⟨lam, hlam, hφ0, hφ'⟩ := combDisc_small xs (lt_min he₁ he₀pos)
  have hφ0a : ‖combDisc lam xs 0‖ < e₁ := hφ0.trans_le (min_le_left _ _)
  have hφ'a : ‖deriv (combDisc lam xs) 0 - 1‖ < e₀ := hφ'.trans_le (min_le_right _ _)
  set φ : ℂ → ℂ := combDisc lam xs with hφdef
  have h0mem : (0 : ℂ) ∈ disk := mem_ball_self one_pos
  have hφmem : ∀ t ∈ disk, φ t ∈ disk := fun t ht => combDisc_mapsTo hlam.le xs ht
  have hφd : DifferentiableOn ℂ φ disk := combDisc_differentiableOn hlam.le xs
  have hkd := koebeD_differentiableOn hδ0.le hδ1
  obtain ⟨hk0, hk'⟩ := hnear0 _ hφ0a
  refine ⟨fun t => koebeD δ (φ t) - koebeD δ (φ 0), ⟨(hkd.comp hφd hφmem).sub_const _, ?_⟩, by simp, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    have h1 : koebeD δ (φ a) = koebeD δ (φ b) := by simpa using hab
    exact combDisc_injOn hlam.le xs ha hb (koebeD_injOn hδ0.le hδ1 (hφmem a ha) (hφmem b hb) h1)
  · have hφat : HasDerivAt φ (deriv φ 0) 0 := (hφd.differentiableAt (isOpen_ball.mem_nhds h0mem)).hasDerivAt
    have hd := ((koebeD_hasDerivAt hδ0.le hδ1 (hφmem 0 h0mem)).comp (0 : ℂ) hφat).sub_const (koebeD δ (φ 0))
    have hderiv : deriv (fun t => koebeD δ (φ t) - koebeD δ (φ 0)) 0 =
        (1 - δ * φ 0) / (1 + δ * φ 0) ^ 3 * deriv φ 0 := hd.deriv
    rw [hderiv]
    set A : ℂ := (1 - δ * φ 0) / (1 + δ * φ 0) ^ 3 with hA
    set B : ℂ := deriv φ 0 with hB
    have hm : min ε 1 ≤ ε := min_le_left _ _
    have hm1 : min ε 1 ≤ 1 := min_le_right _ _
    have hm0 : 0 < min ε 1 := lt_min hε one_pos
    have hAe : ‖A - 1‖ < min ε 1 / 4 := hk'.trans_le he₀b
    have hBe : ‖B - 1‖ < min ε 1 / 4 := hφ'a.trans_le he₀b
    have hprod : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by ring
    have hle : ‖A * B - 1‖ ≤ ‖A - 1‖ * ‖B - 1‖ + ‖A - 1‖ + ‖B - 1‖ := by
      rw [hprod]
      refine (norm_add_le _ _).trans ?_
      refine add_le_add_left ((norm_add_le _ _).trans ?_) _
      exact add_le_add_left (norm_mul_le _ _) _
    have htri : 1 - ‖A * B - 1‖ ≤ ‖A * B‖ := by
      have h := norm_sub_norm_le (1 : ℂ) (1 - A * B)
      rw [sub_sub_cancel, norm_one, norm_sub_rev] at h
      exact h
    have hprodle : ‖A - 1‖ * ‖B - 1‖ ≤ (min ε 1 / 4) * (min ε 1 / 4) :=
      mul_le_mul hAe.le hBe.le (norm_nonneg _) (by positivity)
    nlinarith
  · intro t ht
    have h1 := koebeD_norm_le hδ0.le hδ1 (hφmem t ht)
    have h2 := koebeD_norm_le hδ0.le hδ1 (hφmem 0 h0mem)
    have h3 : ‖koebeD δ (φ t) - koebeD δ (φ 0)‖ ≤ ‖koebeD δ (φ t)‖ + ‖koebeD δ (φ 0)‖ := norm_sub_le _ _
    have h4 : (2 : ℝ) / (1 - δ) ^ 2 = 1 / (1 - δ) ^ 2 + 1 / (1 - δ) ^ 2 := by ring
    show ‖koebeD δ (φ t) - koebeD δ (φ 0)‖ ≤ _
    linarith
  · intro b hb
    obtain ⟨hb1, hb2⟩ := hP b hb
    set x : ℝ := (cayley b).re with hx
    have hxmem : x ∈ xs := Finset.mem_image.2 ⟨b, hb, rfl⟩
    have hcb : cayley b = (x : ℂ) := Complex.ext (by simp [hx]) (by simpa using cayley_unit_real hb1 hb2)
    obtain ⟨e₂, he₂, hk1⟩ := koebeD_near_one hδ0.le (by positivity : 0 < ε * r / 2)
    obtain ⟨L, hL⟩ := cayleyInv_near_one he₂
    obtain ⟨ρ₁, hρ₁, hlarge⟩ := comb_large hlam hxmem L
    obtain ⟨ρ, hρ, hcont⟩ := Metric.continuousAt_iff.1 (cayley_continuousAt hb2) ρ₁ hρ₁
    refine ⟨ρ, hρ, fun t ht htb => ?_⟩
    have hdist : dist (cayley t) (cayley b) < ρ₁ := hcont (by rwa [dist_eq_norm])
    rw [dist_eq_norm, hcb] at hdist
    have hζ := cayley_im_pos ht
    have hG : L < ‖comb lam xs (cayley t)‖ := hlarge _ hζ hdist
    have hφ1 : ‖φ t - 1‖ < e₂ := hL _ (comb_im_pos hlam.le xs hζ) hG
    have hkt := hk1 _ hφ1
    have htri : ‖koebeD δ (φ t) - koebeD δ (φ 0)‖ ≤ ‖koebeD δ (φ t)‖ + ‖koebeD δ (φ 0)‖ := norm_sub_le _ _
    have hsum : (1 + ε) / (1 + δ) ^ 2 = r + ε * r := by rw [hr]; ring
    show ‖koebeD δ (φ t) - koebeD δ (φ 0)‖ < _
    rw [hsum]
    have hk0' : ‖koebeD δ (φ 0)‖ < ε * r / 2 := hk0.trans_le he₀a
    linarith

/-! ### The `F` side: assembly -/

/-- **The `F` of the pair.** `M` first; then, for every `η`, an `F` with `F' ≠ 0` and `|F'(0)| ≤ 1 + ε`, large on a collar of
the circle except where `t^M` is within `η` of `-1`, and there still at least `1 - ε`. -/
theorem pair_F {ε R : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ η : ℝ, 0 < η → ∃ F : ℂ → ℂ, DifferentiableOn ℂ F disk ∧ F 0 = 0 ∧
      (∀ t ∈ disk, deriv F t ≠ 0) ∧ ‖deriv F 0‖ ≤ 1 + ε ∧
      ∃ r₀ : ℝ, r₀ < 1 ∧ ∀ t : ℂ, r₀ ≤ ‖t‖ → ‖t‖ < 1 → R ≤ ‖F t‖ ∨ (1 - ε ≤ ‖F t‖ ∧ ‖t ^ M + 1‖ < η) := by
  obtain ⟨M, a, hM, ha, h1, h2, h3, h4⟩ := exists_params hε R
  have hM1 : 1 ≤ M := by omega
  have hMne : M ≠ 0 := by omega
  have hapos : 0 < a := by linarith
  have hcpos : 0 < 2 * a := by linarith
  have hcne : (2 * a : ℝ) ≠ 0 := hcpos.ne'
  refine ⟨M, hM1, fun η hη => ?_⟩
  obtain ⟨n, C, hCn, hC1, hC2, hC3, hC4⟩ := exists_C hapos hcpos hM1 hε hη
  have hC0 : 0 < C := by linarith
  have hyd := stripY_differentiableOn hapos hC0
  obtain ⟨ξ, hξd, hξ0, hξpow, hξ', hξ'0⟩ := exists_root_transform hM1 hyd (stripY_zero hapos hC0)
    (fun u hu => stripY_deriv_ne_zero hapos hC0 hu) (fun u hu h0 => stripY_ne_zero hapos hC0 hu h0)
  have hpowmem : ∀ t ∈ disk, t ^ M ∈ disk := by
    intro t ht
    have ht1 : ‖t‖ < 1 := by simpa using ht
    have : ‖t ^ M‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) ht1 hMne
    simpa using this
  have hξat : ∀ t ∈ disk, HasDerivAt ξ (deriv ξ t) t := fun t ht =>
    (hξd.differentiableAt (isOpen_ball.mem_nhds ht)).hasDerivAt
  have hFat : ∀ t ∈ disk, HasDerivAt (fun t => EE M (2 * a) (ξ t))
      (Complex.exp (ξ t ^ M) * (1 - ξ t ^ M / (2 * a : ℝ)) * deriv ξ t) t := fun t ht =>
    (EE_hasDerivAt hM1 hcne (ξ t)).comp t (hξat t ht)
  have h0mem : (0 : ℂ) ∈ disk := mem_ball_self one_pos
  refine ⟨fun t => EE M (2 * a) (ξ t), fun t ht => (hFat t ht).differentiableAt.differentiableWithinAt, ?_, ?_, ?_, ?_⟩
  · simp only [hξ0, EE_zero]
  · intro t ht
    rw [(hFat t ht).deriv]
    refine mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) ?_) (hξ' t ht)
    intro h0
    have hmem := stripY_mem hapos hC0 (hpowmem t ht)
    have heq : ξ t ^ M = ((2 * a : ℝ) : ℂ) := by
      have hne : (((2 * a : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hcne
      field_simp at h0
      linear_combination -h0
    rw [hξpow t ht] at heq
    have hre := hmem.1
    rw [heq] at hre
    simp at hre
    linarith
  · rw [(hFat 0 h0mem).deriv, hξ0, zero_pow hMne]
    simp only [Complex.exp_zero, zero_div, sub_zero, mul_one, one_mul]
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) hMne).1 ?_
    rw [hξ'0]
    exact (stripY_deriv_zero hapos hC0).trans h3
  · obtain ⟨r, hr0, hr1, hK⟩ := stripT_collar hapos hC1
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    refine ⟨1 - (1 - r) / (2 * M), by
      have : 0 < (1 - r) / (2 * (M : ℝ)) := div_pos (by linarith) (by positivity)
      linarith, fun t ht1 ht2 => ?_⟩
    have htd : t ∈ disk := by simpa using ht2
    set u : ℂ := t ^ M with hu
    have hud := hpowmem t htd
    have huabs : r < ‖u‖ := by
      have hb := one_add_mul_le_pow (a := ‖t‖ - 1) (n := M) (by linarith [norm_nonneg t])
      have hb' : 1 + (M : ℝ) * (‖t‖ - 1) ≤ ‖t‖ ^ M := by simpa using hb
      have hM' : (M : ℝ) * (1 - ‖t‖) ≤ (1 - r) / 2 := by
        have hle : 1 - ‖t‖ ≤ (1 - r) / (2 * M) := by linarith
        calc (M : ℝ) * (1 - ‖t‖) ≤ M * ((1 - r) / (2 * M)) := mul_le_mul_of_nonneg_left hle hMpos.le
          _ = (1 - r) / 2 := by field_simp
      rw [hu, norm_pow]
      nlinarith
    have hmem := stripY_mem hapos hC0 hud
    have hroot : ξ t ^ M = stripY a C u := hξpow t htd
    have hT : stripT a C (stripY a C u) = u := stripT_stripY hapos hC0 hud
    by_cases hexit : a - 1 ≤ (stripY a C u).re
    · left
      exact norm_EE_exit hM ha h1 h2 (ξ t) (by rw [hroot]; exact hexit) (by rw [hroot]; exact hmem.1.le)
    · right
      have hexit' : (stripY a C u).re ≤ a - 1 := (not_le.1 hexit).le
      have hlow : (stripY a C u).re ≤ -C ∨ C - 1 / 2 ≤ |(stripY a C u).im| := by
        by_contra hcon
        push_neg at hcon
        have h5 := hK _ hcon.1.le hexit' hcon.2.le
        rw [hT] at h5
        linarith
      have hclose : ‖u + 1‖ < η := by
        have h6 := stripT_low hapos hC1 hmem hlow
        rw [hT] at h6
        exact h6.trans_lt hC4
      refine ⟨?_, hclose⟩
      rcases hlow with hl | hl
      · have hc1 : 1 ≤ 2 * a := by linarith
        have h7 := norm_EE_left hM hc1 hC1 (ξ t) (by rw [hroot]; exact hl) (by rw [hroot]; exact hmem.2.le)
        linarith
      · have h7 := norm_EE_cross hM hcpos hCn hC2 (ξ t) (by rw [hroot]; exact hl) (by rw [hroot]; exact hmem.2.le)
        linarith

/-! ### The pair and the bridge -/

/-- A point `t` with `‖t‖ < 1` away from all `M`-th roots of `-1` has `t^M` away from `-1`. -/
theorem exists_eta {M : ℕ} (hM : 1 ≤ M) (P : Finset ℂ) (hP : ∀ t : ℂ, t ^ M = -1 → t ∈ P) {ρ : ℂ → ℝ}
    (hρ : ∀ b ∈ P, 0 < ρ b) :
    ∃ η : ℝ, 0 < η ∧ ∀ t : ℂ, ‖t‖ < 1 → (∀ b ∈ P, ρ b ≤ ‖t - b‖) → η ≤ ‖t ^ M + 1‖ := by
  set K : Set ℂ := closedBall (0 : ℂ) 1 \ ⋃ b ∈ P, ball b (ρ b) with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).diff (isOpen_biUnion fun _ _ => isOpen_ball)
  have hcont : ContinuousOn (fun t : ℂ => ‖t ^ M + 1‖) K := by fun_prop
  have hpos : ∀ t ∈ K, (0 : ℝ) < ‖t ^ M + 1‖ := by
    intro t ht
    refine norm_pos_iff.2 fun h0 => ht.2 ?_
    have hb : t ∈ P := hP t (by linear_combination h0)
    exact mem_biUnion hb (mem_ball_self (hρ t hb))
  obtain ⟨η, hη, hlow⟩ := hKc.exists_forall_le' hcont hpos
  refine ⟨η, hη, fun t ht htb => hlow t ⟨by simpa using ht.le, ?_⟩⟩
  simp only [mem_iUnion, not_exists]
  intro b hb hmem
  have := htb b hb
  rw [mem_ball, dist_eq_norm] at hmem
  linarith

/-- For every `S` with `0 < S < 4`, a polynomial with `m(p) > S`. -/
theorem exists_poly_gt {S : ℝ} (hS0 : 0 < S) (hS : S < 4) : ∃ d : ℕ, 2 ≤ d ∧ ∃ p : ℂ[X], IsPd d p ∧ S < mval p := by
  classical
  set A : ℝ := max ((S + 4) / 2) 2 with hAdef
  have hA2 : 2 ≤ A := le_max_right _ _
  have hSA : S < A := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hA4 : A < 4 := max_lt (by linarith) (by norm_num)
  set δ : ℝ := Real.sqrt A - 1 with hδ
  have hsq : Real.sqrt A ^ 2 = A := Real.sq_sqrt (by linarith)
  have hsq0 : 0 ≤ Real.sqrt A := Real.sqrt_nonneg A
  have hδ0 : 0 < δ := by rw [hδ]; nlinarith
  have hδ1 : δ < 1 := by rw [hδ]; nlinarith
  have h1δ : (1 + δ) ^ 2 = A := by rw [hδ]; linarith [hsq, (by ring : (1 + (Real.sqrt A - 1)) ^ 2 = Real.sqrt A ^ 2)]
  set ε : ℝ := (A - S) / (8 * A) with hεdef
  have hApos : 0 < A := by linarith
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  have hε1 : ε ≤ 1 / 8 := by
    rw [hεdef, div_le_iff₀ (by positivity)]
    linarith
  set B₀ : ℝ := 2 / (1 - δ) ^ 2 with hB₀
  have hB₀pos : 0 < B₀ := div_pos two_pos (pow_pos (by linarith) 2)
  set R : ℝ := max 1 (A * B₀) with hR
  have hR1 : 1 ≤ R := le_max_left _ _
  have hRB : A * B₀ ≤ R := le_max_right _ _
  obtain ⟨M, hM, hF⟩ := pair_F (R := R) hε
  have hMne : M ≠ 0 := by omega
  -- the points, and `W` for them
  set P : Finset ℂ := (nthRoots M (-1 : ℂ)).toFinset with hPdef
  have hPmem : ∀ t : ℂ, t ∈ P ↔ t ^ M = -1 := fun t => by
    rw [hPdef, Multiset.mem_toFinset, mem_nthRoots (by omega)]
  have hP : ∀ b ∈ P, ‖b‖ = 1 ∧ b ≠ 1 := by
    intro b hb
    have hpow := (hPmem b).1 hb
    refine ⟨?_, ?_⟩
    · have h1 : ‖b‖ ^ M = 1 := by rw [← norm_pow, hpow, norm_neg, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hMne).1 h1
    · rintro rfl
      rw [one_pow] at hpow
      have := congrArg Complex.re hpow
      norm_num at this
  obtain ⟨W, hWu, hW0, hW1, hWB, hWnear⟩ := pair_W hδ0 hδ1 hε P hP
  choose! ρ hρ hρnear using hWnear
  obtain ⟨η, hη, hηlow⟩ := exists_eta hM P (fun t ht => (hPmem t).2 ht) hρ
  obtain ⟨F, hFd, hF0, hF', hF'0, r₀, hr₀, hFcol⟩ := hF η hη
  have h0mem : (0 : ℂ) ∈ disk := mem_ball_self one_pos
  have hF1ne : deriv F 0 ≠ 0 := hF' 0 h0mem
  have hW1ne : deriv W 0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hW1
    linarith
  -- the collar: `|F| ≥ ((1 - ε) A/(1 + ε)) |W|`
  have hcollar : ∀ t : ℂ, r₀ ≤ ‖t‖ → ‖t‖ < 1 → (1 - ε) * A / (1 + ε) * ‖W t‖ ≤ ‖F t‖ := by
    intro t ht1 ht2
    have htd : t ∈ disk := by simpa using ht2
    have hgpos : 0 < (1 - ε) * A / (1 + ε) := by
      apply div_pos (mul_pos (by linarith) hApos) (by linarith)
    have hgle : (1 - ε) * A / (1 + ε) ≤ A := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    by_cases hnear : ∃ b ∈ P, ‖t - b‖ < ρ b
    · obtain ⟨b, hb, hbt⟩ := hnear
      have hW := hρnear b hb t htd hbt
      rw [h1δ] at hW
      have hFlow : 1 - ε ≤ ‖F t‖ := by
        rcases hFcol t ht1 ht2 with h | h
        · linarith
        · exact h.1
      have hstep : (1 - ε) * A / (1 + ε) * ‖W t‖ ≤ (1 - ε) * A / (1 + ε) * ((1 + ε) / A) :=
        mul_le_mul_of_nonneg_left hW.le hgpos.le
      have heq : (1 - ε) * A / (1 + ε) * ((1 + ε) / A) = 1 - ε := by
        have : (1 + ε) ≠ 0 := by linarith
        field_simp
      linarith
    · push_neg at hnear
      have hbig := hηlow t ht2 hnear
      have hFhigh : R ≤ ‖F t‖ := by
        rcases hFcol t ht1 ht2 with h | h
        · exact h
        · linarith [h.2]
      have hWle := hWB t htd
      calc (1 - ε) * A / (1 + ε) * ‖W t‖ ≤ A * B₀ := mul_le_mul hgle hWle (norm_nonneg _) hApos.le
        _ ≤ R := hRB
        _ ≤ ‖F t‖ := hFhigh
  -- normalize and apply the bridge
  have hWnorm : InClassS (fun t => W t / deriv W 0) := by
    refine ⟨⟨hWu.1.div_const _, ?_⟩, by simp [hW0], ?_⟩
    · intro a ha b hb hab
      have : W a = W b := by
        have h := hab
        simp only at h
        exact (div_left_inj' hW1ne).1 h
      exact hWu.2 ha hb this
    · rw [deriv_div_const]
      exact div_self hW1ne
  have hGdiff : DifferentiableOn ℂ (fun t => F t / deriv F 0) disk := hFd.div_const _
  have hG' : ∀ t ∈ disk, deriv (fun t => F t / deriv F 0) t ≠ 0 := by
    intro t ht
    rw [deriv_div_const]
    exact div_ne_zero (hF' t ht) hF1ne
  have hGone : deriv (fun t => F t / deriv F 0) 0 = 1 := by
    rw [deriv_div_const]
    exact div_self hF1ne
  set A₁ : ℝ := A * (1 - ε) ^ 2 / (1 + ε) ^ 2 with hA₁
  have hF'pos : 0 < ‖deriv F 0‖ := norm_pos_iff.2 hF1ne
  have hW'pos : 0 < ‖deriv W 0‖ := norm_pos_iff.2 hW1ne
  have hratio : S < A₁ := by
    have h1ε : 0 < 1 + ε := by linarith
    rw [hA₁, lt_div_iff₀ (by positivity)]
    have hkey : A * (A - S) = 8 * A * ε * A := by
      rw [hεdef]
      field_simp
    have hAε : 8 * A * ε = A - S := by
      rw [hεdef]
      field_simp
    nlinarith [mul_pos hApos hε, mul_pos hε hε, mul_pos (mul_pos hApos hε) hε]
  refine bridge_pair hWnorm hGdiff (by simp [hF0]) hGone hG' hS0 hratio hr₀ fun t ht1 ht2 => ?_
  have h1ε : 0 < 1 + ε := by linarith
  have hc := hcollar t ht1 ht2
  simp only [norm_div]
  rw [le_div_iff₀ hF'pos]
  have hWn : ‖W t‖ / ‖deriv W 0‖ * ‖deriv W 0‖ = ‖W t‖ := div_mul_cancel₀ _ hW'pos.ne'
  have hWdiv : ‖W t‖ / ‖deriv W 0‖ ≤ ‖W t‖ / (1 - ε) :=
    div_le_div_of_nonneg_left (norm_nonneg _) (by linarith) hW1
  have hgoal : A₁ * (‖W t‖ / ‖deriv W 0‖) ≤ A₁ * (‖W t‖ / (1 - ε)) :=
    mul_le_mul_of_nonneg_left hWdiv (by positivity)
  have hA₁eq : A₁ * (‖W t‖ / (1 - ε)) = (1 - ε) * A / (1 + ε) * ‖W t‖ / (1 + ε) := by
    have hne : (1 - ε) ≠ 0 := by linarith
    rw [hA₁]
    field_simp
  have hA₁pos : 0 ≤ A₁ * (‖W t‖ / ‖deriv W 0‖) := by positivity
  have hdiv : (1 - ε) * A / (1 + ε) * ‖W t‖ / (1 + ε) ≤ ‖F t‖ / (1 + ε) := div_le_div_of_nonneg_right hc h1ε.le
  have hfinal : ‖F t‖ / (1 + ε) * (1 + ε) = ‖F t‖ := div_mul_cancel₀ _ h1ε.ne'
  have hF0le : 0 ≤ ‖F t‖ / (1 + ε) := by positivity
  calc A₁ * (‖W t‖ / ‖deriv W 0‖) * ‖deriv F 0‖ ≤ A₁ * (‖W t‖ / ‖deriv W 0‖) * (1 + ε) :=
        mul_le_mul_of_nonneg_left hF'0 hA₁pos
    _ ≤ ‖F t‖ / (1 + ε) * (1 + ε) := by
        refine mul_le_mul_of_nonneg_right ?_ h1ε.le
        calc A₁ * (‖W t‖ / ‖deriv W 0‖) ≤ A₁ * (‖W t‖ / (1 - ε)) := hgoal
          _ = (1 - ε) * A / (1 + ε) * ‖W t‖ / (1 + ε) := hA₁eq
          _ ≤ ‖F t‖ / (1 + ε) := hdiv
    _ = ‖F t‖ := hfinal

/-- `4 ≤ K*`. -/
theorem four_le_Kstar : ((4 : ℝ) : EReal) ≤ Kstar := by
  refine le_of_forall_lt fun c hc => ?_
  obtain ⟨S₀, hcS, hS₀⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  have hS₀4 : S₀ < 4 := by exact_mod_cast hS₀
  set S : ℝ := max S₀ 1 with hS
  have hS0 : 0 < S := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hS4 : S < 4 := max_lt hS₀4 (by norm_num)
  obtain ⟨d, hd, p, hp, hm⟩ := exists_poly_gt hS0 hS4
  have h1 : ((mval p : ℝ) : EReal) ≤ Kd d :=
    le_iSup (fun q : {q : ℂ[X] // IsPd d q} => ((mval q.1 : ℝ) : EReal)) ⟨p, hp⟩
  have h2 : Kd d ≤ Kstar := le_iSup (fun e : {e : ℕ // 2 ≤ e} => Kd e.1) ⟨d, hd⟩
  have hcS' : c < ((S : ℝ) : EReal) := hcS.trans_le (by exact_mod_cast le_max_left S₀ 1)
  have h3 : ((S : ℝ) : EReal) < ((mval p : ℝ) : EReal) := by exact_mod_cast hm
  exact (hcS'.trans h3).trans_le (h1.trans h2)

/-- **`K* = 4`**, as `Smale/Defs/Basic.lean` defines `K*`. -/
theorem kstar_eq_four : Kstar = ((4 : ℝ) : EReal) :=
  le_antisymm Smale.Koebe.Kstar_le_four four_le_Kstar

/-! ### The limit form, and each `K(d)` below `4` -/

/-- `K(d) ≤ K(d + 1)` for `d ≥ 2`, as a monotone sequence starting at `d = 2`. -/
theorem Kd_mono : Monotone fun n : ℕ => Smale.Kd (n + 2) :=
  monotone_nat_of_le_succ fun n => Smale.lem_5_3_proved (n + 2) (by omega)

/-- The supremum over `d ≥ 2` equals the supremum of the sequence starting at `d = 2`. -/
theorem iSup_shift : (⨆ n : ℕ, Smale.Kd (n + 2)) = Smale.Kstar := by
  apply le_antisymm
  · exact iSup_le fun n => le_iSup (fun e : {e : ℕ // 2 ≤ e} => Smale.Kd e.1) ⟨n + 2, by omega⟩
  · refine iSup_le fun e => ?_
    obtain ⟨d, hd⟩ := e
    have h := le_iSup (fun n : ℕ => Smale.Kd (n + 2)) (d - 2)
    have hdd : d - 2 + 2 = d := by omega
    simpa [hdd] using h

/-- `K(d)` tends to `4` as `d` tends to infinity. -/
theorem tendsto_Kd_four : Filter.Tendsto Smale.Kd Filter.atTop (nhds ((4 : ℝ) : EReal)) := by
  have h := tendsto_atTop_iSup Kd_mono
  rw [iSup_shift, Smale.P030.kstar_eq_four] at h
  exact (Filter.tendsto_add_atTop_iff_nat 2).1 h

/-- Each `K(d)` with `d ≥ 2` is below `4`. -/
theorem Kd_lt_four {d : ℕ} (hd : 2 ≤ d) : Smale.Kd d < ((4 : ℝ) : EReal) := by
  refine (Smale.Koebe.Kd_le_cfl hd).trans_lt ?_
  have hpos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have : 4 * ((d : ℝ) - 1) / ((d : ℝ) + 1) < 4 := by
    rw [div_lt_iff₀ hpos]
    linarith
  exact_mod_cast this

end Smale.P030
