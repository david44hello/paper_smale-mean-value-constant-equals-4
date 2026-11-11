/-
Smale/P030/Bridge.lean — the bridge in disc form: [JN, Prop. 4.3] and the reduction from a domain to a pair of
functions on the disc, together.
For a univalent `W` and a locally univalent `G` on the unit disk, both normalized, if `|G| ≥ A' |W|` on a collar of the
unit circle, then for every `A` with `0 < A < A'` a polynomial `p ∈ 𝓟_d` has `m(p) > A`. No Jordan domain, no Riemann map and no
Hilbert lemniscate theorem enter: `G ∘ W⁻¹` is approximated on `W(closed disk)`, and the proof of `jatarNg_prop_4_2_proved`
goes through with `G` in place of `W B / B(0)`.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import Smale.Proofs.JNAssembly

@[expose] public section

namespace Smale

open Polynomial Complex Metric Filter Topology

/-- On the band, `|P(Wz)/Wz| > A'`, from closeness to `G` and `|G z| ≥ A₁ |W z|` with `A' < A₁`. -/
theorem bridge_ratio_of_close {w g pv : ℂ} {A' A₁ c₀ : ℝ} (hc₀ : 0 < c₀) (hw : c₀ ≤ ‖w‖) (hg : A₁ * ‖w‖ ≤ ‖g‖)
    (hclose : ‖pv - g‖ < (A₁ - A') * c₀) (hgap : A' < A₁) : A' < ‖pv‖ / ‖w‖ := by
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hc₀ hw
  rw [lt_div_iff₀ hwpos]
  have htri : ‖g‖ - ‖pv - g‖ ≤ ‖pv‖ := by
    have h := norm_sub_norm_le g (g - pv)
    rw [sub_sub_cancel, norm_sub_rev] at h
    exact h
  have h1 : (A₁ - A') * c₀ ≤ (A₁ - A') * ‖w‖ := mul_le_mul_of_nonneg_left hw (by linarith)
  nlinarith

/-- **The bridge, disc form.** `W` univalent and normalized; `G` holomorphic with `G' ≠ 0` on the disk, normalized; on a
collar `r₀ ≤ |z| < 1`, `|G z| ≥ A₁ |W z|`. Then for `0 < A < A₁` some `p ∈ 𝓟_d`, `d ≥ 2`, has `m(p) > A`. -/
theorem bridge_pair {W G : ℂ → ℂ} (hW : InClassS W) (hGd : DifferentiableOn ℂ G disk) (hG0 : G 0 = 0)
    (hG1 : deriv G 0 = 1) (hG' : ∀ z ∈ disk, deriv G z ≠ 0) {A A₁ r₀ : ℝ} (hA0 : 0 < A) (hA : A < A₁) (hr₀1 : r₀ < 1)
    (hcollar : ∀ z : ℂ, r₀ ≤ ‖z‖ → ‖z‖ < 1 → A₁ * ‖W z‖ ≤ ‖G z‖) :
    ∃ d : ℕ, 2 ≤ d ∧ ∃ p : ℂ[X], IsPd d p ∧ A < mval p := by
  obtain ⟨A', hAA', hA'A₁⟩ := exists_between hA
  -- radii
  set r₁ : ℝ := max r₀ (1 / 2) with hr₁def
  have hr₁pos : 0 < r₁ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have h0r₁ : 0 ≤ r₁ := hr₁pos.le
  have hr₁1 : r₁ < 1 := max_lt hr₀1 (by norm_num)
  obtain ⟨r₂, hr₁₂, hr₂1⟩ := exists_between hr₁1
  obtain ⟨r₃, hr₂₃, hr₃1⟩ := exists_between hr₂1
  have h0r₂ : 0 ≤ r₂ := h0r₁.trans hr₁₂.le
  have h0r₃ : 0 ≤ r₃ := h0r₂.trans hr₂₃.le
  have hUniv := hW.1
  -- the band away from `0`: a lower bound for `|W|`
  obtain ⟨c₀, hc₀, hWlow⟩ := univalent_norm_lower hUniv hW.2.1 hr₁pos hr₃1
  have hεpos : 0 < (A₁ - A') * c₀ := mul_pos (by linarith) hc₀
  obtain ⟨P, hP0, hP1, ⟨μ, hμ, hPμ⟩, hPclose⟩ :=
    base_polynomial hW hGd hG0 hG1 hG' h0r₃ hr₃1 hεpos
  -- the separating polynomial
  set E : Set ℂ := W '' closedBall (0 : ℂ) r₂ with hEdef
  set F : Set ℂ := (W '' ball (0 : ℂ) r₃)ᶜ with hFdef
  have hball3 : ball (0 : ℂ) r₃ ⊆ disk := ball_subset_ball hr₃1.le
  have hEcomp : IsCompact E := (isCompact_closedBall _ _).image_of_continuousOn
    (univalent_continuousOn_closedBall hUniv hr₂1)
  have hEinf : E.Infinite :=
    (infinite_of_mem_nhds (0 : ℂ) (closedBall_mem_nhds _ (hr₁pos.trans hr₁₂))).image
      (hUniv.2.mono (closedBall_subset_ball hr₂1))
  have hEconn : IsPreconnected Eᶜ := compl_image_closedBall_isPreconnected hUniv h0r₂ hr₂1
  have hFclosed : IsClosed F := (univalent_isOpen_image hUniv hball3 isOpen_ball).isClosed_compl
  have hEF : Disjoint E F := by
    refine Set.disjoint_left.2 fun w hwE hwF => hwF ?_
    obtain ⟨z, hz, rfl⟩ := hwE
    exact ⟨z, closedBall_subset_ball hr₂₃ hz, rfl⟩
  obtain ⟨Q, a, c, hQdeg, ha, hac, hQE, hQF⟩ := fekete_separation hEcomp hEinf hEconn hFclosed hEF
  obtain ⟨s, r, hr, has, hsc, hcrit⟩ := level_choice hQdeg ha hac
  have hs : 0 < s := by linarith
  have hrs : r < s := by linarith
  have hsne : (s : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hs.ne')
  set q : ℂ[X] := C (s : ℂ)⁻¹ * Q with hqdef
  have hqeval : ∀ b, ‖q.eval b‖ = ‖Q.eval b‖ / s := by
    intro b
    rw [hqdef, eval_mul, eval_C, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs.le]
    field_simp
  have hqdegree : 1 ≤ q.natDegree := by rwa [hqdef, natDegree_C_mul hsne]
  have hρ0 : 0 < r / s := div_pos hr hs
  have hρ1 : r / s < 1 := (div_lt_one hs).2 hrs
  have hlow : ∀ b, ‖q.eval b‖ < 1 - r / s ↔ ‖Q.eval b‖ < s - r := by
    intro b
    rw [hqeval, div_lt_iff₀ hs]
    have : (1 - r / s) * s = s - r := by field_simp
    rw [this]
  have hhigh : ∀ b, ‖q.eval b‖ ≤ 1 + r / s ↔ ‖Q.eval b‖ ≤ s + r := by
    intro b
    rw [hqeval, div_le_iff₀ hs]
    have : (1 + r / s) * s = s + r := by field_simp
    rw [this]
  have h0E : (0 : ℂ) ∈ E := ⟨0, mem_closedBall_self h0r₂, hW.2.1⟩
  have hq0 : ‖q.eval 0‖ < 1 - r / s := (hlow 0).2 (lt_of_le_of_lt (hQE 0 h0E) has)
  -- `|q| ≤ 1 + ρ` keeps a point inside `W(D_{r₃})`
  have hinside : ∀ b, ‖q.eval b‖ ≤ 1 + r / s → b ∈ W '' ball (0 : ℂ) r₃ := by
    intro b hb
    by_contra hbF
    have h1 := hQF b hbF
    have h2 := (hhigh b).1 hb
    linarith
  refine perturb_crit (P := P) (q := q) (K := W '' closedBall (0 : ℂ) r₃) (A' := A') (ρ := r / s) (μ := μ) hP0 hP1
    hqdegree hA0 hAA' hρ0 hρ1 hq0 ((isCompact_closedBall _ _).image_of_continuousOn
      (univalent_continuousOn_closedBall hUniv hr₃1))
    hμ (fun b hb => ?_) ?_ ?_
  · obtain ⟨z, hz, rfl⟩ := hinside b hb
    exact ⟨z, ball_subset_closedBall hz, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hPμ z hz
  · intro b hb1 hb2
    have hband1 : s - r ≤ ‖Q.eval b‖ := not_lt.1 fun h => absurd ((hlow b).2 h) (not_lt.2 hb1)
    have hband2 : ‖Q.eval b‖ ≤ s + r := (hhigh b).1 hb2
    have hQ' : Q.derivative.eval b ≠ 0 := fun h => hcrit b h ⟨hband1, hband2⟩
    have hnotE : b ∉ E := fun hbE => by
      have := hQE b hbE
      linarith
    obtain ⟨z, hz, rfl⟩ := hinside b hb2
    have hzr₃ : ‖z‖ < r₃ := by simpa using hz
    have hzr₂ : r₂ < ‖z‖ := by
      by_contra hle
      exact hnotE ⟨z, by simpa using not_lt.1 hle, rfl⟩
    have hzr₁ : r₁ < ‖z‖ := hr₁₂.trans hzr₂
    have hz1 : ‖z‖ < 1 := hzr₃.trans hr₃1
    have hzr₀ : r₀ ≤ ‖z‖ := (le_max_left _ _).trans hzr₁.le
    refine ⟨?_, ?_, ?_⟩
    · rw [hqdef, derivative_C_mul, eval_mul, eval_C]
      exact mul_ne_zero hsne hQ'
    · exact fun h => hnotE (h ▸ h0E)
    · exact bridge_ratio_of_close hc₀ (hWlow z hzr₁.le hzr₃.le) (hcollar z hzr₀ hz1)
        (hPclose z (by simpa using hzr₃.le)) hA'A₁

end Smale
