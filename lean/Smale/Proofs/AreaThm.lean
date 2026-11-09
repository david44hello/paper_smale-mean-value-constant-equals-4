/-
Smale/Proofs/AreaThm.lean — the area theorem for the first coefficient (Gronwall 1914): if `h` is holomorphic on the unit
disk and `F(z) = z + h(1/z)` is injective on `|z| > 1`, then `|h'(0)| ≤ 1`. Here `F(z) = z + b₀ + b₁/z + ⋯` with `b₁ = h'(0)`.
Route; no Jordan curve theorem and no Green's theorem. Put `φ(u) = 1/u + h(u)`, with `h(0) = 0` after a translation.
(1) Area formula: the area of `φ(A)` is `∫_A |φ'|²`, for the annulus `A = {a < |u| < b}`.
(2) Polar coordinates and the circle mean value: the mean of `|φ'|²` on `|u| = s` is at least `s⁻⁴ + |h'(0)|²`, because
the mean of `u² h'(u)` is `0` and `|h'|² ≥ 2 Re(conj(c) h') - |c|²` pointwise, with `c = h'(0)`.
(3) `φ(A)` lies in the ellipse `K = T(closedBall 0 r)`, with `T z = z + c a² z̄` and `r = 1/a + 2 M a²`: `φ` maps the circle
`|u| = a` into `K`; every point outside `K` is a value of `φ` on `0 < |u| < a` (open-closed argument on the connected
outside of `K`); and `φ` is injective. The area of `K` is at most `π r²`, since `|det T| ≤ 1`.
(4) Compare the two areas, let `a → 0`, then `b → 1`.
-/
import Smale.Defs.Basic

namespace Smale.Koebe

open Metric MeasureTheory Set Filter Topology Complex Real
open scoped ENNReal ComplexConjugate

/-- The real Jacobian determinant of multiplication by `a` on `ℂ` is `|a|²`. -/
lemma det_smulRight_restrictScalars (a : ℂ) :
    (((1 : ℂ →L[ℂ] ℂ).smulRight a).restrictScalars ℝ).det = ‖a‖ ^ 2 := by
  have hlin : ((((1 : ℂ →L[ℂ] ℂ).smulRight a).restrictScalars ℝ : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)
      = (LinearMap.mulLeft ℂ a).restrictScalars ℝ := by
    refine LinearMap.ext fun z => ?_
    simp [mul_comm]
  rw [ContinuousLinearMap.det, hlin, LinearMap.det_restrictScalars, LinearMap.det_mulLeft,
    Algebra.norm_complex_eq]
  exact Complex.normSq_eq_norm_sq a

/-- Area formula: the area of the image of `A` under an injective holomorphic map is `∫_A |φ'|²`. -/
lemma volume_image_eq_lintegral {phi : ℂ → ℂ} {A : Set ℂ} (hA : MeasurableSet A)
    (hphi : ∀ u ∈ A, HasDerivAt phi (deriv phi u) u) (hinj : InjOn phi A) :
    volume (phi '' A) = ∫⁻ u in A, ENNReal.ofReal (‖deriv phi u‖ ^ 2) := by
  have key := lintegral_abs_det_fderiv_eq_addHaar_image (μ := (volume : Measure ℂ)) hA
    (f := phi) (f' := fun u => ((1 : ℂ →L[ℂ] ℂ).smulRight (deriv phi u)).restrictScalars ℝ)
    (fun u hu => ((hphi u hu).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hinj
  rw [← key]
  refine setLIntegral_congr_fun hA fun u _ => ?_
  simp only [det_smulRight_restrictScalars, abs_of_nonneg (sq_nonneg ‖deriv phi u‖)]

/-- The open annulus `a < |u| < b`. -/
def annulus (a b : ℝ) : Set ℂ := {u | a < ‖u‖ ∧ ‖u‖ < b}

lemma isOpen_annulus (a b : ℝ) : IsOpen (annulus a b) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

lemma measurable_polarCoord_symm : Measurable fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
  have heq : (fun p : ℝ × ℝ => Complex.polarCoord.symm p) =
      fun p => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * I) :=
    funext Complex.polarCoord_symm_apply
  rw [heq]
  exact Continuous.measurable (by fun_prop)

lemma polarCoord_symm_eq_circleMap (p : ℝ × ℝ) : Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  rw [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
  simp

/-- Polar coordinates on an annulus, for nonnegative measurable integrands. -/
lemma lintegral_annulus {a : ℝ} (b : ℝ) (ha : 0 ≤ a) (F : ℂ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ u in annulus a b, F u =
      ∫⁻ r in Ioo a b, ENNReal.ofReal r * ∫⁻ θ in Ioo (-π) π, F (circleMap 0 r θ) := by
  have hAm : MeasurableSet (annulus a b) := (isOpen_annulus a b).measurableSet
  have htarget : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl
  rw [← lintegral_indicator hAm, ← Complex.lintegral_comp_polarCoord_symm, htarget,
    Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod]
  · have hsub : Ioo a b ⊆ Ioi (0 : ℝ) := fun r hr => lt_of_le_of_lt ha hr.1
    have hind : ∀ r ∈ Ioi (0 : ℝ),
        (∫⁻ θ in Ioo (-π) π, ENNReal.ofReal r •
            (annulus a b).indicator F (Complex.polarCoord.symm (r, θ))) =
          (Ioo a b).indicator
            (fun r => ENNReal.ofReal r * ∫⁻ θ in Ioo (-π) π, F (circleMap 0 r θ)) r := by
      intro r hr
      have hrpos : (0 : ℝ) < r := hr
      by_cases hmem : r ∈ Ioo a b
      · rw [indicator_of_mem hmem, ← lintegral_const_mul]
        · refine lintegral_congr fun θ => ?_
          have hu : Complex.polarCoord.symm (r, θ) ∈ annulus a b := by
            simp only [annulus, mem_ofPred_eq, Complex.norm_polarCoord_symm, abs_of_pos hrpos]
            exact hmem
          rw [indicator_of_mem hu, polarCoord_symm_eq_circleMap]
          rfl
        · exact hF.comp ((continuous_circleMap 0 r).measurable)
      · rw [indicator_of_notMem hmem]
        have hu : ∀ θ : ℝ, Complex.polarCoord.symm (r, θ) ∉ annulus a b := by
          intro θ hu
          simp only [annulus, mem_ofPred_eq, Complex.norm_polarCoord_symm, abs_of_pos hrpos] at hu
          exact hmem hu
        have hz : ∀ θ : ℝ, ENNReal.ofReal r •
            (annulus a b).indicator F (Complex.polarCoord.symm (r, θ)) = 0 := fun θ => by
          rw [indicator_of_notMem (hu θ), smul_zero]
        simp only [hz, lintegral_zero]
    rw [setLIntegral_congr_fun measurableSet_Ioi hind,
      lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
      inter_eq_left.mpr hsub]
  · refine Measurable.aemeasurable ?_
    refine (ENNReal.measurable_ofReal.comp measurable_fst).smul ?_
    exact (hF.indicator hAm).comp measurable_polarCoord_symm

/-- The mean value on a circle, written over `(-π, π)`. -/
lemma integral_circleMap_eq {g : ℂ → ℂ} {s : ℝ} (hg : DifferentiableOn ℂ g (closedBall 0 s)) (hs : 0 < s) :
    ∫ θ in (-π)..π, g (circleMap 0 s θ) = ((2 * π : ℝ) : ℂ) * g 0 := by
  have hdc : DiffContOnCl ℂ g (ball (0 : ℂ) |s|) := by
    rw [abs_of_pos hs]
    exact hg.diffContOnCl_ball subset_rfl
  have hmean := hdc.circleAverage
  rw [Real.circleAverage_def] at hmean
  have hper : Function.Periodic (fun θ : ℝ => g (circleMap 0 s θ)) (2 * π) :=
    fun θ => by simp only [periodic_circleMap 0 s θ]
  have hshift := hper.intervalIntegral_add_eq (-π) 0
  have h1 : -π + 2 * π = π := by ring
  have h2 : (0 : ℝ) + 2 * π = 2 * π := by ring
  rw [h1, h2] at hshift
  rw [hshift]
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  have hval : (∫ θ in (0 : ℝ)..2 * π, g (circleMap 0 s θ)) =
      (2 * π : ℝ) • ((2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, g (circleMap 0 s θ)) := by
    rw [smul_smul, mul_inv_cancel₀ hpi, one_smul]
  rw [hval, hmean, Complex.real_smul]

/-- The pointwise inequality behind the circle mean bound. -/
lemma pointwise_lower {u k c : ℂ} {s : ℝ} (hs : 0 < s) (hu : ‖u‖ = s) :
    (s⁻¹) ^ 4 - ‖c‖ ^ 2 + (2 * conj c * k - 2 * ((s⁻¹) ^ 4 : ℝ) * (u ^ 2 * k)).re ≤ ‖k - u⁻¹ ^ 2‖ ^ 2 := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    exact hs.ne hu
  have hconj : conj (u⁻¹ ^ 2) = (((s⁻¹) ^ 4 : ℝ) : ℂ) * u ^ 2 := by
    have hnorm : u * conj u = ((s ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    have hs0 : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hconj0 : conj u ≠ 0 := by simpa using hu0
    rw [map_pow, map_inv₀]
    push_cast
    field_simp
    push_cast at hnorm
    calc s ^ 4 = (u * conj u) ^ 2 := by rw [hnorm]; ring
      _ = conj u ^ 2 * u ^ 2 := by ring
  have hnormsq : ‖u⁻¹ ^ 2‖ ^ 2 = (s⁻¹) ^ 4 := by
    rw [norm_pow, norm_inv, hu]
    ring
  have hexp : ‖k - u⁻¹ ^ 2‖ ^ 2 = ‖k‖ ^ 2 + (s⁻¹) ^ 4 - 2 * (k * conj (u⁻¹ ^ 2)).re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq, hnormsq]
  have hdiff : 0 ≤ ‖k‖ ^ 2 + ‖c‖ ^ 2 - 2 * (k * conj c).re := by
    have := Complex.normSq_nonneg (k - c)
    rwa [Complex.normSq_sub, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at this
  rw [hexp, hconj]
  have hre1 : (2 * conj c * k - 2 * ((s⁻¹) ^ 4 : ℝ) * (u ^ 2 * k)).re =
      2 * (k * conj c).re - 2 * (k * (((s⁻¹) ^ 4 : ℝ) * u ^ 2)).re := by
    have e1 : 2 * conj c * k - 2 * ((s⁻¹) ^ 4 : ℝ) * (u ^ 2 * k) =
        2 * (k * conj c) - 2 * (k * (((s⁻¹) ^ 4 : ℝ) * u ^ 2)) := by ring
    have h2 : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z => by simp [Complex.mul_re]
    rw [e1, Complex.sub_re, h2, h2]
  rw [hre1]
  linarith

/-- The circle mean of `|k - u⁻²|²` on `|u| = s` is at least `s⁻⁴ + |k 0|²`. -/
lemma mean_lower {k : ℂ → ℂ} {s : ℝ} (hk : DifferentiableOn ℂ k (closedBall 0 s)) (hs : 0 < s) :
    2 * π * ((s⁻¹) ^ 4 + ‖k 0‖ ^ 2) ≤
      ∫ θ in (-π)..π, ‖k (circleMap 0 s θ) - (circleMap 0 s θ)⁻¹ ^ 2‖ ^ 2 := by
  set c := k 0 with hc
  set Rf : ℂ → ℂ := fun u => 2 * conj c * k u - 2 * ((s⁻¹) ^ 4 : ℝ) * (u ^ 2 * k u) with hRf
  have hRfd : DifferentiableOn ℂ Rf (closedBall 0 s) :=
    ((differentiableOn_const _).mul hk).sub
      ((differentiableOn_const _).mul ((differentiableOn_id.pow 2).mul hk))
  have hmean := integral_circleMap_eq hRfd hs
  have hR0 : Rf 0 = ((2 * ‖c‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : conj c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [hRf, ← hc]
    push_cast at h1 ⊢
    linear_combination 2 * h1
  have hcm : ∀ θ : ℝ, circleMap 0 s θ ∈ closedBall (0 : ℂ) s := fun θ => by
    simp [abs_of_pos hs]
  have hRfc : Continuous fun θ : ℝ => Rf (circleMap 0 s θ) :=
    hRfd.continuousOn.comp_continuous (continuous_circleMap 0 s) hcm
  have hkc : Continuous fun θ : ℝ => k (circleMap 0 s θ) :=
    hk.continuousOn.comp_continuous (continuous_circleMap 0 s) hcm
  have hne : ∀ θ : ℝ, circleMap 0 s θ ≠ 0 := fun θ => circleMap_ne_center hs.ne'
  have hrhs : Continuous fun θ : ℝ => ‖k (circleMap 0 s θ) - (circleMap 0 s θ)⁻¹ ^ 2‖ ^ 2 :=
    ((hkc.sub (((continuous_circleMap 0 s).inv₀ hne).pow 2)).norm).pow 2
  have hlhs : Continuous fun θ : ℝ => (s⁻¹) ^ 4 - ‖c‖ ^ 2 + (Rf (circleMap 0 s θ)).re :=
    continuous_const.add (Complex.continuous_re.comp hRfc)
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by linarith [pi_pos] : -π ≤ π)
    (hlhs.intervalIntegrable _ _) (hrhs.intervalIntegrable _ _)
    (fun θ _ => pointwise_lower (k := k (circleMap 0 s θ)) (c := c) hs (by simp [abs_of_pos hs]))
  refine le_trans (le_of_eq ?_) hmono
  have hreC : Continuous fun θ : ℝ => (Rf (circleMap 0 s θ)).re := Complex.continuous_re.comp hRfc
  rw [intervalIntegral.integral_add (f := fun _ => (s⁻¹) ^ 4 - ‖c‖ ^ 2) intervalIntegrable_const
    (hreC.intervalIntegrable _ _), intervalIntegral.integral_const]
  have hre : (∫ θ in (-π)..π, (Rf (circleMap 0 s θ)).re) = (∫ θ in (-π)..π, Rf (circleMap 0 s θ)).re :=
    Complex.reCLM.intervalIntegral_comp_comm (hRfc.intervalIntegrable _ _)
  rw [hre, hmean, hR0, ← Complex.ofReal_mul, Complex.ofReal_re, smul_eq_mul]
  ring

/-- The radial integral. -/
lemma radial_integral {a b c2 : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ r in a..b, r * (2 * π * ((r⁻¹) ^ 4 + c2)) =
      π * ((a⁻¹ ^ 2 - b⁻¹ ^ 2) + c2 * (b ^ 2 - a ^ 2)) := by
  have hne : ∀ r ∈ uIcc a b, r ≠ 0 := fun r hr => by
    rw [uIcc_of_le hab] at hr
    exact (ha.trans_le hr.1).ne'
  have hderiv : ∀ r ∈ uIcc a b, HasDerivAt (fun r : ℝ => π * (-(r⁻¹ ^ 2) + c2 * r ^ 2))
      (r * (2 * π * ((r⁻¹) ^ 4 + c2))) r := by
    intro r hr
    have hr0 := hne r hr
    have h0 := (hasDerivAt_inv hr0).pow 2
    have h1 : HasDerivAt (fun r : ℝ => r⁻¹ ^ 2) _ r := h0
    have h2 := ((h1.neg).add ((hasDerivAt_pow 2 r).const_mul c2)).const_mul π
    convert h2 using 1
    simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat]
    field_simp
  have hcont : ContinuousOn (fun r : ℝ => r * (2 * π * ((r⁻¹) ^ 4 + c2))) (uIcc a b) :=
    continuousOn_id.mul (continuousOn_const.mul
      (((continuousOn_id.inv₀ hne).pow 4).add continuousOn_const))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  ring

lemma continuous_mean_integrand {k : ℂ → ℂ} {r : ℝ} (hk : DifferentiableOn ℂ k (closedBall 0 r)) (hr : 0 < r) :
    Continuous fun θ : ℝ => ‖k (circleMap 0 r θ) - (circleMap 0 r θ)⁻¹ ^ 2‖ ^ 2 := by
  have hcm : ∀ θ : ℝ, circleMap 0 r θ ∈ closedBall (0 : ℂ) r := fun θ => by
    simp [abs_of_pos hr]
  have hkc : Continuous fun θ : ℝ => k (circleMap 0 r θ) :=
    hk.continuousOn.comp_continuous (continuous_circleMap 0 r) hcm
  exact ((hkc.sub (((continuous_circleMap 0 r).inv₀
    fun θ => circleMap_ne_center hr.ne').pow 2)).norm).pow 2

/-- The lower bound for `∫_A |k - u⁻²|²` over the annulus `A = {a < |u| < b}`. -/
lemma annulus_lower {k : ℂ → ℂ} {a b : ℝ} (ha : 0 < a) (hab : a < b) (hkm : Measurable k)
    (hk : DifferentiableOn ℂ k (closedBall 0 b)) :
    ENNReal.ofReal (π * ((a⁻¹ ^ 2 - b⁻¹ ^ 2) + ‖k 0‖ ^ 2 * (b ^ 2 - a ^ 2))) ≤
      ∫⁻ u in annulus a b, ENNReal.ofReal (‖k u - u⁻¹ ^ 2‖ ^ 2) := by
  have hF : Measurable fun u : ℂ => ENNReal.ofReal (‖k u - u⁻¹ ^ 2‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (((hkm.sub (measurable_id.inv.pow_const 2)).norm).pow_const 2)
  rw [lintegral_annulus b ha.le _ hF]
  have hinner : ∀ r ∈ Ioo a b, ENNReal.ofReal (r * (2 * π * ((r⁻¹) ^ 4 + ‖k 0‖ ^ 2))) ≤
      ENNReal.ofReal r * ∫⁻ θ in Ioo (-π) π,
        ENNReal.ofReal (‖k (circleMap 0 r θ) - (circleMap 0 r θ)⁻¹ ^ 2‖ ^ 2) := by
    intro r hr
    have hr0 : 0 < r := ha.trans hr.1
    have hkr : DifferentiableOn ℂ k (closedBall 0 r) := hk.mono (closedBall_subset_closedBall hr.2.le)
    have hcont := continuous_mean_integrand hkr hr0
    rw [ENNReal.ofReal_mul hr0.le,
      ← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
        (ae_of_all _ fun θ => by positivity)]
    refine mul_le_mul_right ?_ _ |>.trans_eq rfl
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos])]
    exact mean_lower hkr hr0
  have hgc : ContinuousOn (fun r : ℝ => r * (2 * π * ((r⁻¹) ^ 4 + ‖k 0‖ ^ 2))) (Icc a b) :=
    continuousOn_id.mul (continuousOn_const.mul
      (((continuousOn_id.inv₀ fun r hr => (ha.trans_le hr.1).ne').pow 4).add continuousOn_const))
  calc ENNReal.ofReal (π * ((a⁻¹ ^ 2 - b⁻¹ ^ 2) + ‖k 0‖ ^ 2 * (b ^ 2 - a ^ 2)))
      = ENNReal.ofReal (∫ r in Ioo a b, r * (2 * π * ((r⁻¹) ^ 4 + ‖k 0‖ ^ 2))) := by
        rw [← radial_integral ha hab.le, intervalIntegral.integral_of_le hab.le,
          integral_Ioc_eq_integral_Ioo]
    _ = ∫⁻ r in Ioo a b, ENNReal.ofReal (r * (2 * π * ((r⁻¹) ^ 4 + ‖k 0‖ ^ 2))) :=
        ofReal_integral_eq_lintegral_ofReal
          ((hgc.integrableOn_Icc).mono_set Ioo_subset_Icc_self)
          ((ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun r hr => by
            have hr0 : 0 < r := ha.trans hr.1
            show (0 : ℝ) ≤ r * (2 * π * ((r⁻¹) ^ 4 + ‖k 0‖ ^ 2))
            positivity))
    _ ≤ _ := setLIntegral_mono' measurableSet_Ioo hinner

/-! ### The real-linear map `T z = z + λ z̄`, whose image of a disk is an ellipse -/

/-- `T z = z + λ z̄`. -/
noncomputable def ellT (lam z : ℂ) : ℂ := z + lam * conj z

/-- The inverse of `T`, for `|λ| < 1`. -/
noncomputable def ellS (lam w : ℂ) : ℂ := (w - lam * conj w) / ((1 - ‖lam‖ ^ 2 : ℝ) : ℂ)

lemma lam_mul_conj (lam : ℂ) : lam * conj lam = ((‖lam‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma one_sub_ne_zero {lam : ℂ} (hlam : ‖lam‖ < 1) : ((1 - ‖lam‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
  have hpos : 0 < 1 - ‖lam‖ ^ 2 := by nlinarith [norm_nonneg lam]
  exact_mod_cast hpos.ne'

lemma ellT_add (lam z w : ℂ) : ellT lam (z + w) = ellT lam z + ellT lam w := by
  simp only [ellT, map_add]
  ring

lemma ellT_ellS {lam : ℂ} (hlam : ‖lam‖ < 1) (w : ℂ) : ellT lam (ellS lam w) = w := by
  have hD := one_sub_ne_zero hlam
  have hl := lam_mul_conj lam
  simp only [ellT, ellS, map_div₀, map_sub, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  field_simp
  push_cast at hl ⊢
  linear_combination (-w) * hl

lemma ellS_ellT {lam : ℂ} (hlam : ‖lam‖ < 1) (z : ℂ) : ellS lam (ellT lam z) = z := by
  have hD := one_sub_ne_zero hlam
  have hl := lam_mul_conj lam
  simp only [ellT, ellS, map_add, map_mul, Complex.conj_conj]
  field_simp
  push_cast at hl ⊢
  linear_combination (-z) * hl

lemma norm_ellT_le (lam z : ℂ) : ‖ellT lam z‖ ≤ (1 + ‖lam‖) * ‖z‖ := by
  have h1 : ‖lam * conj z‖ = ‖lam‖ * ‖z‖ := by rw [norm_mul, Complex.norm_conj]
  calc ‖ellT lam z‖ ≤ ‖z‖ + ‖lam * conj z‖ := norm_add_le _ _
    _ = (1 + ‖lam‖) * ‖z‖ := by rw [h1]; ring

lemma norm_ellS_le {lam : ℂ} (hlam : ‖lam‖ ≤ 1 / 2) (e : ℂ) : ‖ellS lam e‖ ≤ 2 * ‖e‖ := by
  have hl0 := norm_nonneg lam
  have hpos : 0 < 1 - ‖lam‖ ^ 2 := by nlinarith
  have hnum : ‖e - lam * conj e‖ ≤ (1 + ‖lam‖) * ‖e‖ := by
    calc ‖e - lam * conj e‖ ≤ ‖e‖ + ‖lam * conj e‖ := norm_sub_le _ _
      _ = (1 + ‖lam‖) * ‖e‖ := by rw [norm_mul, Complex.norm_conj]; ring
  rw [ellS, norm_div, Complex.norm_real, Real.norm_of_nonneg hpos.le, div_le_iff₀ hpos]
  nlinarith [norm_nonneg e, mul_nonneg hl0 (norm_nonneg e), mul_nonneg (mul_nonneg hl0 hl0) (norm_nonneg e)]

/-- `T` as a real-linear map. -/
noncomputable def ellTL (lam : ℂ) : ℂ →ₗ[ℝ] ℂ :=
  LinearMap.id + (LinearMap.mulLeft ℝ lam) ∘ₗ Complex.conjAe.toLinearMap

lemma ellTL_apply (lam z : ℂ) : ellTL lam z = ellT lam z := rfl

lemma det_ellTL (lam : ℂ) : LinearMap.det (ellTL lam) = 1 - ‖lam‖ ^ 2 := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI, ellTL_apply,
    ellT]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp
  ring

/-- The area of the ellipse `T(closedBall 0 r)` is at most that of the disk, for `|λ| ≤ 1`. -/
lemma volume_ellT_image_le {lam : ℂ} (hlam : ‖lam‖ ≤ 1) {r : ℝ} (hr : 0 ≤ r) :
    volume (ellT lam '' closedBall (0 : ℂ) r) ≤ ENNReal.ofReal (π * r ^ 2) := by
  have himg : ellT lam '' closedBall (0 : ℂ) r = ellTL lam '' closedBall (0 : ℂ) r := rfl
  have hdet : |LinearMap.det (ellTL lam)| ≤ 1 := by
    rw [det_ellTL, abs_le]
    constructor <;> nlinarith [norm_nonneg lam]
  have hpi : ENNReal.ofReal π = (NNReal.pi : ℝ≥0∞) := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  rw [himg, Measure.addHaar_image_linearMap, Complex.volume_closedBall, mul_comm π,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hr, hpi]
  calc ENNReal.ofReal |LinearMap.det (ellTL lam)| * (ENNReal.ofReal r ^ 2 * (NNReal.pi : ℝ≥0∞))
      ≤ 1 * (ENNReal.ofReal r ^ 2 * (NNReal.pi : ℝ≥0∞)) := by
        refine mul_le_mul_left ?_ _
        simpa using ENNReal.ofReal_le_ofReal hdet
    _ = _ := one_mul _

/-! ### Connected sets -/

/-- Points whose modulus lies in a preconnected set of positive reals form a preconnected set. -/
lemma isPreconnected_norm_preimage {J : Set ℝ} (hJ : IsPreconnected J) (hpos : ∀ r ∈ J, 0 ≤ r) :
    IsPreconnected {u : ℂ | ‖u‖ ∈ J} := by
  have himg : {u : ℂ | ‖u‖ ∈ J} = (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) '' (J ×ˢ univ) := by
    ext u
    constructor
    · intro hu
      refine ⟨(‖u‖, Complex.arg u), ⟨hu, mem_univ _⟩, ?_⟩
      simp [circleMap, Complex.norm_mul_exp_arg_mul_I]
    · rintro ⟨⟨r, θ⟩, ⟨hr, -⟩, rfl⟩
      have hr0 : 0 ≤ r := hpos r hr
      simpa [abs_of_nonneg hr0] using hr
  rw [himg]
  refine (hJ.prod isPreconnected_univ).image _ ?_
  refine Continuous.continuousOn ?_
  simp only [circleMap]
  fun_prop

/-- The outside of the ellipse. -/
lemma isPreconnected_ellT_outside (lam : ℂ) (r : ℝ) (hr : 0 ≤ r) :
    IsPreconnected (ellT lam '' {z : ℂ | r < ‖z‖}) := by
  have hc : Continuous (ellT lam) := by
    unfold ellT
    fun_prop
  refine (isPreconnected_norm_preimage (J := Ioi r) isPreconnected_Ioi fun t ht => ?_).image _
    hc.continuousOn
  exact hr.trans (le_of_lt ht)

lemma isPreconnected_annulus {a : ℝ} (b : ℝ) (ha : 0 ≤ a) : IsPreconnected (annulus a b) :=
  isPreconnected_norm_preimage (J := Ioo a b) isPreconnected_Ioo fun _ ht => ha.trans (le_of_lt ht.1)

/-! ### Containment in the ellipse -/

section Containment

variable {h : ℂ → ℂ}

/-- The map `φ(u) = 1/u + h(u)`. -/
noncomputable def phiOf (h : ℂ → ℂ) (u : ℂ) : ℂ := u⁻¹ + h u

lemma annulus_subset_ball {b : ℝ} (hb : b ≤ 1) : annulus 0 b ⊆ ball (0 : ℂ) 1 := fun u hu => by
  simpa using hu.2.trans_le hb

lemma phiOf_differentiableOn (hh : DifferentiableOn ℂ h (ball 0 1)) :
    DifferentiableOn ℂ (phiOf h) (annulus 0 1) := by
  intro u hu
  have hu0 : u ≠ 0 := norm_pos_iff.mp hu.1
  have hub : u ∈ ball (0 : ℂ) 1 := annulus_subset_ball le_rfl hu
  have hda : DifferentiableAt ℂ h u := (hh u hub).differentiableAt (isOpen_ball.mem_nhds hub)
  exact (DifferentiableAt.add (differentiableAt_inv hu0) hda).differentiableWithinAt

/-- A lower bound for `|φ|` near `0`: if `|h| ≤ M0` on `|u| ≤ 1/2`, then `|φ(u)| ≥ 1/|u| - M0`. -/
lemma phiOf_norm_lower {M0 : ℝ} (hM0 : ∀ u ∈ closedBall (0 : ℂ) (1 / 2), ‖h u‖ ≤ M0) {u : ℂ}
    (hu : ‖u‖ ≤ 1 / 2) : ‖u‖⁻¹ - M0 ≤ ‖phiOf h u‖ := by
  have h1 : ‖u⁻¹‖ ≤ ‖phiOf h u‖ + ‖h u‖ := by
    have heq : u⁻¹ = phiOf h u - h u := by simp [phiOf]
    rw [heq]
    exact norm_sub_le _ _
  have h2 := hM0 u (by simpa using hu)
  rw [norm_inv] at h1
  linarith

/-- The image of the punctured disk `0 < |u| < 1/R` is open. -/
lemma isOpen_image_punctured (hh : DifferentiableOn ℂ h (ball 0 1))
    (hinj : InjOn (phiOf h) (annulus 0 1)) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    IsOpen (phiOf h '' annulus 0 a) := by
  have hsub : annulus 0 a ⊆ annulus 0 1 := fun u hu => ⟨hu.1, hu.2.trans_le ha1⟩
  have han : AnalyticOnNhd ℂ (phiOf h) (annulus 0 a) :=
    ((phiOf_differentiableOn hh).mono hsub).analyticOnNhd (isOpen_annulus 0 a)
  rcases han.is_constant_or_isOpen (isPreconnected_annulus a le_rfl) with ⟨w, hw⟩ | hopen
  · exfalso
    have hm1 : ((a / 2 : ℝ) : ℂ) ∈ annulus 0 a := by
      simp only [annulus, mem_ofPred_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos ha)]
      constructor <;> linarith
    have hm2 : ((a / 3 : ℝ) : ℂ) ∈ annulus 0 a := by
      have h3 : 0 < a / 3 := by positivity
      simp only [annulus, mem_ofPred_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h3]
      constructor <;> linarith
    have heq := hinj (hsub hm1) (hsub hm2) ((hw _ hm1).trans (hw _ hm2).symm)
    have hreal : a / 2 = a / 3 := by exact_mod_cast heq
    linarith
  · exact hopen _ subset_rfl (isOpen_annulus 0 a)

/-- **Containment**: if `φ` maps the circle `|u| = a` into the ellipse `K = T(closedBall 0 r)`, it maps every point
with `a ≤ |u| < 1` into `K`. The argument: every point outside `K` is a value of `φ` on `0 < |u| < a` (open-closed
argument on the connected outside of `K`), and `φ` is injective. -/
lemma phiOf_mem_ellipse (hh : DifferentiableOn ℂ h (ball 0 1))
    (hinj : InjOn (phiOf h) (annulus 0 1)) {a r : ℝ} {lam : ℂ} (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    (hlam : ‖lam‖ ≤ 1 / 2) (hr : 0 ≤ r)
    (hsph : ∀ u : ℂ, ‖u‖ = a → phiOf h u ∈ ellT lam '' closedBall (0 : ℂ) r)
    {u : ℂ} (hua : a ≤ ‖u‖) (hu1 : ‖u‖ < 1) : phiOf h u ∈ ellT lam '' closedBall (0 : ℂ) r := by
  have hlam1 : ‖lam‖ < 1 := by linarith
  have hhc : ContinuousOn h (closedBall (0 : ℂ) (1 / 2)) :=
    hh.continuousOn.mono (closedBall_subset_ball (by norm_num))
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn hhc
  have hM0nn : 0 ≤ M0 := (norm_nonneg _).trans (hM0 0 (by simp))
  set V := phiOf h '' annulus 0 a with hV
  set W := ellT lam '' {z : ℂ | r < ‖z‖} with hW
  have hVopen : IsOpen V := isOpen_image_punctured hh hinj ha (by linarith)
  have hWconn : IsPreconnected W := isPreconnected_ellT_outside lam r hr
  have hdisj : ∀ w ∈ W, w ∉ ellT lam '' closedBall (0 : ℂ) r := by
    rintro w ⟨z, hz, rfl⟩ ⟨z', hz', hzz'⟩
    have heq : z' = z := by
      have := congrArg (ellS lam) hzz'
      rwa [ellS_ellT hlam1, ellS_ellT hlam1] at this
    subst heq
    have hz1 : r < ‖z'‖ := hz
    have hz2 : ‖z'‖ ≤ r := by simpa using hz'
    exact absurd hz1 (not_lt.mpr hz2)
  have hout : ∀ w : ℂ, w ∉ ellT lam '' closedBall (0 : ℂ) r → w ∈ W := by
    intro w hw
    refine ⟨ellS lam w, ?_, ellT_ellS hlam1 w⟩
    by_contra hnot
    exact hw ⟨ellS lam w, by simpa using not_lt.mp hnot, ellT_ellS hlam1 w⟩
  -- a point of `W ∩ V`
  have hne : (W ∩ V).Nonempty := by
    set t : ℝ := (2 * r + M0 + a⁻¹ + 1)⁻¹ with ht
    have hainv : 2 ≤ a⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) ha]
      linarith
    have hden : 0 < 2 * r + M0 + a⁻¹ + 1 := by positivity
    have ht0 : 0 < t := inv_pos.mpr hden
    have htinv : t⁻¹ = 2 * r + M0 + a⁻¹ + 1 := by rw [ht, inv_inv]
    have hta : t < a := by
      rw [← inv_lt_inv₀ ha ht0, htinv]
      linarith
    have hnorm : ‖(t : ℂ)‖ = t := by simp [abs_of_pos ht0]
    have htm : (t : ℂ) ∈ annulus 0 a := by
      simp only [annulus, mem_ofPred_eq, hnorm]
      exact ⟨ht0, hta⟩
    refine ⟨phiOf h t, hout _ ?_, ⟨t, htm, rfl⟩⟩
    rintro ⟨z, hz, hzeq⟩
    have hb1 : ‖phiOf h t‖ ≤ 2 * r := by
      have hz' : ‖z‖ ≤ r := by simpa using hz
      rw [← hzeq]
      refine (norm_ellT_le lam z).trans ?_
      nlinarith [norm_nonneg z, norm_nonneg lam]
    have hb2 := phiOf_norm_lower hM0 (u := (t : ℂ)) (by rw [hnorm]; linarith)
    rw [hnorm, htinv] at hb2
    linarith
  -- closure step
  have hclosure : closure V ∩ W ⊆ V := by
    rintro w ⟨hwV, hwW⟩
    set del : ℝ := (‖w‖ + 2 + M0 + 2)⁻¹ with hdel
    have hdpos : 0 < del := inv_pos.mpr (by positivity)
    have hdinv : del⁻¹ = ‖w‖ + 2 + M0 + 2 := by rw [hdel, inv_inv]
    have hdsmall : del ≤ 1 / 2 := by
      rw [hdel, inv_le_comm₀ (by positivity) (by norm_num)]
      norm_num
      linarith [norm_nonneg w]
    set C : Set ℂ := {u : ℂ | del ≤ ‖u‖} ∩ closedBall 0 a with hC
    have hCcomp : IsCompact C :=
      (isCompact_closedBall (0 : ℂ) a).inter_left (isClosed_le continuous_const continuous_norm)
    have hCsub : C ⊆ annulus 0 1 := fun v hv => by
      have hv2 : ‖v‖ ≤ a := by simpa using hv.2
      exact ⟨hdpos.trans_le hv.1, by linarith⟩
    have hCcont : ContinuousOn (phiOf h) C :=
      (phiOf_differentiableOn hh).continuousOn.mono hCsub
    have hCimg : IsClosed (phiOf h '' C) := (hCcomp.image_of_continuousOn hCcont).isClosed
    have hlocal : ball w 1 ∩ V ⊆ phiOf h '' C := by
      rintro _ ⟨hb, v, hv, rfl⟩
      refine ⟨v, ⟨?_, ?_⟩, rfl⟩
      · by_contra hnot
        have hlt : ‖v‖ < del := not_le.mp hnot
        have hv0 : 0 < ‖v‖ := hv.1
        have hlow := phiOf_norm_lower hM0 (u := v) (by linarith [hv.2])
        have hinv : del⁻¹ < ‖v‖⁻¹ := (inv_lt_inv₀ hdpos hv0).mpr hlt
        have hb' : ‖phiOf h v - w‖ < 1 := by simpa [dist_eq_norm] using hb
        have htri : ‖phiOf h v‖ ≤ ‖phiOf h v - w‖ + ‖w‖ := by
          simpa using norm_add_le (phiOf h v - w) w
        rw [hdinv] at hinv
        linarith
      · simpa using hv.2.le
    have hwC : w ∈ phiOf h '' C := by
      have h1 : w ∈ ball w 1 ∩ closure V := ⟨mem_ball_self one_pos, hwV⟩
      have h2 := isOpen_ball.inter_closure h1
      exact hCimg.closure_subset_iff.mpr hlocal h2
    obtain ⟨v, hv, rfl⟩ := hwC
    have hv2 : ‖v‖ ≤ a := by simpa using hv.2
    rcases hv2.lt_or_eq with hlt | heq
    · exact ⟨v, ⟨hdpos.trans_le hv.1, hlt⟩, rfl⟩
    · exact absurd (hsph v heq) (hdisj _ hwW)
  have hWV : W ⊆ V := hWconn.subset_of_closure_inter_subset hVopen hne hclosure
  by_contra hnot
  obtain ⟨v, hv, hveq⟩ := hWV (hout _ hnot)
  have huA : u ∈ annulus 0 1 := ⟨ha.trans_le hua, hu1⟩
  have hvA : v ∈ annulus 0 1 := ⟨hv.1, hv.2.trans (by linarith)⟩
  have huv := hinj hvA huA hveq
  rw [huv] at hv
  exact absurd hv.2 (not_lt.mpr hua)

end Containment

section Assembly

variable {h : ℂ → ℂ}

/-- `h(u) = h(0) + h'(0) u + u² q(u)` on the disk, with `q` holomorphic. -/
lemma exists_taylor2 (hh : DifferentiableOn ℂ h (ball 0 1)) :
    ∃ q : ℂ → ℂ, DifferentiableOn ℂ q (ball 0 1) ∧
      ∀ u ∈ ball (0 : ℂ) 1, h u = h 0 + deriv h 0 * u + u ^ 2 * q u := by
  have h0mem : ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := ball_mem_nhds _ one_pos
  have hd1 : DifferentiableOn ℂ (dslope h 0) (ball 0 1) :=
    (Complex.differentiableOn_dslope h0mem).mpr hh
  refine ⟨dslope (dslope h 0) 0, (Complex.differentiableOn_dslope h0mem).mpr hd1, fun u _ => ?_⟩
  have e1 : u • dslope h 0 u = h u - h 0 := by simpa using sub_smul_dslope h 0 u
  have e2 : u • dslope (dslope h 0) 0 u = dslope h 0 u - deriv h 0 := by
    simpa [dslope_same] using sub_smul_dslope (dslope h 0) 0 u
  simp only [smul_eq_mul] at e1 e2
  linear_combination (-1 : ℂ) * e1 - u * e2

/-- On the circle `|u| = a`, `φ(u)` lies in the ellipse `T(closedBall 0 (1/a + 2 M a²))`, with `T z = z + c a² z̄`. -/
lemma phiOf_sphere_mem {q : ℂ → ℂ} {M a : ℝ} (hh0 : h 0 = 0) (hq : ∀ u ∈ ball (0 : ℂ) 1,
    h u = h 0 + deriv h 0 * u + u ^ 2 * q u) (hM : ∀ u ∈ closedBall (0 : ℂ) (1 / 2), ‖q u‖ ≤ M)
    (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hlam : ‖deriv h 0 * ((a ^ 2 : ℝ) : ℂ)‖ ≤ 1 / 2) {u : ℂ} (hu : ‖u‖ = a) :
    phiOf h u ∈ ellT (deriv h 0 * ((a ^ 2 : ℝ) : ℂ)) '' closedBall (0 : ℂ) (a⁻¹ + 2 * M * a ^ 2) := by
  set lam := deriv h 0 * ((a ^ 2 : ℝ) : ℂ) with hlamdef
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu
    exact ha.ne hu
  have hub : u ∈ ball (0 : ℂ) 1 := by
    simp only [mem_ball, dist_zero_right, hu]
    linarith
  have huc : ‖u‖ ≤ 1 / 2 := by rw [hu]; exact ha2
  set e := u ^ 2 * q u with he
  have heb : ‖e‖ ≤ M * a ^ 2 := by
    rw [he, norm_mul, norm_pow, hu, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM u (by simpa using huc)) (by positivity)
  refine ⟨u⁻¹ + ellS lam e, ?_, ?_⟩
  · rw [mem_closedBall_zero_iff]
    calc ‖u⁻¹ + ellS lam e‖ ≤ ‖u⁻¹‖ + ‖ellS lam e‖ := norm_add_le _ _
      _ ≤ a⁻¹ + 2 * ‖e‖ := by
          rw [norm_inv, hu]
          exact add_le_add le_rfl (norm_ellS_le hlam e)
      _ ≤ a⁻¹ + 2 * M * a ^ 2 := by nlinarith
  · have hconj : lam * conj u⁻¹ = deriv h 0 * u := by
      have hn : u * conj u = ((a ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
      have hcu : conj u ≠ 0 := by simpa using hu0
      rw [hlamdef, map_inv₀, ← hn]
      field_simp
    have hlam1 : ‖lam‖ < 1 := by linarith
    rw [ellT_add, ellT_ellS hlam1, ellT, hconj, phiOf, hq u hub, hh0]
    ring

/-- The inequality for fixed `0 < a < b < 1` with `a ≤ 1/2` and `|c| a² ≤ 1/2`, for `h(0) = 0`. -/
lemma area_inequality {q : ℂ → ℂ} {M a b : ℝ} (hh : DifferentiableOn ℂ h (ball 0 1))
    (hinj : InjOn (phiOf h) (annulus 0 1)) (hh0 : h 0 = 0)
    (hq : ∀ u ∈ ball (0 : ℂ) 1, h u = h 0 + deriv h 0 * u + u ^ 2 * q u)
    (hM : ∀ u ∈ closedBall (0 : ℂ) (1 / 2), ‖q u‖ ≤ M) (hM0 : 0 ≤ M)
    (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hab : a < b) (hb1 : b < 1)
    (hlam : ‖deriv h 0 * ((a ^ 2 : ℝ) : ℂ)‖ ≤ 1 / 2) :
    (a⁻¹ ^ 2 - b⁻¹ ^ 2) + ‖deriv h 0‖ ^ 2 * (b ^ 2 - a ^ 2) ≤ (a⁻¹ + 2 * M * a ^ 2) ^ 2 := by
  set lam := deriv h 0 * ((a ^ 2 : ℝ) : ℂ) with hlamdef
  set r := a⁻¹ + 2 * M * a ^ 2 with hrdef
  have hr : 0 ≤ r := by positivity
  set A := annulus a b with hA
  have hAsub : A ⊆ annulus 0 1 := fun u hu => ⟨ha.trans hu.1, hu.2.trans hb1⟩
  have hk : DifferentiableOn ℂ (deriv h) (ball 0 1) := hh.deriv isOpen_ball
  have hderiv : ∀ u ∈ A, HasDerivAt (phiOf h) (deriv h u - u⁻¹ ^ 2) u := by
    intro u hu
    have hu0 : u ≠ 0 := norm_pos_iff.mp (ha.trans hu.1)
    have hub : u ∈ ball (0 : ℂ) 1 := annulus_subset_ball le_rfl (hAsub hu)
    have hda := (hh u hub).differentiableAt (isOpen_ball.mem_nhds hub)
    have hsum : HasDerivAt (phiOf h) (-(u ^ 2)⁻¹ + deriv h u) u :=
      (hasDerivAt_inv hu0).add hda.hasDerivAt
    have hval : deriv h u - u⁻¹ ^ 2 = -(u ^ 2)⁻¹ + deriv h u := by
      rw [inv_pow]
      ring
    rw [hval]
    exact hsum
  have hphi : ∀ u ∈ A, HasDerivAt (phiOf h) (deriv (phiOf h) u) u := fun u hu => by
    rw [(hderiv u hu).deriv]
    exact hderiv u hu
  have harea := volume_image_eq_lintegral (isOpen_annulus a b).measurableSet hphi (hinj.mono hAsub)
  have hcongr : ∫⁻ u in A, ENNReal.ofReal (‖deriv (phiOf h) u‖ ^ 2) =
      ∫⁻ u in A, ENNReal.ofReal (‖deriv h u - u⁻¹ ^ 2‖ ^ 2) :=
    setLIntegral_congr_fun (isOpen_annulus a b).measurableSet fun u hu => by
      simp only [(hderiv u hu).deriv]
  have hlower := annulus_lower ha hab (measurable_deriv h)
    (hk.mono (closedBall_subset_ball hb1))
  have hsubK : phiOf h '' A ⊆ ellT lam '' closedBall (0 : ℂ) r := by
    rintro _ ⟨u, hu, rfl⟩
    exact phiOf_mem_ellipse hh hinj ha ha2 hlam hr
      (fun v hv => phiOf_sphere_mem hh0 hq hM ha ha2 hlam hv) hu.1.le (hu.2.trans hb1)
  have hupper := (measure_mono hsubK).trans
    (volume_ellT_image_le (lam := lam) (by linarith) hr)
  rw [harea, hcongr] at hupper
  have hfinal := hlower.trans hupper
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hfinal
  have hpi := Real.pi_pos
  nlinarith [mul_le_mul_of_nonneg_left hfinal (inv_pos.mpr hpi).le,
    inv_mul_cancel₀ hpi.ne', mul_inv_cancel₀ hpi.ne', hfinal]

/-- The core: `|h'(0)| ≤ 1` when `h(0) = 0`. -/
lemma norm_deriv_le_one_of_zero (hh : DifferentiableOn ℂ h (ball 0 1))
    (hinj : InjOn (phiOf h) (annulus 0 1)) (hh0 : h 0 = 0) : ‖deriv h 0‖ ≤ 1 := by
  obtain ⟨q, hqd, hq⟩ := exists_taylor2 hh
  have hqc : ContinuousOn q (closedBall (0 : ℂ) (1 / 2)) :=
    hqd.continuousOn.mono (closedBall_subset_ball (by norm_num))
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn hqc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  set cn := ‖deriv h 0‖ with hcn
  -- for fixed `b ∈ [1/2, 1)` let `a → 0`
  have hstep : ∀ b : ℝ, 1 / 2 ≤ b → b < 1 → cn ^ 2 * b ^ 2 ≤ b⁻¹ ^ 2 := by
    intro b hb2 hb1
    have hb0 : 0 < b := by linarith
    have hev : ∀ᶠ a : ℝ in 𝓝[>] 0,
        cn ^ 2 * (b ^ 2 - a ^ 2) - b⁻¹ ^ 2 ≤ 4 * M * a + 4 * M ^ 2 * a ^ 4 := by
      have hsmall : ∀ᶠ a : ℝ in 𝓝 0, a < b ∧ a ≤ 1 / 2 ∧ cn * a ^ 2 ≤ 1 / 2 := by
        have h1 : ∀ᶠ a : ℝ in 𝓝 0, a < 1 / 2 := Iio_mem_nhds (by norm_num)
        have h3c : Tendsto (fun a : ℝ => cn * a ^ 2) (𝓝 0) (𝓝 (cn * 0 ^ 2)) :=
          (Continuous.tendsto (by fun_prop) 0)
        have h3 : ∀ᶠ a : ℝ in 𝓝 0, cn * a ^ 2 < 1 / 2 :=
          h3c.eventually (Iio_mem_nhds (by norm_num))
        filter_upwards [h1, h3] with a ha1 ha3
        exact ⟨by linarith, ha1.le, ha3.le⟩
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hsmall] with a ha0 hs
      have ha0' : 0 < a := ha0
      have hlam : ‖deriv h 0 * ((a ^ 2 : ℝ) : ℂ)‖ ≤ 1 / 2 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        exact hs.2.2
      have hineq := area_inequality hh hinj hh0 hq hM hM0 ha0' hs.2.1 hs.1 hb1 hlam
      have hexp : (a⁻¹ + 2 * M * a ^ 2) ^ 2 = a⁻¹ ^ 2 + 4 * M * a + 4 * M ^ 2 * a ^ 4 := by
        field_simp
        ring
      rw [hexp] at hineq
      linarith
    have hL : Tendsto (fun a : ℝ => cn ^ 2 * (b ^ 2 - a ^ 2) - b⁻¹ ^ 2) (𝓝[>] 0)
        (𝓝 (cn ^ 2 * (b ^ 2 - 0 ^ 2) - b⁻¹ ^ 2)) :=
      (Continuous.tendsto (by fun_prop) 0).mono_left nhdsWithin_le_nhds
    have hR : Tendsto (fun a : ℝ => 4 * M * a + 4 * M ^ 2 * a ^ 4) (𝓝[>] 0)
        (𝓝 (4 * M * 0 + 4 * M ^ 2 * 0 ^ 4)) :=
      (Continuous.tendsto (by fun_prop) 0).mono_left nhdsWithin_le_nhds
    have hlim := le_of_tendsto_of_tendsto hL hR hev
    have e1 : (0 : ℝ) ^ 2 = 0 := by norm_num
    have e2 : (0 : ℝ) ^ 4 = 0 := by norm_num
    rw [e1, e2] at hlim
    linarith
  -- then let `b → 1`
  have hev2 : ∀ᶠ b : ℝ in 𝓝[<] 1, cn ^ 2 * b ^ 2 ≤ b⁻¹ ^ 2 := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with b hb
    exact hstep b hb.1.le hb.2
  have hL2 : Tendsto (fun b : ℝ => cn ^ 2 * b ^ 2) (𝓝[<] 1) (𝓝 (cn ^ 2 * 1 ^ 2)) :=
    (Continuous.tendsto (by fun_prop) 1).mono_left nhdsWithin_le_nhds
  have hR2 : Tendsto (fun b : ℝ => b⁻¹ ^ 2) (𝓝[<] 1) (𝓝 ((1 : ℝ)⁻¹ ^ 2)) := by
    have hc : ContinuousAt (fun b : ℝ => b⁻¹ ^ 2) 1 :=
      (continuousAt_inv₀ one_ne_zero).pow 2
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hlim2 := le_of_tendsto_of_tendsto hL2 hR2 hev2
  have e3 : (1 : ℝ)⁻¹ ^ 2 = 1 := by norm_num
  have e4 : cn ^ 2 * 1 ^ 2 = cn ^ 2 := by ring
  rw [e3, e4] at hlim2
  have hcn0 : 0 ≤ cn := norm_nonneg _
  nlinarith

/-- **Area theorem, first coefficient** (Gronwall 1914). A map of the exterior of the unit disk with a simple pole at
infinity is `F(z) = z + b₀ + b₁/z + b₂/z² + ⋯`, that is `F(z) = z + h(1/z)` with `h` holomorphic on the unit disk and
`h(u) = b₀ + b₁ u + b₂ u² + ⋯`; so `b₁ = h'(0)`. If `F` is injective on `|z| > 1`, then `|b₁| ≤ 1`. -/
theorem area_b1 {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h disk)
    (hinj : InjOn (fun z : ℂ => z + h z⁻¹) {z : ℂ | 1 < ‖z‖}) : ‖deriv h 0‖ ≤ 1 := by
  -- translate so that `h 0 = 0`
  set h0 : ℂ → ℂ := fun u => h u - h 0 with hh0def
  have hd0 : DifferentiableOn ℂ h0 (ball 0 1) := hh.sub (differentiableOn_const _)
  have hder : deriv h0 0 = deriv h 0 := by
    simp only [hh0def, deriv_sub_const]
  have hinj0 : InjOn (phiOf h0) (annulus 0 1) := by
    intro u hu v hv huv
    have hu0 : u ≠ 0 := norm_pos_iff.mp hu.1
    have hv0 : v ≠ 0 := norm_pos_iff.mp hv.1
    have hmemu : u⁻¹ ∈ {z : ℂ | 1 < ‖z‖} := by
      show 1 < ‖u⁻¹‖
      rw [norm_inv]
      exact (one_lt_inv₀ hu.1).mpr hu.2
    have hmemv : v⁻¹ ∈ {z : ℂ | 1 < ‖z‖} := by
      show 1 < ‖v⁻¹‖
      rw [norm_inv]
      exact (one_lt_inv₀ hv.1).mpr hv.2
    have heq : (fun z : ℂ => z + h z⁻¹) u⁻¹ = (fun z : ℂ => z + h z⁻¹) v⁻¹ := by
      simp only [phiOf, hh0def] at huv
      simp only [inv_inv]
      linear_combination huv
    exact inv_injective (hinj hmemu hmemv heq)
  rw [← hder]
  exact norm_deriv_le_one_of_zero hd0 hinj0 (by simp [hh0def])

end Assembly

end Smale.Koebe
