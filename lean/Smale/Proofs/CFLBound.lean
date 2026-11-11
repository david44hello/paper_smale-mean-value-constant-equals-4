/-
Smale/Proofs/CFLBound.lean — the bound `K(d) ≤ 4(d-1)/(d+1)` for `d ≥ 2`, with no hypothesis, and so Smale's theorem
`K* ≤ 4`. The formula is that of Conte, Fujikawa and Lakic, as printed in Crane's paper.
Route. For `p ∈ 𝓟_d`, let `ρ` be the least modulus of a critical value, attained at the critical point `z₁`. If `ρ = 0`,
then `m(p) = 0`. Otherwise the disk `|w| < ρ` has no critical value, so it lifts through `p`, since `p` is a covering map
away from its critical values. Normalizing gives `G ∈ 𝒮` with `p(ρ G(w)) = ρ w`, and `G` omits `z/ρ` for every critical
point `z`. Put `u_z = ρ/z`. Koebe's bound (Smale/Proofs/Koebe.lean) gives `|a₂(G) + u_z| ≤ 2`, and Vieta gives
`Σ u_z = 2 a₂(G)`, the sum over the `d - 1` critical points counted with multiplicity. Summing the real part of
`conj(u)(u - v)` over the `u_z`, with `u = u_{z₁}`, gives `(d + 1) |u| ≤ 4 (d - 1)`. And `m(p) ≤ |p(z₁)|/|z₁| = |u|`.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import Smale.Proofs.Koebe

@[expose] public section

namespace Smale.Koebe

open Metric Set Filter Topology Polynomial Complex
open scoped ComplexConjugate

/-! ### The lift -/

/-- **Lift of a holomorphic map through a polynomial, on a disk**. If `f` is holomorphic on the disk `|w| < R` and takes no
critical value of `p`, and `p(z₀) = f(0)`, then `f` lifts through `p`: there is `H` with `H(0) = z₀` and `p ∘ H = f`, and
`H' = f'/(p' ∘ H)`. The reason: `p` is a covering map away from its critical values, and the disk is simply connected.
(A constant `p` cannot occur: every `z` is then critical, and `p(z₀) = f(0)` breaks the hypothesis at `w = 0`.) -/
theorem lift_through_ball {p : ℂ[X]} {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball 0 R))
    (havoid : ∀ w ∈ ball (0 : ℂ) R, ∀ z, p.derivative.eval z = 0 → f w ≠ p.eval z) {z₀ : ℂ}
    (hz₀ : p.eval z₀ = f 0) :
    ∃ H : ℂ → ℂ, H 0 = z₀ ∧ ∀ w ∈ ball (0 : ℂ) R,
      p.eval (H w) = f w ∧ p.derivative.eval (H w) ≠ 0 ∧
        HasDerivAt H (deriv f w / p.derivative.eval (H w)) w := by
  classical
  have hmem0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have : ContractibleSpace (ball (0 : ℂ) R) := (convex_ball (0 : ℂ) R).contractibleSpace ⟨0, hmem0⟩
  have : LocallyPathConnectedSpace (ball (0 : ℂ) R) := isOpen_ball.locallyPathConnectedSpace
  let g : C(ball (0 : ℂ) R, ℂ) := ⟨(ball (0 : ℂ) R).domRestrict f,
    continuousOn_iff_continuous_domRestrict.mp hf.continuousOn⟩
  have hgval : ∀ a : ball (0 : ℂ) R, g a = f a := fun _ => rfl
  have hs : ∀ a : ball (0 : ℂ) R, g a ∈ (p.eval '' {k | p.derivative.eval k = 0})ᶜ := by
    rintro ⟨a, ha⟩ ⟨k, hk, hka⟩
    exact havoid a ha k hk hka.symm
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := p.isCoveringMapOn_eval.existsUnique_continuousMap_lifts g
    (a₀ := ⟨0, hmem0⟩) (e₀ := z₀) (by rw [hgval]; exact hz₀) hs
  have hFval : ∀ a : ball (0 : ℂ) R, p.eval (F a) = f a := fun a => congrFun hF a
  -- extend `F` to all of `ℂ`
  set H : ℂ → ℂ := fun w => if hw : w ∈ ball (0 : ℂ) R then F ⟨w, hw⟩ else z₀ with hHdef
  have hH : ∀ w (hw : w ∈ ball (0 : ℂ) R), H w = F ⟨w, hw⟩ := fun w hw => by
    have hw' : ‖w‖ < R := by simpa using hw
    simp [hHdef, hw']
  have hval : ∀ w ∈ ball (0 : ℂ) R, p.eval (H w) = f w := fun w hw => by
    rw [hH w hw]
    exact hFval ⟨w, hw⟩
  have hcont : ContinuousOn H (ball (0 : ℂ) R) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (ball (0 : ℂ) R).domRestrict H = F := by
      ext a
      exact hH a a.2
    rw [heq]
    exact F.continuous
  have hne : ∀ w ∈ ball (0 : ℂ) R, p.derivative.eval (H w) ≠ 0 := by
    intro w hw hzero
    exact havoid w hw _ hzero (hval w hw).symm
  refine ⟨H, ?_, fun w hw => ⟨hval w hw, hne w hw, ?_⟩⟩
  · rw [hH 0 hmem0]
    exact hF0
  · have hfd : HasDerivAt f (deriv f w) w :=
      ((hf w hw).differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
    exact HasDerivAt.of_comp_left (f := fun x => p.eval x)
      (hcont.continuousAt (isOpen_ball.mem_nhds hw)) (p.hasDerivAt (H w)) hfd (hne w hw)
      (by filter_upwards [isOpen_ball.mem_nhds hw] with y hy using hval y hy)

/-- **Lift of a holomorphic map through a polynomial**, for example of a slit map. -/
theorem lift_through {p : ℂ[X]} {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f disk)
    (havoid : ∀ w ∈ disk, ∀ z, p.derivative.eval z = 0 → f w ≠ p.eval z) {z₀ : ℂ} (hz₀ : p.eval z₀ = f 0) :
    ∃ H : ℂ → ℂ, H 0 = z₀ ∧ DifferentiableOn ℂ H disk ∧ ∀ w ∈ disk, p.eval (H w) = f w := by
  obtain ⟨H, hH0, hH⟩ := lift_through_ball one_pos hf havoid hz₀
  exact ⟨H, hH0, fun w hw => (hH w hw).2.2.differentiableAt.differentiableWithinAt,
    fun w hw => (hH w hw).1⟩

/-- **Lift through a polynomial**. If every critical value of `p` has modulus at least `ρ`, the disk `|w| < ρ`
lifts through `p`, starting from any root `z₀` of `p`: there is a holomorphic injective `h` on the disk with
`h(0) = z₀` and `p(h(w)) = w`. (`p = 0` cannot occur: its derivative vanishes at every `z`, and `ρ ≤ 0` is false.) -/
theorem lift_disk {p : ℂ[X]} {ρ : ℝ} (hρ : 0 < ρ) (hcrit : ∀ z, p.derivative.eval z = 0 → ρ ≤ ‖p.eval z‖)
    {z₀ : ℂ} (hz₀ : p.eval z₀ = 0) :
    ∃ h : ℂ → ℂ, h 0 = z₀ ∧ IsUnivalentOn h (ball 0 ρ) ∧ ∀ w ∈ ball (0 : ℂ) ρ,
      p.eval (h w) = w ∧ p.derivative.eval (h w) ≠ 0 ∧ HasDerivAt h (p.derivative.eval (h w))⁻¹ w := by
  have havoid : ∀ w ∈ ball (0 : ℂ) ρ, ∀ z, p.derivative.eval z = 0 → (fun w : ℂ => w) w ≠ p.eval z := by
    intro w hw z hz heq
    have h1 := hcrit z hz
    have h2 : ‖w‖ < ρ := by simpa using hw
    have h3 : w = p.eval z := heq
    rw [← h3] at h1
    linarith
  obtain ⟨h, hh0, hh⟩ := lift_through_ball (f := fun w : ℂ => w) hρ differentiableOn_id havoid hz₀
  have hval : ∀ w ∈ ball (0 : ℂ) ρ, HasDerivAt h (p.derivative.eval (h w))⁻¹ w := fun w hw => by
    have h1 := (hh w hw).2.2
    have h2 : deriv (fun w : ℂ => w) w = 1 := deriv_id w
    rwa [h2, one_div] at h1
  refine ⟨h, hh0, ⟨fun w hw => (hval w hw).differentiableAt.differentiableWithinAt, ?_⟩,
    fun w hw => ⟨(hh w hw).1, (hh w hw).2.1, hval w hw⟩⟩
  intro a ha b hb hab
  have h1 : p.eval (h a) = a := (hh a ha).1
  have h2 : p.eval (h b) = b := (hh b hb).1
  rw [← h1, ← h2, hab]

/-! ### Vieta -/

/-- **Vieta for reciprocals, general form**: for `Q(0) ≠ 0`, the sum of `1/z` over the roots of `Q`, counted with
multiplicity, is `-Q'(0)/Q(0)`. -/
theorem sum_roots_inv {Q : ℂ[X]} (hQ : Q.eval 0 ≠ 0) :
    (Q.roots.map fun z => z⁻¹).sum = -(Q.derivative.eval 0 / Q.eval 0) := by
  rw [(IsAlgClosed.splits Q).eval_derivative_div_eval_of_ne_zero hQ]
  have hmap : (Q.roots.map fun z => 1 / (0 - z)) = (Q.roots.map fun z => -z⁻¹) :=
    Multiset.map_congr rfl fun z _ => by simp
  rw [hmap, Multiset.sum_map_neg, neg_neg]

/-- **Vieta for reciprocals**: for `p'(0) = 1`, the sum of `1/z` over the critical points of `p`, counted with
multiplicity, is `-2 a₂`, where `a₂` is the coefficient of `z²` in `p`. -/
theorem vieta_reciprocal {p : ℂ[X]} (hp1 : p.derivative.eval 0 = 1) :
    (p.derivative.roots.map fun z => z⁻¹).sum = -(2 * p.coeff 2) := by
  rw [sum_roots_inv (by rw [hp1]; exact one_ne_zero), hp1, div_one, ← coeff_zero_eq_eval_zero,
    coeff_derivative, coeff_derivative]
  norm_num
  ring

/-! ### The normalized lift -/

/-- **The normalized lift**. Let `p(0) = 0`, `p'(0) = 1`, and let every
critical value of `p` have modulus at least `ρ > 0`. Then there is `G ∈ 𝒮` with `p(ρ G(w)) = ρ w` on the disk; `G` omits
`z/ρ` for every critical point `z`; and `G''(0) = ρ Σ 1/z`, the sum over the critical points counted with multiplicity.
So, with `u_z = ρ/z`, `Σ u_z = 2 a₂(G)`. -/
theorem exists_normalized_lift {p : ℂ[X]} (hp0 : p.eval 0 = 0) (hp1 : p.derivative.eval 0 = 1) {ρ : ℝ} (hρ : 0 < ρ)
    (hcrit : ∀ z, p.derivative.eval z = 0 → ρ ≤ ‖p.eval z‖) :
    ∃ G : ℂ → ℂ, InClassS G ∧ (∀ w ∈ disk, p.eval ((ρ : ℂ) * G w) = (ρ : ℂ) * w) ∧
      (∀ z, p.derivative.eval z = 0 → ∀ w ∈ disk, G w ≠ z / (ρ : ℂ)) ∧
      deriv (deriv G) 0 = (ρ : ℂ) * (p.derivative.roots.map fun z => z⁻¹).sum := by
  obtain ⟨h, hh0, ⟨-, hinj⟩, hlift⟩ := lift_disk hρ hcrit hp0
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hscale : ∀ w ∈ disk, (ρ : ℂ) * w ∈ ball (0 : ℂ) ρ := fun w hw => by
    have hw1 : ‖w‖ < 1 := by simpa using hw
    simp only [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    nlinarith
  set G : ℂ → ℂ := fun w => h ((ρ : ℂ) * w) / (ρ : ℂ) with hGdef
  have hmulG : ∀ w, (ρ : ℂ) * G w = h ((ρ : ℂ) * w) := fun w => by
    simp only [hGdef]
    field_simp
  -- `G' = 1/p'(ρ G)` on the disk
  have hGd : ∀ w ∈ disk, HasDerivAt G (p.derivative.eval (h ((ρ : ℂ) * w)))⁻¹ w := by
    intro w hw
    have hat := (hlift _ (hscale w hw)).2.2
    have hinner : HasDerivAt (fun w : ℂ => (ρ : ℂ) * w) (ρ : ℂ) w := by
      simpa using (hasDerivAt_id w).const_mul (ρ : ℂ)
    have hcomp : HasDerivAt (fun w => h ((ρ : ℂ) * w))
        ((p.derivative.eval (h ((ρ : ℂ) * w)))⁻¹ * (ρ : ℂ)) w := hat.comp w hinner
    have hdiv := hcomp.div_const (ρ : ℂ)
    have hval : (p.derivative.eval (h ((ρ : ℂ) * w)))⁻¹ * (ρ : ℂ) / (ρ : ℂ) =
        (p.derivative.eval (h ((ρ : ℂ) * w)))⁻¹ := by
      field_simp
    rwa [hval] at hdiv
  have h0mem : (0 : ℂ) ∈ disk := mem_ball_self one_pos
  have hnhds : disk ∈ 𝓝 (0 : ℂ) := ball_mem_nhds _ one_pos
  have hrho0 : (ρ : ℂ) * 0 = 0 := mul_zero _
  have hG0 : G 0 = 0 := by simp only [hGdef, hrho0, hh0, zero_div]
  have hGder0 : deriv G 0 = 1 := by
    rw [(hGd 0 h0mem).deriv, hrho0, hh0, hp1, inv_one]
  refine ⟨G, ⟨⟨fun w hw => (hGd w hw).differentiableAt.differentiableWithinAt, ?_⟩, hG0, hGder0⟩,
    ?_, ?_, ?_⟩
  · intro a ha b hb hab
    have h1 : h ((ρ : ℂ) * a) = h ((ρ : ℂ) * b) := by rw [← hmulG, ← hmulG, hab]
    exact mul_left_cancel₀ hρc (hinj (hscale a ha) (hscale b hb) h1)
  · intro w hw
    rw [hmulG]
    exact (hlift _ (hscale w hw)).1
  · intro z hz w hw heq
    have h1 : h ((ρ : ℂ) * w) = z := by
      rw [← hmulG, heq]
      field_simp
    have h2 := (hlift _ (hscale w hw)).1
    rw [h1] at h2
    have h3 := hcrit z hz
    rw [h2] at h3
    have h4 := mem_ball_zero_iff.mp (hscale w hw)
    linarith
  · -- the second derivative
    have hev : deriv G =ᶠ[𝓝 0] fun w => (p.derivative.eval (h ((ρ : ℂ) * w)))⁻¹ := by
      filter_upwards [hnhds] with w hw using (hGd w hw).deriv
    rw [hev.deriv_eq]
    have hat0 : HasDerivAt h (p.derivative.eval (h ((ρ : ℂ) * 0)))⁻¹ ((ρ : ℂ) * 0) :=
      (hlift _ (hscale 0 h0mem)).2.2
    have hinner : HasDerivAt (fun w : ℂ => (ρ : ℂ) * w) (ρ : ℂ) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul (ρ : ℂ)
    have hcomp : HasDerivAt (fun w => h ((ρ : ℂ) * w))
        ((p.derivative.eval (h ((ρ : ℂ) * 0)))⁻¹ * (ρ : ℂ)) 0 := hat0.comp (0 : ℂ) hinner
    have hpoly : HasDerivAt (fun x => p.derivative.eval x)
        (p.derivative.derivative.eval (h ((ρ : ℂ) * 0))) (h ((ρ : ℂ) * 0)) :=
      p.derivative.hasDerivAt _
    have hcomp1 := hpoly.comp (0 : ℂ) hcomp
    have hcomp2 : HasDerivAt (fun w => p.derivative.eval (h ((ρ : ℂ) * w)))
        (p.derivative.derivative.eval (h ((ρ : ℂ) * 0)) *
          ((p.derivative.eval (h ((ρ : ℂ) * 0)))⁻¹ * (ρ : ℂ))) 0 := hcomp1
    have hne0 : p.derivative.eval (h ((ρ : ℂ) * 0)) ≠ 0 := by
      rw [hrho0, hh0, hp1]
      exact one_ne_zero
    have hinv := hcomp2.inv hne0
    have hinv' : HasDerivAt (fun w => (p.derivative.eval (h ((ρ : ℂ) * w)))⁻¹) _ 0 := hinv
    rw [hinv'.deriv, sum_roots_inv (by rw [hp1]; exact one_ne_zero), hrho0, hh0, hp1]
    simp
    ring

/-! ### The algebra of the sum over the critical points, with no division by `d - 2` -/

/-- The sum over a multiset of the real part of `conj(u)(u - v)`. -/
lemma re_sum_le {u : ℂ} (R : Multiset ℂ) (hR : ∀ v ∈ R, ‖u - v‖ ≤ 4) :
    (conj u * ((Multiset.card R : ℂ) * u - R.sum)).re ≤ (Multiset.card R : ℝ) * (4 * ‖u‖) := by
  induction R using Multiset.induction_on with
  | empty => simp
  | cons v R ih =>
    have hv : ‖u - v‖ ≤ 4 := hR v (Multiset.mem_cons_self v R)
    have hrest := ih fun x hx => hR x (Multiset.mem_cons_of_mem hx)
    have hterm : (conj u * (u - v)).re ≤ 4 * ‖u‖ := by
      calc (conj u * (u - v)).re ≤ ‖conj u * (u - v)‖ := Complex.re_le_norm _
        _ = ‖u‖ * ‖u - v‖ := by rw [norm_mul, Complex.norm_conj]
        _ ≤ ‖u‖ * 4 := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
        _ = 4 * ‖u‖ := mul_comm _ _
    have hsplit : conj u * (((Multiset.card (v ::ₘ R) : ℕ) : ℂ) * u - (v ::ₘ R).sum) =
        conj u * ((Multiset.card R : ℂ) * u - R.sum) + conj u * (u - v) := by
      rw [Multiset.card_cons, Multiset.sum_cons]
      push_cast
      ring
    rw [hsplit, Complex.add_re, Multiset.card_cons]
    push_cast
    linarith

/-- The algebra of the sum over the critical points: a multiset `U` with `|A + v| ≤ 2` for all `v ∈ U` and `Σ U = 2A` has
`(card U + 2) |u| ≤ 4 card U` for every `u ∈ U`. -/
lemma cfl_algebra {U : Multiset ℂ} {u A : ℂ} (hu : u ∈ U) (hA : ∀ v ∈ U, ‖A + v‖ ≤ 2) (hsum : U.sum = 2 * A) :
    ((Multiset.card U : ℝ) + 2) * ‖u‖ ≤ 4 * (Multiset.card U : ℝ) := by
  obtain ⟨R, rfl⟩ := Multiset.exists_cons_of_mem hu
  have hAu : ‖A + u‖ ≤ 2 := hA u (Multiset.mem_cons_self u R)
  have hdiff : ∀ v ∈ R, ‖u - v‖ ≤ 4 := fun v hv => by
    have hAv := hA v (Multiset.mem_cons_of_mem hv)
    have heq : u - v = (A + u) - (A + v) := by ring
    rw [heq]
    linarith [norm_sub_le (A + u) (A + v)]
  have hre := re_sum_le R hdiff
  rw [Multiset.sum_cons] at hsum
  have hRsum : R.sum = 2 * A - u := by linear_combination hsum
  set t := ‖u‖ with ht
  set n : ℝ := (Multiset.card R : ℝ) with hn
  have ht0 : 0 ≤ t := norm_nonneg _
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have huu : (conj u * u).re = t ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  -- `Re(conj(u) A) ≤ 2t - t²`
  have hAre : (conj u * A).re ≤ 2 * t - t ^ 2 := by
    have h1 : (conj u * (A + u)).re ≤ t * 2 := by
      calc (conj u * (A + u)).re ≤ ‖conj u * (A + u)‖ := Complex.re_le_norm _
        _ = t * ‖A + u‖ := by rw [norm_mul, Complex.norm_conj]
        _ ≤ t * 2 := mul_le_mul_of_nonneg_left hAu ht0
    have h2 : conj u * (A + u) = conj u * A + conj u * u := by ring
    rw [h2, Complex.add_re, huu] at h1
    linarith
  -- the sum
  have hexp : conj u * (((Multiset.card R : ℕ) : ℂ) * u - R.sum) =
      ((n + 1 : ℝ) : ℂ) * (conj u * u) - 2 * (conj u * A) := by
    rw [hRsum, hn]
    push_cast
    ring
  rw [hexp] at hre
  have hre2 : (((n + 1 : ℝ) : ℂ) * (conj u * u) - 2 * (conj u * A)).re =
      (n + 1) * t ^ 2 - 2 * (conj u * A).re := by
    have h2 : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z => by simp [Complex.mul_re]
    rw [Complex.sub_re, h2, Complex.re_ofReal_mul, huu]
  rw [hre2] at hre
  have hmain : (n + 3) * t ^ 2 ≤ 4 * (n + 1) * t := by nlinarith
  rw [Multiset.card_cons]
  push_cast
  rw [← hn]
  rcases ht0.eq_or_lt with hzero | hpos
  · rw [← hzero]
    nlinarith
  · have hdiv : (n + 3) * t ≤ 4 * (n + 1) := by
      have h3 : (n + 3) * t * t ≤ 4 * (n + 1) * t := by nlinarith
      exact le_of_mul_le_mul_right h3 hpos
    nlinarith

/-! ### The bound -/

/-- **The bound for one polynomial**: for `p ∈ 𝓟_d`, `d ≥ 2`, `m(p) ≤ 4(d-1)/(d+1)`. -/
theorem cfl_bound {d : ℕ} (hd : 2 ≤ d) {p : ℂ[X]} (hp : IsPd d p) :
    mval p ≤ 4 * ((d : ℝ) - 1) / ((d : ℝ) + 1) := by
  obtain ⟨hdeg, hp0, hp1⟩ := hp
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdne : ((d : ℝ) + 1) ≠ 0 := by positivity
  have hdpos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hbdd : BddBelow (critRatios p) := ⟨0, by
    rintro r ⟨β, -, rfl⟩
    positivity⟩
  have hder_ne : p.derivative ≠ 0 := by
    intro hzero
    rw [hzero, eval_zero] at hp1
    exact zero_ne_one hp1
  have hdegd : p.derivative.natDegree = d - 1 := by
    rw [natDegree_derivative, hdeg]
  have hcard : Multiset.card p.derivative.roots = d - 1 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hdegd]
  have hcardR : ((Multiset.card p.derivative.roots : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [hcard, Nat.cast_sub (by omega)]
    simp
  -- the critical point with the least critical value
  have hroots_ne : p.derivative.roots.toFinset.Nonempty := by
    rw [Multiset.toFinset_nonempty]
    intro hzero
    rw [hzero] at hcard
    simp only [Multiset.card_zero] at hcard
    omega
  obtain ⟨z1, hz1mem, hz1min⟩ := p.derivative.roots.toFinset.exists_min_image (fun z => ‖p.eval z‖) hroots_ne
  have hz1root : p.derivative.eval z1 = 0 := by
    have := Multiset.mem_toFinset.mp hz1mem
    exact (mem_roots hder_ne).mp this
  have hz1ne : z1 ≠ 0 := by
    rintro rfl
    rw [hp1] at hz1root
    exact one_ne_zero hz1root
  have hmval : mval p ≤ ‖p.eval z1‖ / ‖z1‖ := csInf_le hbdd ⟨z1, hz1root, rfl⟩
  set ρ := ‖p.eval z1‖ with hρdef
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have htarget0 : 0 ≤ 4 * ((d : ℝ) - 1) / ((d : ℝ) + 1) := by
    apply div_nonneg _ hdpos.le
    linarith
  rcases hρ0.eq_or_lt with hzero | hρpos
  · -- a critical value is `0`
    rw [← hzero, zero_div] at hmval
    exact hmval.trans htarget0
  · have hcrit : ∀ z, p.derivative.eval z = 0 → ρ ≤ ‖p.eval z‖ := fun z hz =>
      hz1min z (Multiset.mem_toFinset.mpr ((mem_roots hder_ne).mpr hz))
    obtain ⟨G, hG, -, homit, hG2⟩ := exists_normalized_lift hp0 hp1 hρpos hcrit
    have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρpos.ne'
    set U : Multiset ℂ := p.derivative.roots.map fun z => (z / (ρ : ℂ))⁻¹ with hU
    set A : ℂ := deriv (deriv G) 0 / 2 with hA
    have hUA : ∀ v ∈ U, ‖A + v‖ ≤ 2 := by
      intro v hv
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hv
      exact koebe_omit hG (homit z ((mem_roots hder_ne).mp hz))
    have hUsum : U.sum = 2 * A := by
      have hmap : U = p.derivative.roots.map fun z => (ρ : ℂ) * z⁻¹ :=
        Multiset.map_congr rfl fun z _ => by
          rw [inv_div]
          ring
      rw [hmap, Multiset.sum_map_mul_left, hA, hG2]
      ring
    have huU : (z1 / (ρ : ℂ))⁻¹ ∈ U :=
      Multiset.mem_map.mpr ⟨z1, (mem_roots hder_ne).mpr hz1root, rfl⟩
    have halg := cfl_algebra huU hUA hUsum
    have hcardU : ((Multiset.card U : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [hU, Multiset.card_map, hcardR]
    rw [hcardU] at halg
    have hnorm : ‖(z1 / (ρ : ℂ))⁻¹‖ = ρ / ‖z1‖ := by
      rw [norm_inv, norm_div, Complex.norm_real, Real.norm_of_nonneg hρpos.le, inv_div]
    rw [hnorm] at halg
    have hle : ρ / ‖z1‖ ≤ 4 * ((d : ℝ) - 1) / ((d : ℝ) + 1) := by
      rw [le_div_iff₀ hdpos]
      linarith
    exact hmval.trans hle

/-- **`K(d) ≤ 4(d-1)/(d+1)`**, for `d ≥ 2` (the formula of Conte, Fujikawa and Lakic, as printed in Crane's paper). -/
theorem Kd_le_cfl {d : ℕ} (hd : 2 ≤ d) : Kd d ≤ ((4 * ((d : ℝ) - 1) / ((d : ℝ) + 1) : ℝ) : EReal) :=
  iSup_le fun p => EReal.coe_le_coe_iff.mpr (cfl_bound hd p.2)

/-- **`K(d) ≤ 4`**, for `d ≥ 2`. -/
theorem Kd_le_four {d : ℕ} (hd : 2 ≤ d) : Kd d ≤ ((4 : ℝ) : EReal) := by
  refine (Kd_le_cfl hd).trans (EReal.coe_le_coe_iff.mpr ?_)
  have hdpos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hdpos]
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

/-- **Smale's theorem** (Smale 1981): `K* ≤ 4`. -/
theorem Kstar_le_four : Kstar ≤ ((4 : ℝ) : EReal) :=
  iSup_le fun d => Kd_le_four d.2

end Smale.Koebe
