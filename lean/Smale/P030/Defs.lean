/-
Smale/P030/Defs.lean — the definitions for the proof that Smale's mean value constant equals 4. Nothing here changes `Smale/Defs/Basic.lean`.
`W` side: the Koebe-type map `koebeD`, the Cayley map `cayley` and its inverse, the comb `ζ + lam Σ log (ζ - x)`.
`F` side: the entire function `EE`, whose derivative is `exp(ξ^M) (1 - ξ^M/c)`, and the explicit map `stripY` of the
unit disk into the half strip `{Re y < a, |Im y| < C}`, with its left inverse `stripT`.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import Smale.Defs.Basic

namespace Smale.P030

open Complex

/-- `k_δ(t) = t/(1 + δ t)²`, univalent on the disk for `0 ≤ δ < 1`, with `k_δ(1) = 1/(1 + δ)²`. -/
noncomputable def koebeD (δ : ℝ) (t : ℂ) : ℂ := t / (1 + δ * t) ^ 2

/-- `μ(t) = i (1 + t)/(1 - t)`: the disk onto the upper half plane, `1 ↦ ∞`. -/
noncomputable def cayley (t : ℂ) : ℂ := I * (1 + t) / (1 - t)

/-- `μ⁻¹(w) = (w - i)/(w + i)`. -/
noncomputable def cayleyInv (w : ℂ) : ℂ := (w - I) / (w + I)

/-- The comb `G(ζ) = ζ + lam Σ_x log(ζ - x)`, on the upper half plane. -/
noncomputable def comb (lam : ℝ) (xs : Finset ℝ) (ζ : ℂ) : ℂ := ζ + lam * ∑ x ∈ xs, Complex.log (ζ - x)

/-- `φ = μ⁻¹ ∘ G ∘ μ`: a univalent self-map of the disk that tends to the point `1` at each `μ⁻¹(x)`, `x ∈ xs`, when `lam > 0`. -/
noncomputable def combDisc (lam : ℝ) (xs : Finset ℝ) (t : ℂ) : ℂ := cayleyInv (comb lam xs (cayley t))

/-- `E₀(ξ) = ∫_0^ξ exp(s^M) ds`, written on the segment from `0` to `ξ`. -/
noncomputable def E₀ (M : ℕ) (ξ : ℂ) : ℂ := ξ * ∫ τ in (0 : ℝ)..1, Complex.exp ((ξ * τ) ^ M)

/-- `E(ξ) = ∫_0^ξ exp(s^M) (1 - s^M/c) ds`, in closed form from `E₀`: with `k = 1/(c M)`,
`E = (1 + k) E₀ - k ξ exp(ξ^M)`. -/
noncomputable def EE (M : ℕ) (c : ℝ) (ξ : ℂ) : ℂ :=
  (1 + 1 / ((c : ℂ) * M)) * E₀ M ξ - 1 / ((c : ℂ) * M) * (ξ * Complex.exp (ξ ^ M))

/-- The half strip `{Re y < a, |Im y| < C}`. -/
def halfStrip (a C : ℝ) : Set ℂ := {y | y.re < a ∧ |y.im| < C}

/-- `β = π/(2C)`. -/
noncomputable def stripBeta (C : ℝ) : ℝ := Real.pi / (2 * C)

/-- `w = -sinh(β a) (1 - u)/(1 + u)`: the disk onto the left half plane, `0 ↦ -sinh(β a)`, `-1 ↦ ∞`. -/
noncomputable def stripW (a C : ℝ) (u : ℂ) : ℂ := -(Real.sinh (stripBeta C * a) : ℂ) * (1 - u) / (1 + u)

/-- `z` with `(z - 1/z)/2 = w`, `|z| < 1`, `Re z > 0`, for `Re w < 0`: with `m = (w - i)/(w + i)` in the upper half plane
and `p = √m` in the first quadrant, `z = -i (p - 1)/(p + 1)`. -/
noncomputable def stripZ (w : ℂ) : ℂ :=
  -I * ((((w - I) / (w + I)) ^ (1 / 2 : ℂ) - 1) / (((w - I) / (w + I)) ^ (1 / 2 : ℂ) + 1))

/-- The map of the disk into the half strip, `y = a + log(z)/β`, by elementary functions. -/
noncomputable def stripY (a C : ℝ) (u : ℂ) : ℂ := a + Complex.log (stripZ (stripW a C u)) / stripBeta C

/-- The left inverse: `T(y) = (-s - w)/(-s + w)`, `w = sinh(β (y - a))`, `s = sinh(β a)`. -/
noncomputable def stripT (a C : ℝ) (y : ℂ) : ℂ :=
  (-(Real.sinh (stripBeta C * a) : ℂ) - Complex.sinh (stripBeta C * (y - a))) /
    (-(Real.sinh (stripBeta C * a) : ℂ) + Complex.sinh (stripBeta C * (y - a)))

end Smale.P030
