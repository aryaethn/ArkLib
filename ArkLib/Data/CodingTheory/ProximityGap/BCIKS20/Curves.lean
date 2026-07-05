/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound
import ArkLib.Data.CodingTheory.ReedSolomon

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory
open scoped BigOperators LinearCode ProbabilityTheory
open Code

section CoreResults

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]


omit [DecidableEq ι] in
/-- Theorem 1.5 (Correlated agreement for low-degree parameterised curves) in [BCIKS20].

Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and a curve passing through words `u₀, ..., uκ`, such that
the probability that a random point on the curve is `δ`-close to the Reed-Solomon code
is at most `ε`. Then, the words `u₀, ..., uκ` have correlated agreement. -/
theorem correlatedAgreement_affine_curves {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  sorry

end CoreResults

section BCIKS20ProximityGapSection6

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The parameters for which the curve points are `δ`-close to a set `V`
(typically, a linear code). This is the set `S` from the proximity gap paper. -/
noncomputable def coeffs_of_close_proximity_curve {l : ℕ}
    (δ : ℚ≥0) (u : Fin l → Fin n → F) (V : Set (Fin n → F)) : Finset F :=
  Finset.filter (fun z : F => δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z, V) ≤ δ)
    Finset.univ

/-- Unique-decoding regime (`δ ≤ (1 - ρ) / 2`); companion of
`large_agreement_set_on_curve_implies_correlated_agreement'` (Johnson regime). This is
Theorem 6.1 of [BCIKS20]. `V` must be an actual Reed-Solomon code (of rate `ρ`, tied to `V` via
its degree/domain) rather than an arbitrary set of words: the conclusion is false for a `V` with
no algebraic structure connecting its elements, e.g. a `V` that is merely a "coincidentally
close" `Finset` unrelated to `ρ`. If more than `(l - 1) * n` points on the curve defined by `u`
are `δ`-close to `V`, then: every point of the curve is `δ`-close to `V`; there exist vectors `v`
from `V` such that every point of the `v`-curve is `δ`-close to the corresponding point of the
`u`-curve; and `u`, `v` agree outside a `δ`-fraction of coordinates. -/
theorem large_agreement_set_on_curve_implies_correlated_agreement {l : ℕ}
    {deg : ℕ}
    {domain : Fin n ↪ F}
    {δ : ℚ≥0}
    (hδ : δ ≤ (1 - ρ (ReedSolomon.code domain deg)) / 2)
    {u : Fin l → Fin n → F}
    (hS : (l - 1) * n <
      (coeffs_of_close_proximity_curve (F := F) δ u (ReedSolomon.code domain deg)).card) :
    (∀ z : F, δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z,
      ReedSolomon.code domain deg) ≤ δ) ∧
    ∃ v : Fin l → Fin n → F,
      (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
      (∀ z, δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z,
        Curve.polynomialCurveEval (F := F) (A := F) v z) ≤ δ) ∧
      ({ x : Fin n | ∃ i, u i x ≠ v i x } : Finset _).card ≤ δ * n := by
  sorry

/-- The distance bound from [BCIKS20]. -/
noncomputable def δ₀ (rho : ℚ) (m : ℕ) : ℝ :=
  1 - Real.sqrt rho - Real.sqrt rho / (2 * m)

/-- Johnson regime; Theorem 6.2 of [BCIKS20]. As in the unique-decoding companion
`large_agreement_set_on_curve_implies_correlated_agreement`, `V` must be an actual Reed-Solomon
code (of rate `ρ`) rather than an arbitrary set of words. If the set of points on the curve
defined by `u` close to `V` has more than
`((1 + 1 / (2 * m)) ^ 7 * m ^ 7) / (3 * (Real.rpow ρ (3 / 2 : ℚ))) * n ^ 2 * (l - 1)`
points, then there exist vectors `v` from `V` that are `(1 - δ) * n` close to `u`. -/
theorem large_agreement_set_on_curve_implies_correlated_agreement' {l : ℕ}
    [Finite F]
    {m : ℕ}
    {deg : ℕ}
    {domain : Fin n ↪ F}
    {δ : ℚ≥0}
    (hm : 3 ≤ m)
    (hδ : δ ≤ δ₀ (ρ (ReedSolomon.code domain deg)) m)
    {u : Fin l → Fin n → F}
    (hS : ((1 + 1 / (2 * m)) ^ 7 * m ^ 7) /
        (3 * (Real.rpow (ρ (ReedSolomon.code domain deg)) (3 / 2 : ℚ)))
      * n ^ 2 * (l - 1) <
      (coeffs_of_close_proximity_curve (F := F) δ u (ReedSolomon.code domain deg)).card) :
    ∃ v : Fin l → Fin n → F,
      (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
        (1 - δ) * n ≤ ({ x : Fin n | ∀ i, u i x = v i x } : Finset _).card := by
  sorry

end BCIKS20ProximityGapSection6

end ProximityGap
