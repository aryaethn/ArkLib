/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.EpsilonErrors
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ABF26Prelims
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Capacity-regime upper and lower bounds for ε_ca and ε_mca (ABF26 §4.2, §4.3)

External-admit *statements* for the §4 results that bound `ε_ca` and `ε_mca` from above
in the Johnson regime and from below in the capacity regime. From
*Open Problems in List Decoding and Correlated Agreement* (Arnon-Boneh-Fenzi,
April 8, 2026), §§4.2.2 and 4.3.

These theorems sit immediately above the Grand MCA Challenge in ABF26 §1: each one
either produces a witness `δ_C*` for `ε_mca(C, δ_C*) ≤ ε*` (upper bounds), or rules out
witnesses above a given threshold (lower bounds). They are mostly cited from external
papers ([GKL24], [BGKS20], [BCHKS25], [KK25], [CS25], [DG25], etc.); we state them
here in ArkLib's `ε_ca` / `ε_mca` form and admit the proofs as external results.

## Numeric bounds in `ENNReal`

The RHS of each upper bound is a real-valued numeric expression. To match the
`ENNReal`-valued return type of `epsCA` / `epsMCA`, we wrap the bound with
`ENNReal.ofReal`. The lower bounds use the same wrapping for symmetry. This keeps
the bounds well-defined even when the bracketing real expression is negative or
exceeds 1 (in which case `ENNReal.ofReal` either truncates to `0` or stays in `[0, ∞]`).

## Main statements (external admits)

### General linear codes

- `linear_epsMCA_1_5_johnson_gkl24` — ABF26 Theorem 4.11 [GKL24 Thm 3]: `ε_mca` bound
  in the "1.5-Johnson" regime `δ ≤ 1 - ∛(1 - δ_min(C) + η)`.
- `linear_epsCA_1_5_johnson_bgks20` — ABF26 Theorem 4.11 [BGKS20 Lem 3.2]: `ε_ca` bound
  with proximity loss `η`, valid in the same 1.5-Johnson regime.

### Reed-Solomon codes

- `rs_epsMCA_johnson_range_bchks25` — ABF26 Theorem 4.12 [BCHKS25 Thm 4.6]: explicit
  `ε_mca` bound for RS codes in the Johnson range `δ < 1 - √ρ₊ - η`, where
  `ρ₊ := ρ + 1/n`.

### Lower bounds near capacity

- `rs_epsCA_lower_capacity_bchks25_kk25` — ABF26 Theorem 4.16 [BCHKS25, KK25]:
  existence of RS codes for which `ε_ca` at distance `1 - ρ - slack` is at
  least `n^c / |F|` (where the `slack` is an existentially-bound `Θ(1/log n)`-shaped
  parameter; we expose it explicitly because Lean lacks a generic `Θ` notation).
- `rs_epsCA_breakdown_cs25` — ABF26 Theorem 4.17 [CS25 Cor 1]: complete CA breakdown
  for RS codes when the rate sits inside an entropy-defined band.
- `rs_epsCA_johnson_jump_bchks25` — ABF26 Theorem 4.18 [BCHKS25 Cor 1.7]: jump in
  `ε_ca` exactly at the Johnson bound, witnessed by characteristic-2 RS codes.
- `linear_epsCA_ge_sampling_dg25` — ABF26 Lemma 4.19 [DG25 Thm 2.5]: `ε_ca(C, δ)`
  is bounded below by `((q-1)/q) · Pr_{u}[Δ(u, C) ≤ δ]`.

## Deferred statements

- ABF26 Theorem 4.13 [GG25 Cor 4.9] (τ-subspace-design ⇒ MCA up to capacity) —
  blocked on the missing `IsSubspaceDesign` predicate.
- ABF26 Theorem 4.14 [GG25 Cor 4.10] (folded RS MCA up to capacity) — blocked on the
  missing `FRS` (folded Reed-Solomon) code family.
- ABF26 Theorem 4.15 [GG25 Thm 5.15] (random RS MCA up to capacity) — blocked on a
  uniform distribution over size-`n` subsets of `F`.

These are tracked in `ABF26_PLAN.md` §7 and will be stated alongside the corresponding
code-family definitions in Phase 3.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [GKL24] Theorem 3 in their paper.
- [BGKS20] Lemma 3.2 in their paper.
- [BCHKS25] Theorem 4.6 / Corollary 1.7 in their paper.
- [KK25] (cited alongside BCHKS25 in Theorem 4.16).
- [CS25] Corollary 1, source of Theorem 4.17.
- [DG25] Theorem 2.5, source of Lemma 4.19.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open ProximityGap

section General

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **ABF26 Theorem 4.11, Item 1 [GKL24 Thm 3].** For any linear error-correcting code
`C ⊆ F^n`, parameter `η > 0`, and `δ ≤ 1 - ∛(1 - δ_min(C) + η)`:

  `ε_mca(C, δ) ≤ ((n+6)/η + 2 / (η · (∛(1 - δ_min + η) - √(1 - δ_min + η))) ) · (1/|F|)`

The "1.5-Johnson regime" refers to the fact that `1 - ∛(1 - δ_min)` lies strictly above
the classical Johnson bound `1 - √(1 - δ_min)` and strictly below capacity. The bound is
admitted from the cited paper. -/
theorem linear_epsMCA_1_5_johnson_gkl24
    (C : Submodule F (ι → A)) (δ_min η δ : ℝ≥0)
    (_h_δ_min : (δ_min : ℝ) = (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι)
    (_hη : 0 < η)
    (_hδ : (δ : ℝ) ≤ 1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3))) :
    epsMCA (F := F) (A := A) ((C : Set (ι → A))) δ ≤
      ENNReal.ofReal
        ((((Fintype.card ι : ℝ) + 6) / η
          + 2 / ((η : ℝ) *
              ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3)
                - (1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 2)))
         ) / (Fintype.card F : ℝ)) := by
  sorry -- ABF26-T4.11 Item 1; external admit [GKL24 Thm 3].

/-- **ABF26 Theorem 4.11, Item 2 [BGKS20 Lem 3.2].** For any linear error-correcting code
`C ⊆ F^n`, parameter `η > 0`, and `δ ≤ 1 - ∛(1 - δ_min(C) + η)`:

  `ε_ca(C, δ_fld := δ, δ_int := δ + η) ≤ 2 / (η² · |F|)`

Same regime as the GKL24 form but stated in CA-with-proximity-loss shape. Tighter when the
GKL24 bound is dominated by its second term. Admitted from the cited paper. -/
theorem linear_epsCA_1_5_johnson_bgks20
    (C : Submodule F (ι → A)) (δ_min η δ : ℝ≥0)
    (_h_δ_min : (δ_min : ℝ) = (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι)
    (_hη : 0 < η)
    (_hδ : (δ : ℝ) ≤ 1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3))) :
    epsCA (F := F) (A := A) ((C : Set (ι → A))) δ (δ + η) ≤
      ((2 : ENNReal) / ((η : ENNReal) ^ 2 * (Fintype.card F : ENNReal))) := by
  sorry -- ABF26-T4.11 Item 2; external admit [BGKS20 Lem 3.2].

end General

section ReedSolomon

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **ABF26 Theorem 4.12 [BCHKS25 Thm 4.6].** For `C := RS[F, L, k]` with rate `ρ` and
`η > 0`, letting `ρ_plus := ρ + 1/n` and `m := max(⌈√ρ_plus/(2η)⌉, 3)`, for
`δ < 1 - √ρ_plus - η`:

  `ε_mca(C, δ) ≤ (1/|F|) · ( (2(m+½)⁵ + 3(m+½)·δ·ρ_plus) / (3·ρ_plus^{3/2}) · n
                              + (m+½)/√ρ_plus )`

The full numeric expression is preserved verbatim so future RS analyses can plug in
concrete `ρ`, `η`, and `n` values. Admitted as an external result. -/
theorem rs_epsMCA_johnson_range_bchks25
    (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0)
    (_hη : 0 < η)
    (_hδ :
        (δ : ℝ) <
          1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2))
            - (η : ℝ)) :
    epsMCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ ≤
      ENNReal.ofReal
        (let n : ℝ := Fintype.card ι
         let ρ_plus : ℝ := k / n + 1 / n
         let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
         ((2 * (m + 1/2) ^ 5 + 3 * (m + 1/2) * δ * ρ_plus)
            / (3 * ρ_plus ^ ((3 : ℝ) / 2)) * n
          + (m + 1/2) / ρ_plus ^ ((1 : ℝ) / 2))
           / (Fintype.card F : ℝ)) := by
  sorry -- ABF26-T4.12; external admit [BCHKS25 Thm 4.6].

/-- **ABF26 Theorem 4.16 [BCHKS25, KK25].** Existence: for every `c > 0` and rate
`ρ ∈ (0, 1/2)` there exists a power-of-two `n ∈ ℕ` and a Reed-Solomon code
`C := RS[F, L, k]` of rate `ρ` over a prime field `F` with `|F| = poly(n)` and smooth
`L` of size `n` such that

  `ε_ca(C, 1 - ρ - slack) ≥ n^c / |F|`

for some `slack` of order `Θ(1/log n)`. We existentially bind the slack parameter as a
real-valued knob rather than encoding `Θ` directly. -/
theorem rs_epsCA_lower_capacity_bchks25_kk25
    (c : ℝ≥0) (_hc : 0 < c) (ρ : ℝ≥0) (_hρ_pos : 0 < ρ) (_hρ_lt : ρ < (1 / 2 : ℝ≥0)) :
    ∃ (ιC : Type) (_ : Fintype ιC) (_ : Nonempty ιC) (_ : DecidableEq ιC)
      (FC : Type) (_ : Field FC) (_ : Fintype FC) (_ : DecidableEq FC)
      (domain : ιC ↪ FC) (k : ℕ) (slack : ℝ≥0),
      (k : ℝ) / Fintype.card ιC = ρ ∧
      epsCA (F := FC) (A := FC) ((ReedSolomon.code domain k : Set (ιC → FC)))
          (1 - ρ - slack) (1 - ρ - slack) ≥
        ((Fintype.card ιC : ENNReal) ^ (c : ℝ)) / (Fintype.card FC : ENNReal) := by
  sorry -- ABF26-T4.16; external admit [BCHKS25, KK25].

/-- **ABF26 Theorem 4.17 [CS25 Cor 1].** Complete CA breakdown for Reed-Solomon codes.
Let `C := RS[F, L, k]` with `q = |F| ≥ 10`, rate `ρ`, and `δ` satisfying:

  `1 - H_q(δ) + 2/n + √((H_q(δ) - δ)/n) ≤ ρ ≤ 1 - δ - 2/n`

Then `ε_ca(C, δ) = 1`. Uses `qEntropy` (ABF26 Definition 2.2, defined in
`ABF26Prelims.lean`). Admitted as an external result. -/
theorem rs_epsCA_breakdown_cs25
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (_hq_ge : 10 ≤ Fintype.card F)
    (_hδ_lo :
        1 - qEntropy (Fintype.card F) (δ : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((qEntropy (Fintype.card F) (δ : ℝ) - (δ : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (_hδ_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ : ℝ) - 2 / (Fintype.card ι : ℝ)) :
    epsCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ δ = 1 := by
  sorry -- ABF26-T4.17; external admit [CS25 Cor 1].

/-- **ABF26 Theorem 4.18 [BCHKS25 Cor 1.7].** CA jump at the Johnson bound. Fix `ε > 0`,
let `δ := 15/16`. Then for all `F` of characteristic 2 there exists a Reed-Solomon code
`C := RS[F, L, k]` with `n = |F|^{(1+ε)/2}` and `δ_min(C) = 15/16` such that:

  `ε_ca(C, J(δ_min(C)), J(δ_min(C)) + 1/8 + 1/n) ≥ n^{2(1-ε)} / |F|`

where `J(δ) := 1 - √(1 - δ)` is the Johnson radius. Witnesses a sharp jump in CA
error precisely at the Johnson bound. Admitted as an external result. -/
theorem rs_epsCA_johnson_jump_bchks25
    (ε : ℝ≥0) (_hε : 0 < ε) :
    ∃ (ιC : Type) (_ : Fintype ιC) (_ : Nonempty ιC) (_ : DecidableEq ιC)
      (FC : Type) (_ : Field FC) (_ : Fintype FC) (_ : DecidableEq FC),
      CharP FC 2 ∧ ∃ (domain : ιC ↪ FC) (k : ℕ),
      (Fintype.card ιC : ℝ) = (Fintype.card FC : ℝ) ^ (((1 : ℝ) + ε) / 2) ∧
      (Code.minDist ((ReedSolomon.code domain k : Set (ιC → FC))) : ℝ)
          / Fintype.card ιC = (15 : ℝ) / 16 ∧
      epsCA (F := FC) (A := FC) ((ReedSolomon.code domain k : Set (ιC → FC)))
          (((1 : ℝ) - (1 - ((15 : ℝ) / 16)) ^ ((1 : ℝ) / 2)).toNNReal)
          (((1 : ℝ) - (1 - ((15 : ℝ) / 16)) ^ ((1 : ℝ) / 2)
              + 1 / 8 + 1 / (Fintype.card ιC : ℝ)).toNNReal) ≥
        ((Fintype.card ιC : ENNReal) ^ (2 * ((1 : ℝ) - ε)))
          / (Fintype.card FC : ENNReal) := by
  sorry -- ABF26-T4.18; external admit [BCHKS25 Cor 1.7].

end ReedSolomon

section Sampling

open scoped ProbabilityTheory

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **ABF26 Lemma 4.19 [DG25 Thm 2.5].** Let `C ⊆ F^n` be a linear code and let
`δ' := max_{u ∈ F^n} Δ(u, C)` be the (relative) covering radius. For every
`δ ∈ (0, δ')`:

  `ε_ca(C, δ) ≥ ((q-1)/q) · Pr_{u ← F^n}[Δ(u, C) ≤ δ]`

The probability is over a uniform word in `F^n`, expressed via the `Pr_{...}[...]`
notation. Admitted as an external result. -/
theorem linear_epsCA_ge_sampling_dg25
    (C : Submodule F (ι → F)) (δ δ' : ℝ≥0)
    (_h_δ' : (δ' : ENNReal) = ⨆ u : ι → F, δᵣ(u, (C : Set (ι → F))))
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < δ') :
    ((Fintype.card F - 1 : ℝ≥0) / Fintype.card F : ENNReal)
        * Pr_{let u ← $ᵖ (ι → F)}[δᵣ(u, (C : Set (ι → F))) ≤ δ] ≤
      epsCA (F := F) (A := F) ((C : Set (ι → F))) δ δ := by
  sorry -- ABF26-L4.19; external admit [DG25 Thm 2.5].

end Sampling

end CodingTheory
