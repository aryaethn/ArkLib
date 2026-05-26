/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.MvPolynomial.RestrictDegree

/-!
# Structured (Witness-Mode) Sumcheck — Types and Helpers

This file collects the data types and degree-bookkeeping helpers used by the
**structured sumcheck**: the witness-mode degree-2 multilinear-times-multilinear sumcheck
that underlies Binius BinaryBasefold, Binius RingSwitching, and (in the future) Hachi.

Unlike the canonical, oracle-mode sumcheck in `ArkLib/ProofSystem/Sumcheck/Spec/*`, where
the polynomial being sumchecked is an oracle statement accessible to the verifier, here
the polynomial `H = m · t` is the prover's *witness*: `t` is a committed multilinear, `m`
is a context-dependent multilinear multiplier, and `H` is their degree-2 product. The
verifier sees only the prover's round polynomials `pᵢ`, not `H` directly.

The two modes coexist as parallel primitives under `Sumcheck`.

## TODO (option C, tracked separately)

A refinement theorem connecting the two modes — given `H = m · t`, derive structured-mode
soundness from canonical-mode soundness — is left for follow-up work. Until then, the two
modes carry independent proofs.

## Contents (lifted from `Binius.BinaryBasefold.Basic` § `SumcheckOperations` and
`Binius.RingSwitching.SumcheckWitness`)

- `MultilinearPoly`, `MultiquadraticPoly` — degree-1 / degree-2 `MvPolynomial` abbreviations.
- `SumcheckMultiplierParam` — bundles a `Context → MultilinearPoly` (the multiplier `m`).
- `computeInitialSumcheckPoly` — `H := m · t` with the degree-2 proof.
- `projectToMidSumcheckPoly`, `projectToNextSumcheckPoly` — partial evaluation of `H` at
  the verifier's previous challenges.
- `SumcheckBaseContext` — `(t_eval_point, original_claim)` shared input.
- `Statement Context i` — per-round state: `(sumcheck_target, challenges, ctx)`.
- `sumcheckConsistencyProp` — claim equals hypercube sum.
- `SumcheckWitness` — per-round witness `(t', H)` (the committed multilinear + projected
  round polynomial).
-/

noncomputable section

namespace Sumcheck.Structured

open Finset MvPolynomial

section SumcheckOperations

abbrev MultilinearPoly (L : Type) [CommSemiring L] (ℓ : ℕ) := L⦃≤ 1⦄[X Fin ℓ]
abbrev MultiquadraticPoly (L : Type) [CommSemiring L] (ℓ : ℕ) := L⦃≤ 2⦄[X Fin ℓ]

/-- We treat the multiplier poly as a blackbox for protocol abstraction.
For example, in Binary Basefold it's `eqTilde(r₀, .., r_{ℓ-1}, X₀, .., X_{ℓ-1})` -/
structure SumcheckMultiplierParam (L : Type) [CommRing L] (ℓ : ℕ) (Context : Type := Unit) where
  multpoly : (ctx: Context) → MultilinearPoly L ℓ

-- The variable block matches the original `Binius.BinaryBasefold.Basic`'s line-19 block
-- (`ℓ` explicit + `[NeZero ℓ]` instance) so that positional callers like
-- `projectToMidSumcheckPoly ℓ wit.t ...` continue to typecheck. PR 4 will weaken these
-- once `ProofSystem/RingSwitching/*` no longer uses positional `ℓ`.
variable {L : Type} [CommRing L] (ℓ : ℕ) [NeZero ℓ]

/-- `H₀(X₀, ..., X_{ℓ-1}) = h(X₀, ..., X_{ℓ-1}) =`
  `m(X_0, ..., X_{ℓ-1}) · t(X_0, ..., X_{ℓ-1})` -/
def computeInitialSumcheckPoly (t : MultilinearPoly L ℓ)
    (m : MultilinearPoly L ℓ) : MultiquadraticPoly L ℓ :=
  ⟨m * t, by
    rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
    intro i
    have h_t_deg: degreeOf i t.val ≤ 1 :=
      degreeOf_le_iff.mpr fun term a ↦ (t.property) a i
    have h_m_deg: degreeOf i m.val ≤ 1 :=
      degreeOf_le_iff.mpr fun term a ↦ (m.property) a i
    calc
      _ ≤ (degreeOf i m.val) + (degreeOf i t.val) :=
        degreeOf_mul_le i m.val t.val
      _ ≤ 2 := by omega
  ⟩

/-- `Hᵢ(Xᵢ, ..., X_{ℓ-1}) = ∑ ω ∈ 𝓑ᵢ, H₀(ω₀, …, ω_{i-1}, Xᵢ, …, X_{ℓ-1}) (where H₀=h)` -/
def projectToMidSumcheckPoly (t : MultilinearPoly L ℓ)
    (m : MultilinearPoly L ℓ) (i : Fin (ℓ + 1))
    (challenges : Fin i → L)
    : MultiquadraticPoly L (ℓ-i) :=
  let H₀: MultiquadraticPoly L ℓ := computeInitialSumcheckPoly (ℓ:=ℓ) t m
  let Hᵢ := fixFirstVariablesOfMQP (ℓ := ℓ) (v := ⟨i, by omega⟩)
    (H := H₀) (challenges := challenges)
  ⟨Hᵢ, by
    have hp := H₀.property
    simpa using
      (fixFirstVariablesOfMQP_degreeLE (L := L) (ℓ := ℓ) (v := ⟨i, by omega⟩)
        (poly := H₀.val) (challenges := challenges) (deg := 2) hp)
  ⟩

/-- Derive `H_{i+1}` from `H_i` by projecting the first variable -/
def projectToNextSumcheckPoly (i : Fin (ℓ)) (Hᵢ : MultiquadraticPoly L (ℓ - i))
    (rᵢ : L) : -- the current challenge
    MultiquadraticPoly L (ℓ - i.succ) := by
  let projectedH := fixFirstVariablesOfMQP (ℓ := ℓ - i) (v := ⟨1, by omega⟩)
    (H := Hᵢ.val) (challenges := fun _ => rᵢ)
  exact ⟨projectedH, by
    have hp := Hᵢ.property
    simpa using
      (fixFirstVariablesOfMQP_degreeLE (L := L) (ℓ := ℓ - i) (v := ⟨1, by omega⟩)
        (poly := Hᵢ.val) (challenges := fun _ => rᵢ) (deg := 2) hp)
  ⟩

end SumcheckOperations

section ContextAndStatement

/-- Input context for the sumcheck protocol, used mainly in BinaryBasefold.
For other protocols, there might be other context data.
NOTE: might add a flag `rejected` to indicate if prover has been rejected before. But that seems
like a fundamental feature of OracleReduction instead, so no action taken for now. -/
structure SumcheckBaseContext (L : Type) (ℓ : ℕ) where
  t_eval_point : Fin ℓ → L         -- r = (r_0, ..., r_{ℓ-1}) => shared input
  original_claim : L               -- s = t(r) => the original claim to verify

-- `[NeZero ℓ]` matches the original auto-bind on `Statement` (the variable block in
-- `Binius.BinaryBasefold.Basic` line 384 had `[NeZero ℓ]` in scope, so `Statement` carried it).
variable {L : Type} {ℓ : ℕ} [NeZero ℓ]

/-- Statement per iterated sumcheck round -/
structure Statement (Context : Type) (i : Fin (ℓ + 1)) where
  -- Current round state
  sumcheck_target : L              -- s_i (current sumcheck target for round i)
  challenges : Fin i → L           -- R'_i = (r'_0, ..., r'_{i-1}) from previous rounds
  ctx : Context -- external context for composition from the outer protocol

end ContextAndStatement

section ConsistencyProp

variable {L : Type} [CommRing L]
variable {𝓑 : Fin 2 ↪ L}

/-- Sumcheck consistency: the claimed sum equals the actual polynomial evaluation sum -/
def sumcheckConsistencyProp {k : ℕ} (sumcheckTarget : L) (H : L⦃≤ 2⦄[X Fin (k)]) : Prop :=
  sumcheckTarget = ∑ x ∈ (univ.map 𝓑) ^ᶠ (k), H.val.eval x

end ConsistencyProp

section Witness

/-- Witness for the structured sumcheck at round `i`:
- `t'` — the original multilinear polynomial (the "data" being committed); same across rounds.
- `H`  — the projected round polynomial `H_i(X_i, …, X_{ℓ-1})`, equal to the multiquadratic
  product `m · t'` with the first `i` variables fixed to the verifier's previous challenges.

Lifted from `Binius.RingSwitching.SumcheckWitness`. Generic in shape; PR 2b's per-round
prover/verifier consume this witness uniformly across all structured-sumcheck instantiations. -/
structure SumcheckWitness (L : Type) [CommSemiring L] (ℓ : ℕ) (i : Fin (ℓ + 1)) where
  t' : MultilinearPoly L ℓ
  H : L⦃≤ 2⦄[X Fin (ℓ - i)]

end Witness

end Sumcheck.Structured
