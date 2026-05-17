/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.ProofSystem.ToyProblem.Spec.General

/-!
# Simplified toy-problem IOR (ABF26 Construction 6.9)

The "attack target" simplified IOR from ABF26 §6.4. Unlike the full
Construction 6.2, this version:

  * has **one round** (V→P combination randomness only — no spot-check),
  * does **not** test acceptance (no final `guard`); instead it
    *reduces* the input instance `(v, μ₁, μ₂, f₁, f₂)` to a smaller
    instance `(v, μ₁ + γ·μ₂, f₁ + γ·f₂)`,
  * is therefore a reduction from `R̃²_{C,δ}` to `R̃¹_{C,δ}`.

This file follows the FRI/Sumcheck `Spec/` convention exactly (mirroring
`ToyProblem/Spec/General.lean`). The two protocols live in sibling
files because they are structurally distinct (C6.2 is a 3-round
yes/no test; C6.9 is a 1-round reducing protocol).

## Protocol

```
Verifier input  : (v, μ₁, μ₂) explicit, (f₁, f₂) oracle.
Prover witness  : (M₁, M₂) ∈ (F^k)² with C(Mᵢ) = fᵢ, ⟨Mᵢ, v⟩ = μᵢ.

Round 0  V → P : γ ←$ F.
Outputs:
  Verifier sets statement x* := (v, μ₁ + γ·μ₂) and oracle y* := f₁ + γ·f₂.
  Honest prover sets witness w* := M₁ + γ·M₂.
```

The new instance lies in `R̃¹_{C,δ}` iff the original lay in
`R̃²_{C,δ}` (up to the soundness error of L6.10).

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§6.4, Construction 6.9, Lemma 6.10).
-/

namespace ToyProblem

namespace SimplifiedIOR

open OracleSpec OracleComp ProtocolSpec
open scoped NNReal
open ToyProblem.Spec (Statement OracleStatement Witness)

variable {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Fintype F]
         [DecidableEq F]

variable (k : ℕ)

/-- Output statement for C6.9: the new `(v, μ_new)` pair. The
constraint count drops from 2 to 1 (a single combined linear
constraint). -/
@[reducible]
def OutputStatement : Type := (Fin k → F) × F

/-- Output oracle statement: the single combined codeword
`f_new := f₁ + γ·f₂ : ι → F`. -/
@[reducible]
def OutputOracleStatement (ι F : Type) : Fin 1 → Type := fun _ ↦ ι → F

/-- Output witness for C6.9: the combined message `M_new := M₁ + γ·M₂`. -/
@[reducible]
def OutputWitness : Type := Fin k → F

/-- Protocol specification for Construction 6.9: a single
`V → P` round sending the combination randomness `γ : F`. -/
@[reducible]
def pSpec : ProtocolSpec 1 :=
  ⟨!v[.V_to_P], !v[F]⟩

instance : ∀ j, OracleInterface ((pSpec (F := F)).Message j)
  | ⟨0, h⟩ => nomatch h

instance : ∀ j, OracleInterface ((pSpec (F := F)).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

instance [SampleableType F] : ∀ j, SampleableType ((pSpec (F := F)).Challenge j)
  | ⟨0, _⟩ => (inferInstance : SampleableType F)

/-- Honest prover for Construction 6.9. After receiving `γ`, sets the
new witness `M_new := M₀ + γ·M₁` and outputs the reduced instance.

State machine (`PrvState : Fin 2 → Type`):
  * `PrvState 0` — initial: bundled `(stmt, oStmt) × witness`.
  * `PrvState 1` — after receiving γ: `γ × bundle`. -/
def prover :
    Prover []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι F i)) (Witness (F := F) k)
      (OutputStatement (F := F) k × (∀ i, OutputOracleStatement ι F i)) (OutputWitness (F := F) k)
      (pSpec (F := F)) where
  PrvState
  | ⟨0, _⟩ =>
      (Statement (F := F) k × (∀ i, OracleStatement ι F i)) × Witness (F := F) k
  | _ =>
      F × (Statement (F := F) k × (∀ i, OracleStatement ι F i)) × Witness (F := F) k

  input := id

  receiveChallenge
  | ⟨0, _⟩ => fun st ↦ pure <| fun (γ : F) ↦ (γ, st)

  sendMessage
  | ⟨0, h⟩ => nomatch h

  output := fun ⟨γ, ⟨stmt, oStmt⟩, M⟩ ↦ pure <|
    ⟨⟨(stmt.1, stmt.2.1 + γ * stmt.2.2),
       fun _ ↦ fun j ↦ oStmt 0 j + γ * oStmt 1 j⟩,
      fun j ↦ M 0 j + γ * M 1 j⟩

/-- Honest verifier for Construction 6.9. Reads `γ` from the transcript
and produces the new statement `(v, μ₁ + γ·μ₂)` and oracle
`f_new := f₁ + γ·f₂`. Always accepts — the "test" semantics of C6.2
become a "reduce" semantics here.

`encode` is not used (the reduced instance is what it is — testing it
against the code is a separate downstream concern). -/
def verifier :
    Verifier []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι F i))
      (OutputStatement (F := F) k × (∀ i, OutputOracleStatement ι F i))
      (pSpec (F := F)) where
  verify := fun ⟨stmt, oStmt⟩ tr ↦ do
    let γ : F := tr ⟨0, by decide⟩
    pure ((stmt.1, stmt.2.1 + γ * stmt.2.2),
           fun _ ↦ fun j ↦ oStmt 0 j + γ * oStmt 1 j)

/-- Honest reduction for Construction 6.9. -/
def reduction :
    Reduction []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι F i)) (Witness (F := F) k)
      (OutputStatement (F := F) k × (∀ i, OutputOracleStatement ι F i)) (OutputWitness (F := F) k)
      (pSpec (F := F)) where
  prover := prover (ι := ι) (F := F) (k := k)
  verifier := verifier (k := k)

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- **Lemma 6.10 of [ABF26]** (knowledge soundness of Construction 6.9).

For any `δ ∈ (0, δ_min(C))`, the simplified IOR has knowledge soundness
(paper Def A.5) from `R̃²_{C,δ}` to `R̃¹_{C,δ}` with error

  `ε_mca(C, δ) + |Λ(C^{≡2}, δ)| / |F|`.

Note the cleaner error term compared with L6.6: there's no `(1-δ)^t`
spot-check term because C6.9 has no spot-check round.

The proof is the "1-round version" of L6.8's KnowledgeStateFunction
construction; same extractor strategy (erasure-decode against the
agreement set). Tagged sorry. -/
theorem simplifiedIOR_knowledgeSound
    [SampleableType F]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (C : Set (ι → F)) (δ : ℝ≥0)
    (_hδ_pos : 0 < δ) :
    ∃ knowledgeError : ℝ≥0,
      (verifier (ι := ι) (F := F) (k := k)).knowledgeSoundness
        (WitOut := OutputWitness (F := F) k)
        init impl
        (ToyProblem.Spec.outputRelation k C δ)
        (ToyProblem.Spec.outputRelation₁ (ι := ι) (F := F) k C δ)
        knowledgeError := by
  -- ABF26-L6.10; the intended `knowledgeError` is
  -- `epsMCA C δ + Lambda (interleavedCodeSet C) δ / |F|`.
  sorry

end SimplifiedIOR

end ToyProblem
