/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.ProofSystem.ToyProblem.Definitions
import ArkLib.ProofSystem.ToyProblem.SoundnessBounds
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.ToVCVio.OracleComp.SimSemantics.SimulateQ
import ArkLib.ToVCVio.OracleComp.RbrGame

/-!
# Toy problem oracle reduction (ABF26 Construction 6.2)

We describe the ABF26 §6 toy-problem IOR as an `OracleReduction` over
ArkLib's `OracleReduction` framework, following the conventions used by
`ArkLib/ProofSystem/Fri/Spec/SingleRound.lean` and
`ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean`:

* `Statement`, `OracleStatement`, `Witness`, `OutputStatement` — input /
  oracle / witness / output type aliases (all `@[reducible]`).
* `pSpec` — the 3-round `ProtocolSpec` (`V → P` γ, `P → V` g, `V → P`
  spot-checks).
* `OracleInterface`, `Inhabited`, `Fintype` instances for the messages
  and challenges of `pSpec`.
* `inputRelationFor` / `outputRelationFor` — IOR input/output relations
  (Definitions 6.1 and 6.3, in IOR shape, pinned to the verifier's fixed
  encoder).
* `accepts` — the §6.1 decision predicate (extracted for use by the
  verifier and by completeness proofs).

The `prover` / `verifier` / `oracleReduction` triple is complete.
Completeness (C6.2, `oracleReduction_perfectCompleteness`) and
round-by-round knowledge soundness (L6.8,
`protocol62_rbrKnowledgeSound`) are **fully proven** here. Plain
knowledge soundness (L6.6, `protocol62_knowledgeSound`) is **fully
proven** in the sibling file `Spec/KnowledgeSoundness.lean`, with the
**corrected** sum-form error
`(ε_mca(C,δ) + |Λ(C^{≡2},δ)|/|F|) + (1-δ)^t`: the paper's claimed `max`
of the two terms is **false as stated** (its proof swaps conditional for
unconditional probabilities; there is a concrete counterexample) — see
`PAPER_REVS.md` item 11. The per-round game bounds proven in this file
(`gamma_round_game_bound`, `spotcheck_round_game_bound`) are shared by
both the L6.8 and L6.6 proofs.

## Protocol description

The verifier holds an explicit input `(v, μ₁, μ₂)` and has oracle
access to two purported codewords `f₁, f₂ : ι → F`. The protocol runs:

  1. **Combination randomness** (V → P): the verifier sends `γ ←$ F`.
  2. **Prover claim** (P → V): the prover sends `g : Fin k → F`. In the
     honest case `g = M₁ + γ · M₂` is the combination of the underlying
     messages.
  3. **Spot-check randomness** (V → P): the verifier sends
     `x₁, …, xₜ ←$ ι`.

The verifier accepts iff `⟨g, v⟩ = μ₁ + γ · μ₂` (linear-constraint
check) and for every `j ∈ Fin t`, `encode(g)(xⱼ) = f₁(xⱼ) + γ · f₂(xⱼ)`
(spot-check).

## Paper ↔ framework mapping

How each step of Construction 6.2 lands on an ArkLib / VCV-io primitive:

* `γ ←$ F` (combination randomness) ↦ `pSpec` round 0 (`.V_to_P`); the
  security games sample it via the `SampleableType F` instance on the
  challenge type.
* prover claim `ḡ ∈ F^k` ↦ `pSpec` round 1 (`.P_to_V`), with
  `OracleInterface.instDefault` as its message-oracle interface.
* spot-check positions `x₁, …, xₜ` ↦ `pSpec` round 2 (`.V_to_P`), of
  type `Fin t → ι`.
* oracle access to `f₁, f₂` ↦ `OracleStatement` queried via `queryF`,
  routed through the per-index `OracleInterface` instances.
* the §6.1 decision predicate ↦ `accepts`.
* verifier query routing ↦ `OracleInterface.simOracle2` / `simulateQ`
  (VCV-io's query-simulation semantics).
* completeness game ↦ `OracleReduction.perfectCompleteness`.
* knowledge-soundness games (paper App A.1, Defs A.2 / A.4 / A.5) ↦
  `OracleVerifier.knowledgeSoundness` / `OracleVerifier.rbrKnowledgeSoundness`.
  Two caveats: extraction **time** (the paper's `O(enc + ecor)` extractor
  cost) is outside ArkLib's cost-free model, and the verifier's query
  complexity (`2t + 1`) is documented, not enforced
  (`OracleVerifier.numQueries` is upstream-sorried).

## Alphabet restriction (`s = 1`)

The paper's Construction 6.1/6.2 inputs are `f : [n] → F^s` for a folding
parameter `s` (and the §6.3 tables sweep `s = 2^0, …, 2^12`). This
formalization fixes `s = 1`: words are `ι → F`, not `ι → F^s`. This is a
genuine scope restriction, not mere notational choice — reindexing
`ι := [n] × [s]` does **not** recover the general case, because the
relative Hamming metric over the alphabet `F^s` (one symbol = one
`F^s`-coordinate) differs from the metric over `F` on the flattened
index set. The §6.3 `s`-sweep therefore needs the `F^s` generalization,
planned for Phase-5 `Impl/FRS`. The `s = 2^0` rows of the paper's tables
fall squarely inside the current form, so the `s = 1` formalization is
non-vacuous for the prize regime.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§6).
-/

namespace ToyProblem

namespace Spec

open OracleSpec OracleComp ProtocolSpec
open Code InterleavedCode ListDecodable ProximityGap
open scoped NNReal ENNReal ProbabilityTheory

/-! ### Type-level definitions and relations

The relations need `[Fintype ι]` (for `relaxedRelationFor`'s
`Fintype.card ι` call) and `[Field F]` (for the `→ₗ[F]` encoder). The
heavier `[DecidableEq ι] [Fintype F] [DecidableEq F]` instances come
in below for the protocol-object definitions. -/

variable {ι F : Type} [Fintype ι] [Field F]
variable (k t : ℕ)

/-- Input (explicit) statement of Construction 6.2: the linear-constraint
vector `v ∈ F^k` and the two constraint values `(μ₁, μ₂) ∈ F²`. -/
@[reducible]
def Statement : Type := (Fin k → F) × F × F

/-- Oracle statements of Construction 6.2: the two purported codewords
`f₁, f₂ : ι → F`. The verifier only queries them at the spot-check
positions. -/
@[reducible]
def OracleStatement (ι F : Type) : Fin 2 → Type := fun _ ↦ ι → F

instance : ∀ i, OracleInterface (OracleStatement ι F i) :=
  fun _ ↦ inferInstance

/-- Honest witness: the underlying messages `M₁, M₂ : Fin k → F` whose
encodings are the oracle codewords `f₁, f₂`. -/
@[reducible]
def Witness : Type := Fin 2 → Fin k → F

/-- Output statement: the IOR is a yes/no test — accept (return `()`) or
short-circuit to `none` via `OptionT`. -/
@[reducible]
def OutputStatement : Type := Unit

/-- Output oracle statement: the IOR has no output oracle component. -/
@[reducible]
def OutputOracleStatement : (Fin 0) → Type := nofun

/-- Output witness: empty. -/
@[reducible]
def OutputWitness : Type := Unit

/-- Protocol specification for Construction 6.2: three rounds, in the
order

    V → P  (γ : F)            -- combination randomness
    P → V  (g : Fin k → F)    -- combined message claim
    V → P  (xs : Fin t → ι)   -- spot-check positions.

Marked `@[reducible]` so per-round type access `pSpec.Type i` reduces
in client code (cf. FRI / Sumcheck single-round specs). -/
@[reducible]
def pSpec : ProtocolSpec 3 :=
  ⟨!v[.V_to_P, .P_to_V, .V_to_P],
   !v[F, Fin k → F, Fin t → ι]⟩

instance : ∀ j, OracleInterface ((pSpec (ι := ι) (F := F) k t).Message j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => OracleInterface.instDefault
  | ⟨2, h⟩ => nomatch h

instance : ∀ j, OracleInterface ((pSpec (ι := ι) (F := F) k t).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

/-- The challenges of the toy-problem `pSpec` are `SampleableType` when
the underlying field `F` and the codeword index `ι` are. This is needed
to instantiate the (round-by-round) knowledge-soundness games, which
sample challenges from the protocol's challenge spaces. -/
instance [SampleableType F] [SampleableType ι] :
    ∀ j, SampleableType ((pSpec (ι := ι) (F := F) k t).Challenge j)
  | ⟨0, _⟩ => (inferInstance : SampleableType F)
  | ⟨1, h⟩ => nomatch h
  | ⟨2, _⟩ => (inferInstance : SampleableType (Fin t → ι))

/-- The §6.1 decision predicate, factored out so completeness proofs and
the verifier object share the same statement.

Given the explicit input `(v, μ₁, μ₂)`, the oracle codewords
`(f 0, f 1)`, the challenge `γ`, the prover's claim `g`, the spot-check
positions `xs`, and an encoding function `encode`, the verifier accepts
iff:

  * `⟨g, v⟩ = μ₁ + γ · μ₂` (linear constraint), and
  * `∀ j, encode(g)(xs j) = f 0 (xs j) + γ · f 1 (xs j)` (per-spot-check).
-/
def accepts (encode : (Fin k → F) → (ι → F))
    (stmt : Statement (F := F) k) (f : ∀ i, OracleStatement ι F i)
    (γ : F) (g : Fin k → F) (xs : Fin t → ι) : Prop :=
  (∑ j, g j * stmt.1 j = stmt.2.1 + γ * stmt.2.2) ∧
  ∀ j : Fin t, encode g (xs j) = f 0 (xs j) + γ * f 1 (xs j)

/-- The IOR-shaped **fixed-encoding** input relation (Definition 6.1).

`((v, μ₁, μ₂), (f₀, f₁)) ∈ inputRelationFor encode` with witness `M`
iff the oracle codewords are the `encode`-images of the witness messages
(`fᵢ = encode (M i)`) and the witness satisfies the linear constraint
(`⟨M i, v⟩ = μᵢ`). The encoding is the verifier's **fixed** `encode` (a plain
function, matching `oracleVerifier`), and the witness `M` is tied to the
statement — this is what the honest prover sends `g = M₀ + γ·M₁` against and
what `accepts_of_inputRelation` consumes.

This replaces the earlier existential-encoding form (`ToyProblem.relation`,
`∃ encode'`), under which honest completeness is unprovable / false: the honest
prover's `encode g` need not match `fᵢ = encode' (Mᵢ)` when `encode' ≠ encode`
(the same defect found for the L6.12 attack — see `ToyProblem.relationFor`). -/
def inputRelationFor (encode : (Fin k → F) → (ι → F)) :
    Set ((Statement (F := F) k × (∀ i, OracleStatement ι F i)) ×
      Witness (F := F) k) :=
  fun input ↦
    (∀ i : Fin 2, input.1.2 i = encode (input.2 i)) ∧
    (∀ i : Fin 2, ∑ j, input.2 i j * input.1.1.1 j = ![input.1.1.2.1, input.1.1.2.2] i)

/-- The IOR-shaped **fixed-encoding** *relaxed* output relation (Definition 6.3).
The soundness statement of L6.6/6.8 is with respect to this: the verifier's
"accept" guarantee is that the input `(f₀, f₁)` is `δ`-close (on a common
agreement column set) to a valid instance `encode (M i)` for some constraint-
satisfying messages `M`. Uses the verifier's fixed plain `encode` (cf.
`ToyProblem.relaxedRelationFor`), and checks the witness component supplied by
the ArkLib knowledge extractor; this is a witness-bearing relation, not merely
language membership. -/
def outputRelationFor (encode : (Fin k → F) → (ι → F)) (δ : ℝ≥0) :
    Set ((Statement (F := F) k × (∀ i, OracleStatement ι F i)) ×
      Witness (F := F) k) :=
  fun input ↦
    (∀ i : Fin 2, ∑ j, input.2 i j * input.1.1.1 j =
      ![input.1.1.2.1, input.1.1.2.2] i) ∧
    ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
      ∀ i : Fin 2, ∀ j ∈ S, input.1.2 i j = encode (input.2 i) j

-- The 1-arity relaxed relation `R̃¹_{C,δ}` lives in
-- `Spec/SimplifiedIOR.lean :: outputRelationFor` (the C6.9 output relation).
-- We expose it from the simplified-IOR file rather than here so its
-- type signature aligns with `SimplifiedIOR.OutputStatement` /
-- `OutputOracleStatement` / `OutputWitness` rather than re-bundling.

/-! ### Honest prover, verifier, and reduction

This section mirrors the `foldProver` / `foldVerifier` / `foldOracleReduction`
pattern in [`Fri/Spec/SingleRound.lean`](../../../Fri/Spec/SingleRound.lean).
Because `OracleStatement ι F i = ι → F` is a plain function (not an
oracle that needs the `OracleQuery` machinery), we use the **non-oracle**
`Prover` / `Verifier` / `Reduction` triple with the oracle codewords
threaded through the bundled input `StmtIn = Statement × (∀ i, OracleStatement i)`.
This is sound — it's the same shape produced by
`OracleReduction.toReduction` — and avoids the `embed` / `hEq`
plumbing. The `OracleProver` / `OracleVerifier` flavour (the target of
the completeness and soundness statements) follows in the next section.
-/

section Protocol
variable [DecidableEq ι] [Fintype F] [DecidableEq F]

/-- Honest prover for Construction 6.2. After receiving the combination
randomness `γ`, the prover sends `g := M 0 + γ · M 1` (point-wise on
`Fin k`). The spot-check positions `xs` are not used by the prover —
they only feed the verifier's spot-check at the end.

State machine (`PrvState : Fin 4 → Type`):
  * `PrvState 0` — initial: the bundled `(stmt, oStmt) × witness`.
  * `PrvState 1, 2, 3` — same plus the combination randomness `γ`. -/
def prover :
    Prover []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι F i)) (Witness (F := F) k)
      OutputStatement OutputWitness
      (pSpec (ι := ι) (F := F) k t) where
  PrvState
  | ⟨0, _⟩ =>
      (Statement (F := F) k × (∀ i, OracleStatement ι F i)) × Witness (F := F) k
  | _ =>
      F × (Statement (F := F) k × (∀ i, OracleStatement ι F i)) × Witness (F := F) k

  input := id

  receiveChallenge
  | ⟨0, _⟩ => fun st ↦ pure <| fun (γ : F) ↦ (γ, st)
  | ⟨1, h⟩ => nomatch h
  | ⟨2, _⟩ => fun ⟨γ, st⟩ ↦ pure <| fun (_ : Fin t → ι) ↦ (γ, st)

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨γ, ⟨stmt, oStmt⟩, M⟩ ↦
      pure ((fun j ↦ M 0 j + γ * M 1 j), (γ, ⟨stmt, oStmt⟩, M))
  | ⟨2, h⟩ => nomatch h

  output := fun _ ↦ pure ((), ())

/-- The §6.1 decision predicate is decidable: it's a finite conjunction
of equalities in `F` (decidable via `DecidableEq F`) and a `Fin t`
universally-quantified equality (decidable via the `Fintype` `Decidable`
instance). Marking explicitly so the `verifier` below can stay
computable (cf. FRI's `foldVerifier`, which is plain `def`). -/
instance accepts.instDecidable
    (encode : (Fin k → F) → (ι → F))
    (stmt : Statement (F := F) k) (f : ∀ i, OracleStatement ι F i)
    (γ : F) (g : Fin k → F) (xs : Fin t → ι) :
    Decidable (accepts (k := k) (t := t) encode stmt f γ g xs) := by
  unfold accepts; infer_instance

/-- Honest verifier for Construction 6.2. Takes the bundled input
`(stmt, oStmt) = ((v, μ₁, μ₂), (f₁, f₂))` and the full transcript
`(γ, g, xs)`; accepts iff `accepts` holds for the supplied encoding.

Computable — `accepts` is decidable, so no `Classical.dec` is needed.
This mirrors FRI's `foldVerifier`, which is also a plain `def`. -/
def verifier (encode : (Fin k → F) → (ι → F)) :
    Verifier []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι F i))
      OutputStatement
      (pSpec (ι := ι) (F := F) k t) where
  verify := fun ⟨stmt, oStmt⟩ tr ↦ do
    let γ : F := tr ⟨0, by decide⟩
    let g : Fin k → F := tr ⟨1, by decide⟩
    let xs : Fin t → ι := tr ⟨2, by decide⟩
    if accepts (k := k) (t := t) encode stmt oStmt γ g xs
    then pure () else failure

/-- Honest reduction for Construction 6.2: the package
`{prover, verifier}` over the bundled-input `Reduction` type. -/
def reduction (encode : (Fin k → F) → (ι → F)) :
    Reduction []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι F i)) (Witness (F := F) k)
      OutputStatement OutputWitness
      (pSpec (ι := ι) (F := F) k t) where
  prover := prover (ι := ι) (F := F) (k := k) (t := t)
  verifier := verifier (k := k) (t := t) encode

/-! ### Oracle-flavour prover, verifier, reduction

These are the `OracleProver` / `OracleVerifier` / `OracleReduction`
flavours of the same protocol, exposing `(f₁, f₂)` as oracle inputs
rather than bundling them into `StmtIn`. They match FRI/Sumcheck's
exact idiom and are necessary to make the *query complexity* of the
verifier explicit (`2t + 1` queries per execution: one for `g`, two
per spot-check).

The honest-completeness, knowledge-soundness, and round-by-round
knowledge-soundness lemmas below are all stated against these
oracle-flavour objects: completeness via
`OracleReduction.perfectCompleteness`, L6.6 via
`OracleVerifier.knowledgeSoundness`, and L6.8 via
`OracleVerifier.rbrKnowledgeSoundness`. The latter two are
definitionally `toVerifier.knowledgeSoundness` /
`toVerifier.rbrKnowledgeSoundness`, so the oracle-flavour statements
carry no extra proof burden over the bundled-input forms.

**Framework vacuity (KS) — RESOLVED 2026-06-11.** The historical trap —
`Verifier.knowledgeSoundness` admitted an always-failing `OptionT`
extractor that drove the bad-event probability to `0` — was fixed by
PR #569 (`fix/knowledge-soundness-failing-extractor`), now merged and
synced into this branch: extraction failure (`extractedWitIn? = none`)
is scored against the prover. The KS sorries below
(`protocol62_knowledgeSound`, and `simplifiedIOR_knowledgeSound` in
`Spec/SimplifiedIOR.lean`) may be closed on their mathematical merits.
`Verifier.rbrKnowledgeSoundness` was never affected, so
`protocol62_rbrKnowledgeSound` is provable as-is (and is the natural
first target; KS then follows via the rbrKS → KS implication).
-/

/-- Same as `prover` but exposed at the `OracleProver` signature. The
underlying `Prover` is identical (after the `OracleProver` type-alias
unfolds to a `Prover` on bundled in/out types). The output is the
trivial `(((), nofun), ())` since the IOR has no output oracle
statements (`OutputOracleStatement : Fin 0 → Type`). -/
def oracleProver :
    OracleProver []ₒ
      (Statement (F := F) k) (OracleStatement ι F) (Witness (F := F) k)
      OutputStatement OutputOracleStatement OutputWitness
      (pSpec (ι := ι) (F := F) k t) where
  PrvState
  | ⟨0, _⟩ =>
      (Statement (F := F) k × (∀ i, OracleStatement ι F i)) × Witness (F := F) k
  | _ =>
      F × (Statement (F := F) k × (∀ i, OracleStatement ι F i)) × Witness (F := F) k

  input := id

  receiveChallenge
  | ⟨0, _⟩ => fun st ↦ pure <| fun (γ : F) ↦ (γ, st)
  | ⟨1, h⟩ => nomatch h
  | ⟨2, _⟩ => fun ⟨γ, st⟩ ↦ pure <| fun (_ : Fin t → ι) ↦ (γ, st)

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨γ, ⟨stmt, oStmt⟩, M⟩ ↦
      pure ((fun j ↦ M 0 j + γ * M 1 j), (γ, ⟨stmt, oStmt⟩, M))
  | ⟨2, h⟩ => nomatch h

  output := fun _ ↦ pure (((), nofun), ())

/-- Query helper: fetch the prover's combined-message claim `g`
(`pSpec` round 1 — the `P → V` direction). Mirrors FRI's `getConst`. -/
def queryG : OracleComp [(pSpec (ι := ι) (F := F) k t).Message]ₒ (Fin k → F) :=
  liftM <| OracleSpec.query
    (show [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain from
      ⟨⟨1, by rfl⟩, (by simpa using ())⟩)

/-- Query helper: read codeword `f i` at position `x : ι`. Mirrors
FRI's `queryCodeword`. -/
def queryF (i : Fin 2) (x : ι) : OracleComp [OracleStatement ι F]ₒ F :=
  liftM <| OracleSpec.query
    (show [OracleStatement ι F]ₒ.Domain from ⟨i, (by simpa using x)⟩)

/-- Oracle verifier for Construction 6.2.

Queries the prover's message `g` once and the two oracle codewords
`f₁, f₂` at each of the `t` spot-check positions (query complexity:
`2t + 1`), then `guard (accepts …)` to decide.

`embed` and `hEq` are trivial — `OutputOracleStatement : Fin 0 → Type`
is empty, so the output-oracle family is vacuously a subset of input
oracles + prover messages. -/
def oracleVerifier (encode : (Fin k → F) → (ι → F)) :
    OracleVerifier []ₒ
      (Statement (F := F) k) (OracleStatement ι F)
      OutputStatement OutputOracleStatement
      (pSpec (ι := ι) (F := F) k t) where
  verify := fun stmt challenges ↦ do
    let γ : F := challenges ⟨⟨0, by decide⟩, by rfl⟩
    let xs : Fin t → ι := challenges ⟨⟨2, by decide⟩, by rfl⟩
    let g : Fin k → F ← liftM <| queryG (ι := ι) (F := F) (k := k) (t := t)
    guard (∑ j, g j * stmt.1 j = stmt.2.1 + γ * stmt.2.2)
    for j in (List.finRange t) do
      let f₀ : F ← liftM <| queryF (ι := ι) (F := F) 0 (xs j)
      let f₁ : F ← liftM <| queryF (ι := ι) (F := F) 1 (xs j)
      guard (encode g (xs j) = f₀ + γ * f₁)
    pure ()
  embed := ⟨fun i ↦ i.elim0, fun a _ _ ↦ a.elim0⟩
  hEq := fun i ↦ i.elim0

/-- Honest oracle reduction for Construction 6.2: the
`OracleProver` / `OracleVerifier` pair packaged as `OracleReduction`. -/
def oracleReduction (encode : (Fin k → F) → (ι → F)) :
    OracleReduction []ₒ
      (Statement (F := F) k) (OracleStatement ι F) (Witness (F := F) k)
      OutputStatement OutputOracleStatement OutputWitness
      (pSpec (ι := ι) (F := F) k t) where
  prover := oracleProver (ι := ι) (F := F) (k := k) (t := t)
  verifier := oracleVerifier (k := k) (t := t) encode

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- Honest completeness for ABF26 Construction 6.2, point form: if
`((v, μ₁, μ₂), (f₁, f₂))` lies in `inputRelation` with the underlying
messages `M = (M₀, M₁)` (and `fᵢ` is the `encode`-image of `Mᵢ`), then
for any verifier challenges `(γ, xs)` the §6.1 decision `accepts` holds
against the honest prover's message `g = M₀ + γ · M₁`.

This is the point-form companion to the
`OracleReduction.perfectCompleteness` theorem that wraps the prover and
verifier objects below. -/
theorem accepts_of_inputRelation {k t : ℕ}
    {encode : (Fin k → F) →ₗ[F] (ι → F)}
    (stmt : Statement (F := F) k)
    (M : Witness (F := F) k)
    (hM : ∀ i, ∑ j, M i j * stmt.1 j =
        (if i = (0 : Fin 2) then stmt.2.1 else stmt.2.2))
    (f : ∀ i, OracleStatement ι F i)
    (hf : ∀ i, f i = encode (M i))
    (γ : F) (xs : Fin t → ι) :
    accepts (k := k) (t := t) (encode := (encode : (Fin k → F) → (ι → F)))
      stmt f γ (fun j ↦ M 0 j + γ * M 1 j) xs := by
  refine ⟨?_, ?_⟩
  · -- Linear-constraint: ∑ j, (M 0 j + γ * M 1 j) * v j = μ₁ + γ * μ₂.
    have h0 : ∑ j, M 0 j * stmt.1 j = stmt.2.1 := by
      have := hM 0; simpa using this
    have h1 : ∑ j, M 1 j * stmt.1 j = stmt.2.2 := by
      have := hM 1
      have hne : (1 : Fin 2) ≠ 0 := by decide
      simpa [if_neg hne] using this
    calc ∑ j, (M 0 j + γ * M 1 j) * stmt.1 j
        = ∑ j, (M 0 j * stmt.1 j + γ * (M 1 j * stmt.1 j)) := by
          apply Finset.sum_congr rfl; intros j _; ring
      _ = (∑ j, M 0 j * stmt.1 j) + ∑ j, γ * (M 1 j * stmt.1 j) :=
          Finset.sum_add_distrib
      _ = (∑ j, M 0 j * stmt.1 j) + γ * ∑ j, M 1 j * stmt.1 j := by
          rw [← Finset.mul_sum]
      _ = stmt.2.1 + γ * stmt.2.2 := by rw [h0, h1]
  · -- Spot-check: encode(g) x = f 0 x + γ * f 1 x.
    intro j
    have hg_eq : (fun i ↦ M 0 i + γ * M 1 i) = M 0 + γ • M 1 := by
      funext i; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hg_eq, map_add, map_smul, hf 0, hf 1]
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

omit [Fintype ι] [DecidableEq ι] [Fintype F] in
/-- The honest oracle verifier's body, simulated through `simOracle2` against the prover's
messages `msgs` and the input codewords `oStmt`, resolves to `pure (some ())` whenever the two
accept conditions hold for the supplied challenge `γ`, spot-check positions `xs`, and prover
message `g = msgs ⟨1, rfl⟩`:

  * `hAcc1`: the linear-constraint check `∑ j, g j · v j = μ₁ + γ · μ₂`, and
  * `hAcc2`: the per-spot-check `encode g (xs j) = f₀(xs j) + γ · f₁(xs j)`.

This is the monadic core of `oracleReduction_perfectCompleteness`: the residual support obligation
after the `Pr[…] = 1` goal is reduced via `OptionT.probEvent_eq_one_of_simulateQ_support_bind`
forces every honest-run output to be `some` of an accepting output, which this lemma certifies by
resolving each query (the prover claim `g` and the `2t` codeword reads) against `simOracle2` and
discharging both guards. The query/loop routing uses the staged `simulateQ`/`OptionT` toolkit
(`OracleComp.monadLift_liftM_OptionT`, `simulateQ_optionT_bind`/`_lift`,
`simulateQ_optionT_forIn_yield_pure_some`); the `change`/`conv` steps bridge the definitional —
but not syntactic — equalities between the elaborated verifier's `MonadLift`/`ForIn` instance
trees and the toolkit lemmas' canonical spellings. -/
lemma verifierBody_simulateQ_eq_pure
    (encode : (Fin k → F) → (ι → F))
    (oStmt : (i : Fin 2) → OracleStatement ι F i)
    (msgs : (j : (pSpec (ι := ι) (F := F) k t).MessageIdx) →
      (pSpec (ι := ι) (F := F) k t).Message j)
    (stmt1 : Fin k → F) (mu1 mu2 : F) (γ : F) (xs : Fin t → ι)
    (hAcc1 : ∑ j, (msgs ⟨1, rfl⟩) j * stmt1 j = mu1 + γ * mu2)
    (hAcc2 : ∀ j : Fin t, encode (msgs ⟨1, rfl⟩) (xs j)
      = oStmt 0 (xs j) + γ * oStmt 1 (xs j)) :
    simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) oStmt msgs)
      (do
        let g : Fin k → F ← liftM (queryG (ι := ι) (F := F) (k := k) (t := t))
        guard (∑ j, g j * stmt1 j = mu1 + γ * mu2)
        (fun _ ↦ ()) <$>
          forIn (List.finRange t) PUnit.unit fun j _ ↦ do
            let f₀ : F ← liftM (queryF (ι := ι) (F := F) 0 (xs j))
            let f₁ : F ← liftM (queryF (ι := ι) (F := F) 1 (xs j))
            (fun _ ↦ ForInStep.yield PUnit.unit) <$>
              guard (encode g (xs j) = f₀ + γ * f₁)
        : OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) Unit)
      = pure (some ()) := by
  -- Bridge each OptionT-lifted query helper to `OptionT.lift` of its OracleComp lift.
  rw [show (liftM (queryG (ι := ι) (F := F) (k := k) (t := t)) :
        OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) (Fin k → F))
      = OptionT.lift (liftM (queryG (ι := ι) (F := F) (k := k) (t := t)) :
          OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) (Fin k → F)) from
        (OracleComp.monadLift_liftM_OptionT _).symm]
  simp only [show ∀ (i : Fin 2) (x : ι), (liftM (queryF (ι := ι) (F := F) i x) :
        OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) F)
      = OptionT.lift (liftM (queryF (ι := ι) (F := F) i x) :
          OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) F) from
        fun i x ↦ (OracleComp.monadLift_liftM_OptionT _).symm]
  -- Push `simulateQ` through the OptionT bind / lift / map structure.
  simp only [map_eq_bind_pure_comp, simulateQ_optionT_bind, simulateQ_optionT_lift,
    queryG, queryF, OracleInterface.simOracle2, QueryImpl.addLift_def]
  -- Resolve the `g`-query to its oracle answer `msgs ⟨1, rfl⟩` by defeq.
  conv_lhs =>
    enter [1, 1]
    change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
        QueryImpl.liftTarget (OracleComp []ₒ)
          ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
            (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
      (Sum.inr (Sum.inr (⟨⟨1, rfl⟩, id ()⟩ :
        [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain)))
    rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
        QueryImpl.liftTarget (OracleComp []ₒ)
          ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
            (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
      (Sum.inr (Sum.inr (⟨⟨1, rfl⟩, id ()⟩ :
        [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain)))
      = (pure (msgs ⟨1, rfl⟩) : OracleComp []ₒ (Fin k → F)) from rfl]
  rw [show (OptionT.lift (pure (msgs ⟨1, rfl⟩)) : OptionT (OracleComp []ₒ) (Fin k → F))
      = (pure (msgs ⟨1, rfl⟩) : OptionT (OracleComp []ₒ) (Fin k → F)) from rfl, pure_bind]
  -- Guard 1 passes (hAcc1): `guard True = pure ()`, then `simulateQ impl (pure …) = pure …`.
  rw [show (guard (∑ j, msgs ⟨1, rfl⟩ j * stmt1 j = mu1 + γ * mu2) :
        OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
      = pure PUnit.unit from by rw [hAcc1]; simp [guard]]
  conv_lhs => enter [1]; rw [show (pure PUnit.unit : OptionT (OracleComp ([]ₒ +
        ([OracleStatement ι F]ₒ + [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
      = OptionT.lift (pure PUnit.unit) from rfl]
  rw [simulateQ_optionT_lift, simulateQ_pure]
  rw [show (OptionT.lift (pure PUnit.unit) : OptionT (OracleComp []ₒ) PUnit)
      = pure PUnit.unit from rfl, pure_bind]
  -- Resolve the spot-check `forIn` to `pure (some ())` via the yield-pure induction lemma.
  -- `hForIn`'s type is checked against the goal-shaped equation by `isDefEq` (bridging the
  -- lift-instance gaps); a `conv … change` then re-spells the goal's loop to `hForIn`'s LHS.
  have hForIn :
      simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) oStmt msgs)
        ((forIn (List.finRange t) PUnit.unit fun (j : Fin t) (_ : PUnit) ↦
          (OptionT.lift (liftM (queryF (ι := ι) (F := F) 0 (xs j))) >>= fun f₀ ↦
            OptionT.lift (liftM (queryF (ι := ι) (F := F) 1 (xs j))) >>= fun f₁ ↦
              guard (encode (msgs ⟨1, rfl⟩) (xs j) = f₀ + γ * f₁) >>=
                pure ∘ fun _ ↦ ForInStep.yield PUnit.unit)
            : OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι F]ₒ +
                [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit))
      = (pure (some PUnit.unit) : OracleComp (emptySpec.{0, 0}) (Option PUnit)) := by
    apply simulateQ_optionT_forIn_yield_pure_some
    intro j
    simp only [simulateQ_optionT_bind, simulateQ_optionT_lift,
      queryF, OracleInterface.simOracle2, QueryImpl.addLift_def]
    -- Resolve the two `queryF` reads (`f₀ = oStmt 0 (xs j)`, `f₁ = oStmt 1 (xs j)`) by defeq.
    conv_lhs =>
      enter [1, 1]
      change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
          QueryImpl.liftTarget (OracleComp []ₒ)
            ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
              (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
        (Sum.inr (Sum.inl (⟨0, xs j⟩ : [OracleStatement ι F]ₒ.Domain)))
      rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
          QueryImpl.liftTarget (OracleComp []ₒ)
            ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
              (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
        (Sum.inr (Sum.inl (⟨0, xs j⟩ : [OracleStatement ι F]ₒ.Domain)))
        = (pure (oStmt 0 (xs j)) : OracleComp []ₒ F) from rfl]
    rw [show (OptionT.lift (pure (oStmt 0 (xs j))) : OptionT (OracleComp []ₒ) F)
        = (pure (oStmt 0 (xs j)) : OptionT (OracleComp []ₒ) F) from rfl, pure_bind]
    conv_lhs =>
      enter [1, 1]
      change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
          QueryImpl.liftTarget (OracleComp []ₒ)
            ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
              (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
        (Sum.inr (Sum.inl (⟨1, xs j⟩ : [OracleStatement ι F]ₒ.Domain)))
      rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
          QueryImpl.liftTarget (OracleComp []ₒ)
            ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
              (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
        (Sum.inr (Sum.inl (⟨1, xs j⟩ : [OracleStatement ι F]ₒ.Domain)))
        = (pure (oStmt 1 (xs j)) : OracleComp []ₒ F) from rfl]
    rw [show (OptionT.lift (pure (oStmt 1 (xs j))) : OptionT (OracleComp []ₒ) F)
        = (pure (oStmt 1 (xs j)) : OptionT (OracleComp []ₒ) F) from rfl, pure_bind]
    -- Guard passes by hAcc2; then `simulateQ impl (pure …) = pure …`.
    rw [show (guard (encode (msgs ⟨1, rfl⟩) (xs j) = oStmt 0 (xs j) + γ * oStmt 1 (xs j)) :
          OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
        = pure PUnit.unit from by rw [hAcc2 j]; simp [guard]]
    conv_lhs => enter [1]; rw [show (pure PUnit.unit : OptionT (OracleComp ([]ₒ +
          ([OracleStatement ι F]ₒ + [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
        = OptionT.lift (pure PUnit.unit) from rfl]
    rw [simulateQ_optionT_lift, simulateQ_pure,
      show (OptionT.lift (pure PUnit.unit) : OptionT (OracleComp []ₒ) PUnit)
        = pure PUnit.unit from rfl, pure_bind]
    -- Trailing `(pure ∘ yield) unit = pure (yield unit)`, simulated to `pure (some (yield unit))`.
    change simulateQ _ ((pure (ForInStep.yield PUnit.unit) : OptionT (OracleComp ([]ₒ +
        ([OracleStatement ι F]ₒ + [(pSpec (ι := ι) (F := F) k t).Message]ₒ)))
          (ForInStep PUnit)) : OracleComp _ (Option (ForInStep PUnit))) = _
    conv_lhs => rw [show (pure (ForInStep.yield PUnit.unit) :
          OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) (ForInStep PUnit))
        = OptionT.lift (pure (ForInStep.yield PUnit.unit)) from rfl]
    rw [simulateQ_optionT_lift, simulateQ_pure]
    rfl
  -- Collapse the loop. The goal's bound `simulateQ … (forIn …)` is defeq to `hForIn`'s LHS but
  -- not `rw`-matchable (the `ForIn`/`MonadLift` instance trees differ syntactically). A
  -- `conv … change` re-spells the focused loop as `hForIn`'s exact LHS (the universes are pinned
  -- to `0` by the `emptySpec.{0,0}` ascription in the statement), after which `rw [hForIn]` fires.
  conv_lhs =>
    enter [1]
    change simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) oStmt msgs)
        ((forIn (List.finRange t) PUnit.unit fun (j : Fin t) (_ : PUnit) ↦
          (OptionT.lift (liftM (queryF (ι := ι) (F := F) 0 (xs j))) >>= fun f₀ ↦
            OptionT.lift (liftM (queryF (ι := ι) (F := F) 1 (xs j))) >>= fun f₁ ↦
              guard (encode (msgs ⟨1, rfl⟩) (xs j) = f₀ + γ * f₁) >>=
                pure ∘ fun _ ↦ ForInStep.yield PUnit.unit)
            : OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι F]ₒ +
                [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit))
  rw [hForIn]
  -- After collapsing the loop the goal is `(pure (some ()) : OracleComp []ₒ _) >>= …`; the bind
  -- runs the constant `(pure ∘ id)` continuation, leaving
  -- `simulateQ impl (pure ()) = pure (some ())`.
  change ((pure (some PUnit.unit) : OracleComp []ₒ (Option PUnit)) >>= fun _ ↦
      simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs)
        ((pure PUnit.unit : OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit) :
          OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) (Option PUnit))) = _
  rw [pure_bind]
  exact simulateQ_pure _ (some PUnit.unit)

omit [Fintype ι] [DecidableEq ι] [Fintype F] in
/-- Two-sided (`ite`) companion of `verifierBody_simulateQ_eq_pure`: the simulated verifier
body is the **deterministic** computation `pure (some ())` when both §6.1 accept conditions
hold for the supplied challenge `γ`, prover message `msgs ⟨1, rfl⟩`, and spot-check positions
`xs`, and `pure none` otherwise (a failed `guard` propagates through the remaining `OptionT`
binds, short-circuiting the spot-check loop).

The accepting direction delegates to `verifierBody_simulateQ_eq_pure`; the failing directions
re-run the same defeq bridges (see that lemma's docstring for the toolkit) and collapse the
failed `guard` via `simulateQ_optionT_failure` / `OptionT.failure_bind`, using
`simulateQ_optionT_forIn_yield_pure_none` for a failure inside the spot-check `forIn`. This is
the monadic core of the soundness direction (`accepts_of_mem_support_verifier_run` below):
a successful simulated run forces both accept conditions. -/
lemma verifierBody_simulateQ_eq_pure_ite
    (encode : (Fin k → F) → (ι → F))
    (oStmt : (i : Fin 2) → OracleStatement ι F i)
    (msgs : (j : (pSpec (ι := ι) (F := F) k t).MessageIdx) →
      (pSpec (ι := ι) (F := F) k t).Message j)
    (stmt1 : Fin k → F) (mu1 mu2 : F) (γ : F) (xs : Fin t → ι) :
    simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) oStmt msgs)
      (do
        let g : Fin k → F ← liftM (queryG (ι := ι) (F := F) (k := k) (t := t))
        guard (∑ j, g j * stmt1 j = mu1 + γ * mu2)
        (fun _ ↦ ()) <$>
          forIn (List.finRange t) PUnit.unit fun j _ ↦ do
            let f₀ : F ← liftM (queryF (ι := ι) (F := F) 0 (xs j))
            let f₁ : F ← liftM (queryF (ι := ι) (F := F) 1 (xs j))
            (fun _ ↦ ForInStep.yield PUnit.unit) <$>
              guard (encode g (xs j) = f₀ + γ * f₁)
        : OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) Unit)
      = pure (if (∑ j, (msgs ⟨1, rfl⟩) j * stmt1 j = mu1 + γ * mu2) ∧
            (∀ j : Fin t, encode (msgs ⟨1, rfl⟩) (xs j)
              = oStmt 0 (xs j) + γ * oStmt 1 (xs j))
          then some () else none) := by
  by_cases h1 : ∑ j, (msgs ⟨1, rfl⟩) j * stmt1 j = mu1 + γ * mu2
  case pos =>
    by_cases h2 : ∀ j : Fin t, encode (msgs ⟨1, rfl⟩) (xs j)
        = oStmt 0 (xs j) + γ * oStmt 1 (xs j)
    case pos =>
      rw [if_pos ⟨h1, h2⟩]
      exact verifierBody_simulateQ_eq_pure (k := k) (t := t)
        encode oStmt msgs stmt1 mu1 mu2 γ xs h1 h2
    case neg =>
      rw [if_neg (fun hc ↦ h2 hc.2)]
      -- Bridge each OptionT-lifted query helper to `OptionT.lift` of its OracleComp lift.
      rw [show (liftM (queryG (ι := ι) (F := F) (k := k) (t := t)) :
            OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
              [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) (Fin k → F))
          = OptionT.lift (liftM (queryG (ι := ι) (F := F) (k := k) (t := t)) :
              OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
                [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) (Fin k → F)) from
            (OracleComp.monadLift_liftM_OptionT _).symm]
      simp only [show ∀ (i : Fin 2) (x : ι), (liftM (queryF (ι := ι) (F := F) i x) :
            OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
              [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) F)
          = OptionT.lift (liftM (queryF (ι := ι) (F := F) i x) :
              OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
                [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) F) from
            fun i x ↦ (OracleComp.monadLift_liftM_OptionT _).symm]
      -- Push `simulateQ` through the OptionT bind / lift / map structure.
      simp only [map_eq_bind_pure_comp, simulateQ_optionT_bind, simulateQ_optionT_lift,
        queryG, queryF, OracleInterface.simOracle2, QueryImpl.addLift_def]
      -- Resolve the `g`-query to its oracle answer `msgs ⟨1, rfl⟩` by defeq.
      conv_lhs =>
        enter [1, 1]
        change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
            QueryImpl.liftTarget (OracleComp []ₒ)
              ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
                (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
          (Sum.inr (Sum.inr (⟨⟨1, rfl⟩, id ()⟩ :
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain)))
        rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
            QueryImpl.liftTarget (OracleComp []ₒ)
              ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
                (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
          (Sum.inr (Sum.inr (⟨⟨1, rfl⟩, id ()⟩ :
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain)))
          = (pure (msgs ⟨1, rfl⟩) : OracleComp []ₒ (Fin k → F)) from rfl]
      rw [show (OptionT.lift (pure (msgs ⟨1, rfl⟩)) : OptionT (OracleComp []ₒ) (Fin k → F))
          = (pure (msgs ⟨1, rfl⟩) : OptionT (OracleComp []ₒ) (Fin k → F)) from rfl, pure_bind]
      -- Guard 1 passes (h1): `guard True = pure ()`, then collapse the simulated pure.
      rw [show (guard (∑ j, msgs ⟨1, rfl⟩ j * stmt1 j = mu1 + γ * mu2) :
            OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
              [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
          = pure PUnit.unit from by rw [h1]; simp [guard]]
      conv_lhs => enter [1]; rw [show (pure PUnit.unit : OptionT (OracleComp ([]ₒ +
            ([OracleStatement ι F]ₒ + [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
          = OptionT.lift (pure PUnit.unit) from rfl]
      rw [simulateQ_optionT_lift, simulateQ_pure]
      rw [show (OptionT.lift (pure PUnit.unit) : OptionT (OracleComp []ₒ) PUnit)
          = pure PUnit.unit from rfl, pure_bind]
      -- Collapse the spot-check `forIn` to `pure none` (some spot check fails, by `h2`).
      have hForIn :
          simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) oStmt msgs)
            ((forIn (List.finRange t) PUnit.unit fun (j : Fin t) (_ : PUnit) ↦
              (OptionT.lift (liftM (queryF (ι := ι) (F := F) 0 (xs j))) >>= fun f₀ ↦
                OptionT.lift (liftM (queryF (ι := ι) (F := F) 1 (xs j))) >>= fun f₁ ↦
                  guard (encode (msgs ⟨1, rfl⟩) (xs j) = f₀ + γ * f₁) >>=
                    pure ∘ fun _ ↦ ForInStep.yield PUnit.unit)
                : OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι F]ₒ +
                    [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit))
          = (pure none : OracleComp (emptySpec.{0, 0}) (Option PUnit)) := by
        refine simulateQ_optionT_forIn_yield_pure_none _ _ _ _
          (fun j ↦ encode (msgs ⟨1, rfl⟩) (xs j) = oStmt 0 (xs j) + γ * oStmt 1 (xs j))
          (fun j ↦ ?_) (fun hall ↦ h2 (fun j ↦ hall j (List.mem_finRange j)))
        simp only [simulateQ_optionT_bind, simulateQ_optionT_lift,
          queryF, OracleInterface.simOracle2, QueryImpl.addLift_def]
        -- Resolve the two `queryF` reads (`f₀`, `f₁`) by defeq, as in the `some` direction.
        conv_lhs =>
          enter [1, 1]
          change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
              QueryImpl.liftTarget (OracleComp []ₒ)
                ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
                  (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
            (Sum.inr (Sum.inl (⟨0, xs j⟩ : [OracleStatement ι F]ₒ.Domain)))
          rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
              QueryImpl.liftTarget (OracleComp []ₒ)
                ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
                  (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
            (Sum.inr (Sum.inl (⟨0, xs j⟩ : [OracleStatement ι F]ₒ.Domain)))
            = (pure (oStmt 0 (xs j)) : OracleComp []ₒ F) from rfl]
        rw [show (OptionT.lift (pure (oStmt 0 (xs j))) : OptionT (OracleComp []ₒ) F)
            = (pure (oStmt 0 (xs j)) : OptionT (OracleComp []ₒ) F) from rfl, pure_bind]
        conv_lhs =>
          enter [1, 1]
          change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
              QueryImpl.liftTarget (OracleComp []ₒ)
                ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
                  (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
            (Sum.inr (Sum.inl (⟨1, xs j⟩ : [OracleStatement ι F]ₒ.Domain)))
          rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
              QueryImpl.liftTarget (OracleComp []ₒ)
                ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
                  (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
            (Sum.inr (Sum.inl (⟨1, xs j⟩ : [OracleStatement ι F]ₒ.Domain)))
            = (pure (oStmt 1 (xs j)) : OracleComp []ₒ F) from rfl]
        rw [show (OptionT.lift (pure (oStmt 1 (xs j))) : OptionT (OracleComp []ₒ) F)
            = (pure (oStmt 1 (xs j)) : OptionT (OracleComp []ₒ) F) from rfl, pure_bind]
        -- Per-spot-check guard: passes or fails according to `cond j`.
        by_cases hj : encode (msgs ⟨1, rfl⟩) (xs j) = oStmt 0 (xs j) + γ * oStmt 1 (xs j)
        · rw [if_pos hj]
          rw [show (guard (encode (msgs ⟨1, rfl⟩) (xs j)
                = oStmt 0 (xs j) + γ * oStmt 1 (xs j)) :
                OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
                  [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
              = pure PUnit.unit from by rw [hj]; simp [guard]]
          conv_lhs => enter [1]; rw [show (pure PUnit.unit : OptionT (OracleComp ([]ₒ +
                ([OracleStatement ι F]ₒ + [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
              = OptionT.lift (pure PUnit.unit) from rfl]
          rw [simulateQ_optionT_lift, simulateQ_pure,
            show (OptionT.lift (pure PUnit.unit) : OptionT (OracleComp []ₒ) PUnit)
              = pure PUnit.unit from rfl, pure_bind]
          change simulateQ _ ((pure (ForInStep.yield PUnit.unit) : OptionT (OracleComp ([]ₒ +
              ([OracleStatement ι F]ₒ + [(pSpec (ι := ι) (F := F) k t).Message]ₒ)))
                (ForInStep PUnit)) : OracleComp _ (Option (ForInStep PUnit))) = _
          conv_lhs => rw [show (pure (ForInStep.yield PUnit.unit) :
                OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
                  [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) (ForInStep PUnit))
              = OptionT.lift (pure (ForInStep.yield PUnit.unit)) from rfl]
          rw [simulateQ_optionT_lift, simulateQ_pure]
          rfl
        · rw [if_neg hj]
          rw [show (guard (encode (msgs ⟨1, rfl⟩) (xs j)
                = oStmt 0 (xs j) + γ * oStmt 1 (xs j)) :
                OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
                  [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
              = failure from by simp only [guard, if_neg hj]]
          rw [simulateQ_optionT_failure, OptionT.failure_bind]
          rfl
      -- Re-spell the goal's loop to `hForIn`'s LHS and collapse; failure then propagates.
      conv_lhs =>
        enter [1]
        change simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) oStmt msgs)
            ((forIn (List.finRange t) PUnit.unit fun (j : Fin t) (_ : PUnit) ↦
              (OptionT.lift (liftM (queryF (ι := ι) (F := F) 0 (xs j))) >>= fun f₀ ↦
                OptionT.lift (liftM (queryF (ι := ι) (F := F) 1 (xs j))) >>= fun f₁ ↦
                  guard (encode (msgs ⟨1, rfl⟩) (xs j) = f₀ + γ * f₁) >>=
                    pure ∘ fun _ ↦ ForInStep.yield PUnit.unit)
                : OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι F]ₒ +
                    [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit))
      rw [hForIn]
      rw [show (pure none : OracleComp (emptySpec.{0, 0}) (Option PUnit))
          = ((failure : OptionT (OracleComp (emptySpec.{0, 0})) PUnit) :
              OracleComp (emptySpec.{0, 0}) (Option PUnit)) from rfl,
        OptionT.failure_bind]
  case neg =>
    rw [if_neg (fun hc ↦ h1 hc.1)]
    -- Bridge the `g`-query, resolve it by defeq, then fail on the linear-constraint guard.
    rw [show (liftM (queryG (ι := ι) (F := F) (k := k) (t := t)) :
          OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) (Fin k → F))
        = OptionT.lift (liftM (queryG (ι := ι) (F := F) (k := k) (t := t)) :
            OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
              [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) (Fin k → F)) from
          (OracleComp.monadLift_liftM_OptionT _).symm]
    simp only [map_eq_bind_pure_comp, simulateQ_optionT_bind, simulateQ_optionT_lift,
      queryG, OracleInterface.simOracle2, QueryImpl.addLift_def]
    conv_lhs =>
      enter [1, 1]
      change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
          QueryImpl.liftTarget (OracleComp []ₒ)
            ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
              (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
        (Sum.inr (Sum.inr (⟨⟨1, rfl⟩, id ()⟩ :
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain)))
      rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
          QueryImpl.liftTarget (OracleComp []ₒ)
            ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
              (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
        (Sum.inr (Sum.inr (⟨⟨1, rfl⟩, id ()⟩ :
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain)))
        = (pure (msgs ⟨1, rfl⟩) : OracleComp []ₒ (Fin k → F)) from rfl]
    rw [show (OptionT.lift (pure (msgs ⟨1, rfl⟩)) : OptionT (OracleComp []ₒ) (Fin k → F))
        = (pure (msgs ⟨1, rfl⟩) : OptionT (OracleComp []ₒ) (Fin k → F)) from rfl, pure_bind]
    rw [show (guard (∑ j, msgs ⟨1, rfl⟩ j * stmt1 j = mu1 + γ * mu2) :
          OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
        = failure from by simp only [guard, if_neg h1]]
    rw [simulateQ_optionT_failure, OptionT.failure_bind]
    rfl

omit [Fintype ι] [DecidableEq ι] [Fintype F] in
/-- **Soundness direction of the verifier-run support characterization** (converse companion
of the completeness-side `verifierBody_simulateQ_eq_pure`): if the simulated run of the C6.2
oracle verifier (routed through `toVerifier` / `simOracle2`, then through an arbitrary
empty-spec `impl`) on a **fixed** full transcript `tr` can succeed — `some _` lies in the run's
support — then the §6.1 decision predicate `accepts` holds for that transcript's challenge
`γ = tr 0`, prover message `g = tr 1`, and spot-check positions `xs = tr 2`.

Proof: the empty-spec simulation can only shrink support
(`support_simulateQ_run'_subset`), and after `toVerifier` routing the verifier body is the
deterministic `pure (if accepts-conditions then some () else none)`
(`verifierBody_simulateQ_eq_pure_ite`), so a `some` in the support forces the condition. -/
lemma accepts_of_mem_support_verifier_run
    {σ : Type} (impl : QueryImpl []ₒ (StateT σ ProbComp)) (s₀ : σ)
    (encode : (Fin k → F) → (ι → F))
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι F i))
    (tr : FullTranscript (pSpec (ι := ι) (F := F) k t))
    {y : OutputStatement × (∀ i, OutputOracleStatement i)}
    (hy : some y ∈ support ((simulateQ impl
        (((oracleVerifier (k := k) (t := t) encode).toVerifier).run stmtIn tr)).run' s₀)) :
    accepts (k := k) (t := t) encode stmtIn.1 stmtIn.2
      (tr ⟨0, by decide⟩) (tr ⟨1, by decide⟩) (tr ⟨2, by decide⟩) := by
  -- Drop the `impl` simulation layer (an empty-spec impl can only shrink the support).
  have hy' := support_simulateQ_run'_subset impl _ s₀ hy
  -- Expose the `toVerifier`-routed verifier body and collapse it to its `ite` normal form.
  simp only [OracleVerifier.toVerifier, oracleVerifier, Verifier.run, bind_pure_comp] at hy'
  rw [verifierBody_simulateQ_eq_pure_ite (encode := encode) (stmt1 := stmtIn.1.1)
      (mu1 := stmtIn.1.2.1) (mu2 := stmtIn.1.2.2)] at hy'
  -- Peel the trailing output-assembly bind; a `none` head contradicts `some y` in the support.
  rcases OptionT.mem_support_run_bind _ _ hy' with ⟨hnone, hcontra⟩ | ⟨a, ha, _⟩
  · exact absurd hcontra (by simp)
  · have ha := OracleComp.eq_of_mem_support_pure _ ha
    split at ha
    · rename_i hcond
      exact hcond
    · exact absurd ha (by simp)

omit [Fintype ι] [DecidableEq ι] [Fintype F] in
/-- Round-by-round-framework wrapper for `accepts_of_mem_support_verifier_run`, consuming the
exact hypothesis shape that `KnowledgeStateFunction.toFun_full`
(`ArkLib/OracleReduction/Security/RoundByRound.lean`) provides for the C6.2 oracle verifier:
if the verifier's simulated run on a fixed transcript outputs, with positive probability, a
statement that is `relOut`-related to some `witOut` (for **any** `relOut`, in particular
`Set.univ`), then the §6.1 decision predicate `accepts` holds on that transcript. This is the
entry point for the L6.8 round-by-round knowledge-soundness state function: at the full
transcript it converts the framework's `Pr[…] > 0` acceptance hypothesis into the concrete
accept equations that the [ABF26] §6.2 argument consumes. -/
lemma accepts_of_probEvent_pos_verifier_run
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (encode : (Fin k → F) → (ι → F))
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι F i))
    (tr : FullTranscript (pSpec (ι := ι) (F := F) k t))
    (witOut : OutputWitness)
    (relOut : Set ((OutputStatement × ∀ i, OutputOracleStatement i) × OutputWitness))
    (h : Pr[ fun stmtOut ↦ (stmtOut, witOut) ∈ relOut
      | OptionT.mk do
          (simulateQ impl
              (((oracleVerifier (k := k) (t := t) encode).toVerifier).run stmtIn tr)).run'
            (← init)] > 0) :
    accepts (k := k) (t := t) encode stmtIn.1 stmtIn.2
      (tr ⟨0, by decide⟩) (tr ⟨1, by decide⟩) (tr ⟨2, by decide⟩) := by
  rw [gt_iff_lt, probEvent_pos_iff] at h
  obtain ⟨stmtOut, hmem, -⟩ := h
  obtain ⟨s₀, -, hmem⟩ := OptionT.mem_support_bind_mk init _ hmem
  rw [OptionT.mem_support_iff] at hmem
  exact accepts_of_mem_support_verifier_run (k := k) (t := t) impl s₀ encode stmtIn tr hmem

omit [Fintype ι] [DecidableEq ι] [Fintype F] in
/-- **Honest completeness for Construction 6.2** (protocol-level form).

The honest oracle reduction is perfectly complete from `inputRelationFor encode`
to the trivial output relation `Set.univ`. The load-bearing fact is
`accepts_of_inputRelation` above: under any verifier challenges, the
honest prover's message `g = M₀ + γ M₁` makes `accepts` hold, so the
verifier's `if accepts then pure () else failure` never fails.

**Status: fully proven (sorry-free, axiom-clean: `propext`, `Classical.choice`,
`Quot.sound` only; closed 2026-06-11).** The proof unfolds
`OracleReduction.perfectCompleteness` through `toReduction`, expands the
prover's three-round `runToRound` via `Fin.induction_three`, resolves the three
round directions, and reduces the `Pr[…] = 1` goal to a support-membership
obligation via `OptionT.probEvent_eq_one_of_simulateQ_support_bind`
(`ArkLib/ToVCVio/OracleComp/SimSemantics/SimulateQ.lean`). The support
obligation splits into:

  1. **The monadic core** — resolving the verifier body's `queryG`/`queryF`
     against `simOracle2` through the composed `MonadLiftT`/`OptionT` instance
     chains and collapsing the spot-check `forIn` — packaged as
     `verifierBody_simulateQ_eq_pure` (above), built on the staged toolkit
     (`simulateQ_optionT_bind`/`_lift`, `simulateQ_optionT_forIn_yield_pure_some`,
     `OracleComp.monadLift_liftM_OptionT`); the query routing itself is done by
     manual definitional bridges, not by the staged `simulateQ_add_add_liftM_*`
     simp family (whose `implA + implB` left-hand sides do not match
     `simOracle2`'s `addLift`/`liftTarget` spelling — that family remains an
     upstream-candidate for canonically-spelled goals). The recurrent obstacle —
     elaborated `MonadLift`/`ForIn` instance trees that are *definitionally* but
     not *syntactically* equal to the toolkit lemmas' canonical spellings — is
     bridged by `conv … change`/`show … from rfl` steps and a universe-pinned
     `emptySpec.{0,0}` ascription (the `[]ₒ` notation otherwise leaves a free
     universe metavariable that blocks `rw`).
  2. **Support plumbing** — peeling the `Reduction.run` OptionT-bind chain
     (challenge sampling, `Transcript.concat` layers, final `Option.getM`) via
     the `obtain`-friendly defeq peelers (`OptionT.mem_support_run_bind`,
     `OracleComp.mem_support_bind_peel`, …, same staged file), landing each
     support element on `verifierBody_simulateQ_eq_pure` with the accept
     hypotheses supplied by `accepts_of_inputRelation` from `hRel`.

**Statement faithfulness (fixed 2026-06-04).** The input relation is the
**fixed-encoding** `inputRelationFor encode` (the verifier's own `encode`, with
the witness `M` tied to the codewords `fᵢ = encode (M i)`). An earlier
existential-encoding form (`ToyProblem.relation`, `∃ encode'`) made completeness
*unprovable / false* — the honest prover's `encode g` need not match
`fᵢ = encode' (Mᵢ)` when `encode' ≠ encode` (the same defect found for the L6.12
attack). With `inputRelationFor encode` the discharge to `accepts_of_inputRelation`
(`hf : fᵢ = encode (M i)`, `hM : ⟨M i, v⟩ = μᵢ`) goes through. -/
theorem oracleReduction_perfectCompleteness
    [SampleableType F] [SampleableType ι]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (encode : (Fin k → F) →ₗ[F] (ι → F)) :
    (oracleReduction (ι := ι) (F := F) (k := k) (t := t)
        (encode : (Fin k → F) → (ι → F))).perfectCompleteness
      init impl
      (inputRelationFor (encode := (encode : (Fin k → F) → (ι → F))))
      (Set.univ : Set (((OutputStatement × ∀ i, OutputOracleStatement i)) ×
        OutputWitness)) := by
  unfold OracleReduction.perfectCompleteness
  rw [Reduction.perfectCompleteness_eq_prob_one]
  intro stmtIn witIn hRel
  -- Unfold the reduction run, expand the 3-round prover (`Fin.induction_three`),
  -- and inline the oracle verifier's `toVerifier` wrapper.
  simp only [OracleReduction.toReduction, Reduction.run, oracleReduction,
    oracleProver, OracleVerifier.toVerifier, oracleVerifier,
    Prover.run, Prover.runToRound, Fin.induction_three, Prover.processRound,
    Verifier.run, pSpec, bind_pure_comp]
  -- Resolve round 0 direction (`V_to_P`, the combination randomness `γ`).
  split <;> rename_i hDir0
  swap
  · exact absurd hDir0 (by decide)
  try simp only [pure_bind, map_pure, Functor.map_map, Function.comp, bind_pure_comp]
  -- Resolve round 1 direction (`P_to_V`, the prover's claim `g`).
  split <;> rename_i hDir1
  · exact absurd hDir1 (by decide)
  try simp only [pure_bind, map_pure, Functor.map_map, Function.comp, bind_pure_comp]
  -- Resolve round 2 direction (`V_to_P`, the spot-check positions `xs`).
  split <;> rename_i hDir2
  swap
  · exact absurd hDir2 (by decide)
  -- Reduce `Pr[…] = 1` to a support-membership obligation on the (pre-simulation)
  -- `OracleComp` body via the toolkit lemma, which peels the `(← init)` bind, the
  -- `simulateQ`/`StateT.run'` layers, and the `OptionT.mk` failure bookkeeping.
  apply OptionT.probEvent_eq_one_of_simulateQ_support_bind
  intro x hx
  -- The output relation is trivial: `OutputStatement = OutputWitness = Unit`, so both
  -- conjuncts (`(a.2, a.1.2.2) ∈ Set.univ` and `a.1.2.1 = a.2`) hold for *every* `a`
  -- (`Subsingleton Unit`). It therefore suffices to show `x = some a` for some `a`.
  refine (fun ⟨a, ha⟩ ↦ ⟨a, ha, Set.mem_univ _, Subsingleton.elim _ _⟩) (?_ : ∃ a, x = some a)
  -- The monadic-simulation core (the historical C6.2 blocker — routing `queryG`/`queryF` through
  -- the composed `simOracle2` `MonadLift` chain and collapsing the `OptionT` spot-check `forIn`) is
  -- now **closed**, packaged as `verifierBody_simulateQ_eq_pure` (above) on top of the staged
  -- toolkit (`simulateQ_optionT_bind`/`_lift`, `simulateQ_optionT_forIn_yield_pure_some`,
  -- `OracleComp.monadLift_liftM_OptionT`). The defeq-vs-syntactic lift-instance gaps are bridged
  -- there by `conv … change` + universe-pinned `emptySpec.{0,0}` ascriptions.
  --
  -- The verifier body resolves to `pure (some ())` by `verifierBody_simulateQ_eq_pure` (above) —
  -- this is the load-bearing C6.2 content, now **fully proven**: for *any* sampled challenge `γ`
  -- and spot-check positions `xs`, the honest prover's round-1 message `g = M₀ + γ·M₁` makes both
  -- guards pass (`accepts_of_inputRelation`, supplied via `hRel : … ∈ inputRelationFor encode`),
  -- so the simulated verifier body never fails and yields `some ()`. Concretely, in `hx`'s run the
  -- verifier subterm is `simulateQ (simOracle2 []ₒ stmtIn.2 proverResult.1.messages) (do let g ←
  -- queryG; guard …; for … ; …).run`, which is exactly `verifierBody_simulateQ_eq_pure` at
  -- `oStmt := stmtIn.2`, `msgs := proverResult.1.messages`, `g := proverResult.1.messages ⟨1,rfl⟩`.
  --
  -- The remaining work (ABF26-C6.2, now **closed**) is generic support plumbing: decompose
  -- `support (Reduction.run …)` through the `Prover.run` challenge-sampling binds (`getChallenge`
  -- for the two `V_to_P` rounds), the `Transcript.concat`/`liftM` coercion layers, and the final
  -- `OptionT.run`/`Option.getM`. The elaborated `liftM`/`OptionT`/`Fin.induction` bind tree is
  -- defeq but not syntactically `>>=`, so the syntactic `support_bind`/`mem_support_liftComp_iff`
  -- `rw`s do not engage; instead the peel is driven by the *definitional*-unification `obtain`
  -- helpers `OracleComp.mem_support_bind_peel`/`mem_support_map_peel`/`eq_of_mem_support_pure` and
  -- `OptionT.mem_support_run_bind`/`_lift_bind` (`ArkLib/ToVCVio/.../SimulateQ.lean`). Each support
  -- element fixes a sampled `(γ₀, xs₂)` and the deterministic honest message
  -- `proverResult.1.messages ⟨1,rfl⟩ = fun j => witIn 0 j + γ₀ · witIn 1 j`; under that message
  -- `verifierBody_simulateQ_eq_pure` (via `accepts_of_inputRelation`) collapses the verifier body
  -- to `pure (some ())`, forcing `stmtOut = some _` and hence `x = some _`.
  obtain ⟨proverResult, hPR, hx⟩ := OptionT.mem_support_run_lift_bind _ _ hx
  -- Characterize the honest prover's transcript from `hPR`.
  rw [show (monadLift : OracleComp ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ) _ →
        OracleComp ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ) _) = id from rfl,
      id_eq] at hPR
  -- Peel the prover-run binds by *definitional*-unification `obtain` (the elaborated
  -- `Fin.induction` bind tree is defeq but not syntactically `>>=`, so `rw`-based
  -- peelers do not engage).
  -- `prover.run = let r ← runToRound (last 3); ⟨r.1, ← output r.2⟩`.
  obtain ⟨r3, hr3, hPR⟩ := OracleComp.mem_support_bind_peel _ _ hPR
  obtain ⟨out, _, hPR⟩ := OracleComp.mem_support_bind_peel _ _ hPR
  -- `hPR : proverResult ∈ support (pure (r3.1, out))`.
  have hPReq : proverResult = (r3.1, out) := by
    have := (mem_support_pure_iff (m := OracleComp ([]ₒ +
      [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)) proverResult (r3.1, out)).mp hPR
    simpa using this
  -- runToRound = processRound 2 (processRound 1 (processRound 0 (pure base))).
  -- Peel the round-2 bind: `r3 ∈ support (let r2 ← (rounds 0-1); round2body r2)`.
  obtain ⟨r2, hr2, hr3⟩ := OracleComp.mem_support_bind_peel _ _ hr3
  -- Peel the round-1 bind from `hr2`: `r2 ∈ support (let r1 ← (round 0); round1body r1)`.
  obtain ⟨r1, hr1, hr2⟩ := OracleComp.mem_support_bind_peel _ _ hr2
  -- Peel the round-0 bind from `hr1`: `r1 ∈ support (let r0 ← pure base; round0body r0)`.
  obtain ⟨r0, hr0, hr1⟩ := OracleComp.mem_support_bind_peel _ _ hr1
  -- Resolve `r0` to the pure base value (kept symbolic to avoid spelling `default`).
  have hr0 := OracleComp.eq_of_mem_support_pure _ hr0
  subst hr0
  -- round 0: peel the challenge `γ₀`, then resolve `r1`.
  obtain ⟨γ₀, hγ₀, hr1⟩ := OracleComp.mem_support_bind_peel _ _ hr1
  -- round 2: peel the challenge `xs₂`, then resolve `r3`.
  obtain ⟨xs₂, hxs₂, hr3⟩ := OracleComp.mem_support_bind_peel _ _ hr3
  -- Resolve `r1`, `r2`, `r3` from their `map`-of-`liftM (pure …)` supports.
  obtain ⟨f1, hf1, hr1⟩ := OracleComp.mem_support_map_peel _ _ hr1
  obtain ⟨f2, hf2, hr2⟩ := OracleComp.mem_support_map_peel _ _ hr2
  obtain ⟨f3, hf3, hr3⟩ := OracleComp.mem_support_map_peel _ _ hr3
  have hf1 := OracleComp.eq_of_mem_support_pure _ hf1
  have hf2 := OracleComp.eq_of_mem_support_pure _ hf2
  have hf3 := OracleComp.eq_of_mem_support_pure _ hf3
  subst hf1 hf2 hf3 hr1 hr2 hr3 hPReq
  -- Reduce the transcript accessors (`Fin.snoc` at indices 0/1/2) inside the verifier subterm.
  simp only [id_eq, FullTranscript.challenges, Transcript.concat,
    Fin.snoc, Fin.val_zero,
    Fin.val_one, Fin.val_two, lt_self_iff_false, Fin.val_castLT,
    Fin.castSucc_castLT, show (0 : ℕ) < 2 from by norm_num, show (0 : ℕ) < 1 from by norm_num,
    show ¬ ((2 : ℕ) < 0) from by norm_num, dif_pos, cast_eq,
    dite_false] at hx
  -- Extract the witness facts from the input relation.
  obtain ⟨hf, hM⟩ := hRel
  -- Rewrite the verifier subterm in `hx` to `pure (some ())` via `verifierBody_simulateQ_eq_pure`.
  -- `msgs`, `γ`, `xs` are inferred by unification; `hAcc1`/`hAcc2` come from
  -- `accepts_of_inputRelation` after identifying round-1 message `msgs ⟨1, rfl⟩` with honest `g`.
  rw [verifierBody_simulateQ_eq_pure (encode := (encode : (Fin k → F) → (ι → F)))
      (stmt1 := stmtIn.1.1) (mu1 := stmtIn.1.2.1) (mu2 := stmtIn.1.2.2)
      (hAcc1 := ?hAcc1) (hAcc2 := ?hAcc2)] at hx
  · -- After the rewrite the verifier round-1 query produces `pure (some ())`, so the second bind's
    -- first computation never fails. Peel it: the `none` branch is contradicted by `pure (some _)`.
    rcases OptionT.mem_support_run_bind _ _ hx with ⟨hverNone, _⟩ | ⟨stmtOut, hSO, hx⟩
    · exact absurd (OracleComp.eq_of_mem_support_pure _ hverNone) (by simp)
    -- `hSO : some stmtOut ∈ support (liftM (g <$> pure (some ())))` is defeq `pure (g (some ()))`,
    -- forcing `stmtOut = ((), embed)`; then `stmtOut.getM` succeeds and `x = some _`.
    have hSO := OracleComp.eq_of_mem_support_pure _ hSO
    rw [Option.some.injEq] at hSO
    subst hSO
    have hx := OracleComp.eq_of_mem_support_pure _ hx
    exact ⟨_, hx⟩
  case hAcc1 =>
    have hacc := accepts_of_inputRelation (encode := encode) stmtIn.1 witIn
      (fun i ↦ by have := hM i; fin_cases i <;> simpa using this) stmtIn.2
      (fun i ↦ by have := hf i; simpa using this) (cast (by rfl) γ₀) xs₂
    simp only [FullTranscript.messages, Fin.snoc] at *
    exact hacc.1
  case hAcc2 =>
    have hacc := accepts_of_inputRelation (encode := encode) stmtIn.1 witIn
      (fun i ↦ by have := hM i; fin_cases i <;> simpa using this) stmtIn.2
      (fun i ↦ by have := hf i; simpa using this) (cast (by rfl) γ₀) xs₂
    intro j
    simp only [FullTranscript.messages, Fin.snoc] at *
    exact hacc.2 j

/-! ### Remark 6.7 of [ABF26] — MCA, not just CA

The L6.6 soundness argument depends on **mutual** correlated agreement
(MCA). With only correlated agreement (CA), one cannot prove every
codeword `u ∈ Λ(C, f₁ + γ·f₂, δ)` decomposes as `u = u₁ + γ·u₂` for some
`(u₁, u₂) ∈ Λ(C^{≡2}, (f₁, f₂), δ)`, so the extractor would fail. MCA
provides exactly this decomposition with probability `≥ 1 − ε_mca`. -/

/-! ### Lemma 6.8 assembly — extractor, knowledge state function, per-round bounds.
The post-spot-check state is the §6.1 acceptance predicate itself
(witness-ignoring) — see PAPER_REVS.md item 10 for the deviation rationale. -/

/-- `Pr_{x ← D}[P x] = 0` for a never-satisfied predicate `P`. -/
private lemma Pr_eq_zero_of_forall_not {α : Type} (D : PMF α) (P : α → Prop)
    (h : ∀ x, ¬ P x) : Pr_{let x ← D}[P x] = 0 := by
  classical rw [prob_tsum_form_singleton]; simp [h]

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- The post-`γ` knowledge state of the L6.8 argument ([ABF26] §6.2): `m`
satisfies the folded linear constraint at `γ`, and `f₁ + γ·f₂` agrees with
`encode m` on a `≥ (1-δ)`-fraction column set. Shaped to match the event of
`ToyProblem.gamma_transition_prob_le` exactly.

Public (not `private`) because the L6.6 assembly
(`Spec/KnowledgeSoundness.lean`) reuses it as its γ-round prefix event. -/
def gammaState (encode : (Fin k → F) → (ι → F)) (δ : ℝ≥0)
    (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → F) (γ : F) (m : Fin k → F) : Prop :=
  (∑ j, m j * v j = μ₁ + γ * μ₂) ∧
  ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
    ∀ j ∈ S, f₁ j + γ * f₂ j = encode m j

/-- L6.8 intermediate witness types: input witness at round 0, the γ-round
candidate message during rounds 1–2, nothing after the spot-check round. -/
private def rbrWitMid : Fin 4 → Type
  | ⟨0, _⟩ => Witness (F := F) k
  | ⟨1, _⟩ => Fin k → F
  | ⟨2, _⟩ => Fin k → F
  | ⟨3, _⟩ => PUnit

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
open Classical in
/-- Round-0 extraction for L6.8: if *any* witness completes `stmtIn` in the
relaxed output relation, return one by choice; otherwise a dummy.

Public (not `private`) because L6.10 reuses it verbatim: the C6.9 input relation is
the same `R̃²_{C,δ}` (`outputRelationFor`), so the L6.10 straightline extractor is this
same classical choice (`SimplifiedIOR.simplifiedIOR_knowledgeSound`). -/
noncomputable def extractZero (encode : (Fin k → F) → (ι → F)) (δ : ℝ≥0)
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι F i)) :
    Witness (F := F) k :=
  if h : ∃ M, (stmtIn, M) ∈ outputRelationFor k encode δ then h.choose
  else fun _ _ ↦ 0

omit [DecidableEq ι] [DecidableEq F] in
/-- If a relaxed-relation witness exists at all, `extractZero` returns one.
(Shared by the L6.8 γ-round bound and the L6.10 game bound.) -/
lemma extractZero_mem {encode : (Fin k → F) → (ι → F)} {δ : ℝ≥0}
    {stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι F i)}
    (hw : ∃ M, (stmtIn, M) ∈ outputRelationFor k encode δ) :
    (stmtIn, extractZero k encode δ stmtIn) ∈ outputRelationFor k encode δ := by
  unfold extractZero; rw [dif_pos hw]; exact hw.choose_spec

omit [DecidableEq ι] in
/-- The L6.8 round-by-round extractor ([ABF26] §6.2): round 0 extracts a
relaxed-relation witness by choice, round 1 passes the candidate message
through, round 2 reads the prover's claim `g` off the transcript. -/
private noncomputable def rbrExtractor (encode : (Fin k → F) → (ι → F)) (δ : ℝ≥0) :
    Extractor.RoundByRound []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι F i))
      (Witness (F := F) k) OutputWitness
      (pSpec (ι := ι) (F := F) k t) (rbrWitMid (F := F) k) where
  eqIn := rfl
  extractMid
  | ⟨0, _⟩ => fun stmtIn _ _ ↦ extractZero k encode δ stmtIn
  | ⟨1, _⟩ => fun _ _ w ↦ w
  | ⟨2, _⟩ => fun _ tr _ ↦ tr ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩
  extractOut := fun _ _ _ ↦ PUnit.unit

omit [DecidableEq ι] in
/-- The L6.8 knowledge state function ([ABF26] §6.2): relaxed-relation
membership at round 0, `gammaState` after rounds 1–2, and the §6.1 acceptance
predicate after the spot-check round (PAPER_REVS.md item 10). -/
private noncomputable def rbrKSF (encode : (Fin k → F) → (ι → F)) (δ : ℝ≥0)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ((oracleVerifier (k := k) (t := t) encode).toVerifier).KnowledgeStateFunction init impl
      (outputRelationFor k encode δ)
      (Set.univ : Set ((OutputStatement × ∀ i, OutputOracleStatement i) × OutputWitness))
      (rbrExtractor k t encode δ) where
  toFun
  | ⟨0, _⟩ => fun stmtIn _ w ↦ (stmtIn, w) ∈ outputRelationFor k encode δ
  | ⟨1, _⟩ => fun stmtIn tr w ↦
      gammaState k encode δ stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
        (stmtIn.2 0) (stmtIn.2 1) (tr ⟨0, Nat.zero_lt_succ _⟩) w
  | ⟨2, _⟩ => fun stmtIn tr w ↦
      gammaState k encode δ stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
        (stmtIn.2 0) (stmtIn.2 1) (tr ⟨0, Nat.zero_lt_succ _⟩) w
  | ⟨3, _⟩ => fun stmtIn tr _ ↦
      accepts (k := k) (t := t) encode stmtIn.1 stmtIn.2
        (tr ⟨0, Nat.zero_lt_succ _⟩) (tr ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)
        (tr ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩)
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m ↦ match m with
    | ⟨0, _⟩ => fun hDir ↦ absurd hDir (fun h ↦ Direction.noConfusion h)
    | ⟨1, _⟩ => fun _ _ _ _ _ h ↦ h
    | ⟨2, _⟩ => fun hDir ↦ absurd hDir (fun h ↦ Direction.noConfusion h)
  toFun_full := fun stmtIn tr witOut h ↦
    accepts_of_probEvent_pos_verifier_run (k := k) (t := t) init impl encode
      stmtIn tr witOut _ h

omit [DecidableEq ι] [DecidableEq F] in
/-- `epsMCA` is a supremum of probabilities, hence `≤ 1 < ⊤`. (Candidate for
relocation to `ProximityGap/Errors.lean`. Public because the L6.10 coercion
endgame in `Spec/SimplifiedIOR.lean` reuses it.) -/
lemma epsMCA_ne_top [Nonempty ι] (C : Set (ι → F)) (δ : ℝ≥0) :
    epsMCA (F := F) (A := F) C δ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun _ ↦ PMF.coe_le_one _ _)

omit [DecidableEq ι] in
/-- Per-transcript γ-round bound for the L6.8 game ([ABF26] §6.2, via
`ToyProblem.gamma_transition_prob_le`), stated in the definitionally reduced
form of the game event so the master rbr-game lemma can consume it.

Public (not `private`) because the L6.6 assembly
(`Spec/KnowledgeSoundness.lean`) consumes it as its γ-round prefix bound. -/
lemma gamma_round_game_bound [SampleableType F] [Nonempty ι]
    (C : Set (ι → F)) (δ : ℝ≥0)
    (encode : (Fin k → F) →ₗ[F] (ι → F))
    (hinj : Function.Injective encode)
    (hC : Set.range encode = C)
    (hδ_pos : 0 < δ) (hδ_lt : δ < (minRelHammingDistCode C : ℝ≥0))
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι F i)) :
    Pr[fun γ : F ↦ ∃ w : Fin k → F,
        (stmtIn, extractZero k (encode : (Fin k → F) → (ι → F)) δ stmtIn) ∉
            outputRelationFor k (encode : (Fin k → F) → (ι → F)) δ ∧
          gammaState k (encode : (Fin k → F) → (ι → F)) δ stmtIn.1.1 stmtIn.1.2.1
            stmtIn.1.2.2 (stmtIn.2 0) (stmtIn.2 1) γ w
      | $ᵗ F] ≤
      (((epsMCA (F := F) (A := F) C δ).toNNReal +
        ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
          / (Fintype.card F : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
  classical
  rw [probEvent_uniformSample_eq_prob_uniformOfFintype]
  by_cases hw : ∃ M, (stmtIn, M) ∈ outputRelationFor k (encode : (Fin k → F) → (ι → F)) δ
  · refine (Pr_eq_zero_of_forall_not _ _ ?_).trans_le zero_le'
    rintro γ ⟨w, hne, -⟩
    exact hne (extractZero_mem k hw)
  · refine le_trans (Pr_le_Pr_of_implies _ _
      (fun γ ↦ ∃ m, gammaState k (encode : (Fin k → F) → (ι → F)) δ stmtIn.1.1
        stmtIn.1.2.1 stmtIn.1.2.2 (stmtIn.2 0) (stmtIn.2 1) γ m) ?_) ?_
    · rintro γ ⟨w, -, hst⟩
      exact ⟨w, hst⟩
    · have hNoWit : ¬ ∃ M : Fin 2 → (Fin k → F),
          (∀ i : Fin 2, ∑ j, M i j * stmtIn.1.1 j = ![stmtIn.1.2.1, stmtIn.1.2.2] i) ∧
          ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
            ∀ i : Fin 2, ∀ j ∈ S, ![stmtIn.2 0, stmtIn.2 1] i j = encode (M i) j := by
        rintro ⟨M, h1, S, h2, h3⟩
        refine hw ⟨M, h1, S, h2, fun i j hj ↦ ?_⟩
        fin_cases i
        · simpa using h3 0 j hj
        · simpa using h3 1 j hj
      refine le_trans (gamma_transition_prob_le C δ encode hinj hC hδ_pos hδ_lt
        stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2 (stmtIn.2 0) (stmtIn.2 1) hNoWit)
        (le_of_eq ?_)
      rw [ENNReal.coe_add, ENNReal.coe_toNNReal (epsMCA_ne_top C δ),
        ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
        ENNReal.coe_natCast, ENNReal.coe_natCast]

omit [DecidableEq ι] [Fintype F] in
-- `[DecidableEq F]` is used in the proof (`by_cases` on the linear constraint, the agreement
-- filter) but does not surface in the statement; same false-positive pattern as
-- `ToyProblem.pair_violates` (SoundnessBounds.lean).
set_option linter.unusedDecidableInType false in
/-- Per-transcript spot-check-round bound for the L6.8 game ([ABF26] §6.2):
for any fixed `(γ, g)` with the post-`γ` state false, the probability over
uniform spot checks that the verifier accepts is at most `(1-δ)^t`. Stated in
the definitionally reduced form of the game event.

Public (not `private`) because the L6.6 assembly
(`Spec/KnowledgeSoundness.lean`) consumes it as its spot-check tail bound. -/
lemma spotcheck_round_game_bound [Nonempty ι]
    (encode : (Fin k → F) → (ι → F)) (δ : ℝ≥0)
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι F i))
    (γ : F) (g : Fin k → F) [SampleableType (Fin t → ι)] :
    Pr[fun xs : Fin t → ι ↦ ∃ _w : PUnit,
        ¬ gammaState k encode δ stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
            (stmtIn.2 0) (stmtIn.2 1) γ g ∧
          accepts (k := k) (t := t) encode stmtIn.1 stmtIn.2 γ g xs
      | $ᵗ (Fin t → ι)] ≤ (((1 - δ) ^ t : ℝ≥0) : ℝ≥0∞) := by
  classical
  rw [probEvent_uniformSample_eq_prob_uniformOfFintype]
  by_cases hbad : gammaState k encode δ stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
      (stmtIn.2 0) (stmtIn.2 1) γ g
  · refine (Pr_eq_zero_of_forall_not _ _ ?_).trans_le zero_le'
    rintro xs ⟨-, hne, -⟩
    exact hne hbad
  by_cases hlin : ∑ j, g j * stmtIn.1.1 j = stmtIn.1.2.1 + γ * stmtIn.1.2.2
  swap
  · refine (Pr_eq_zero_of_forall_not _ _ ?_).trans_le zero_le'
    rintro xs ⟨-, -, hacc⟩
    exact hlin (And.left hacc)
  set A : Finset ι :=
    Finset.univ.filter (fun j ↦ stmtIn.2 0 j + γ * stmtIn.2 1 j = encode g j) with hA
  have hι : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hAcard : (A.card : ℝ) < (1 - (δ : ℝ)) * Fintype.card ι :=
    not_le.mp fun hge ↦ hbad ⟨hlin, A, hge, fun j hj ↦ (Finset.mem_filter.mp hj).2⟩
  have hδ1 : δ ≤ 1 := by
    by_contra hgt
    have h1δ : (1 : ℝ) - (δ : ℝ) < 0 := sub_neg.mpr (by exact_mod_cast not_le.mp hgt)
    linarith [mul_neg_of_neg_of_pos h1δ hι, (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)]
  have hbase : ((A.card : ℝ≥0) / (Fintype.card ι : ℝ≥0)) ≤ 1 - δ := by
    rw [div_le_iff₀ (by exact_mod_cast Fintype.card_pos : (0 : ℝ≥0) < Fintype.card ι),
      ← NNReal.coe_le_coe]
    push_cast [NNReal.coe_sub hδ1]
    linarith
  refine le_trans (Pr_le_Pr_of_implies _ _ (fun xs ↦ ∀ j, xs j ∈ A) ?_) ?_
  · rintro xs ⟨-, -, hacc⟩ j
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (And.right hacc j).symm⟩
  · refine le_trans (prob_uniform_pi_mem_finset_le A t) ?_
    rw [ENNReal.coe_pow]
    refine pow_le_pow_left' ?_ t
    rw [show ((A.card : ℝ≥0∞)) = ((A.card : ℝ≥0) : ℝ≥0∞) from (ENNReal.coe_natCast _).symm,
      show ((Fintype.card ι : ℝ≥0∞)) = ((Fintype.card ι : ℝ≥0) : ℝ≥0∞) from
        (ENNReal.coe_natCast _).symm,
      ← ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
    exact ENNReal.coe_le_coe.mpr hbase

omit [DecidableEq ι] in
/-- **Lemma 6.8 of [ABF26]** (round-by-round knowledge soundness of
Construction 6.2).

For any `δ ∈ (0, δ_min(C))` and fixed injective linear encoder with
range `C` (injectivity is implicit in the paper's encoding map and
load-bearing for the extractor's per-list-pair counting),
the IOR has round-by-round knowledge soundness (ArkLib's
`OracleVerifier.rbrKnowledgeSoundness`, definitionally
`toVerifier.rbrKnowledgeSoundness`) against `R̃_{C,δ}^2`, with
per-round errors

**Quantification note (paper Definition A.5 vs the ArkLib game).** The
paper's rbr definition bounds the bad-transition probability for *every*
fixed transcript prefix (worst case); ArkLib's game samples the prefix
challenges uniformly inside the prover run and bounds the *mixture*. The
in-tree statement is therefore the averaged form, implied by the paper's.
The per-round lemmas feeding this proof (`gamma_round_game_bound`,
`spotcheck_round_game_bound`) hold for every fixed prefix — i.e. they ARE
the paper-strength worst-case facts — so the paper's mathematical content
is fully in-tree; only the bundled top-level game statement averages.

  * `ε_mca(C, δ) + |Λ(C^{≡2}, δ)| / |F|` after the γ round,
  * `(1 − δ)^t` after the spot-check round.

The `(Lambda …).toNat` in the γ-round error is faithful: `Lambda` is
never `⊤` over a finite alphabet (`ListDecodable.Lambda_ne_top`).

**Status: fully proven (sorry-free).** The `KnowledgeStateFunction` is
`rbrKSF` above (relation membership → `gammaState` → the acceptance
predicate; the witness-ignoring final state is PAPER_REVS.md item 10),
the extractor is `rbrExtractor` (round-0 extraction by classical choice),
and the two per-round bounds are `gamma_round_game_bound` (via
`ToyProblem.gamma_transition_prob_le`) and `spotcheck_round_game_bound`,
plugged into the game shape by
`ProtocolSpec.probEvent_simulateQ_addLift_getChallenge_bind_le`. -/
theorem protocol62_rbrKnowledgeSound
    [SampleableType F] [SampleableType ι] [Nonempty ι]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (C : Set (ι → F)) (δ : ℝ≥0)
    (encode : (Fin k → F) →ₗ[F] (ι → F))
    (hinj : Function.Injective encode)
    (hC : Set.range encode = C)
    (hδ_pos : 0 < δ)
    (hδ_lt_min : δ < (minRelHammingDistCode C : ℝ≥0)) :
      (oracleVerifier (k := k) (t := t) (encode : (Fin k → F) → (ι → F))).rbrKnowledgeSoundness
        (WitOut := OutputWitness)
        init impl (outputRelationFor k (encode : (Fin k → F) → (ι → F)) δ)
        (Set.univ : Set ((OutputStatement × ∀ i, OutputOracleStatement i) ×
          OutputWitness))
        (fun i ↦
          -- round 0 (combination randomness γ): MCA + list-decoding term;
          -- round 2 (spot checks): `(1-δ)^t`.
          if i.1 = 0 then
            (epsMCA (F := F) (A := F) C δ).toNNReal +
              ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
                / (Fintype.card F : ℝ≥0)
          else (1 - δ) ^ t) := by
  unfold OracleVerifier.rbrKnowledgeSoundness Verifier.rbrKnowledgeSoundness
  refine ⟨rbrWitMid (F := F) k,
    rbrExtractor k t (encode : (Fin k → F) → (ι → F)) δ,
    rbrKSF k t (encode : (Fin k → F) → (ι → F)) δ init impl, ?_⟩
  intro stmtIn witIn prover i
  obtain ⟨⟨iv, hi⟩, hdir⟩ := i
  rcases iv with _ | _ | _ | iv
  · -- Round 0 (combination randomness γ): the MCA + list-decoding bound.
    refine probEvent_simulateQ_addLift_getChallenge_bind_le init impl
      (prover.runWithLogToRound _ stmtIn witIn) ⟨⟨0, hi⟩, hdir⟩
      (fun x c ↦ (x.1.1, c, x.2)) _ ?_
    exact fun _ ↦ gamma_round_game_bound k C δ encode hinj hC hδ_pos hδ_lt_min stmtIn
  · exact absurd hdir (fun h ↦ Direction.noConfusion h)
  · -- Round 2 (spot checks): the `(1-δ)^t` bound, per fixed `(γ, g)`.
    refine probEvent_simulateQ_addLift_getChallenge_bind_le init impl
      (prover.runWithLogToRound _ stmtIn witIn) ⟨⟨2, hi⟩, hdir⟩
      (fun x c ↦ (x.1.1, c, x.2)) _ ?_
    exact fun x ↦ spotcheck_round_game_bound k t (encode : (Fin k → F) → (ι → F)) δ
      stmtIn (x.1.1 ⟨0, Nat.zero_lt_succ _⟩)
      (x.1.1 ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)
  · exact absurd hi (by omega)

end Protocol

end Spec

end ToyProblem

