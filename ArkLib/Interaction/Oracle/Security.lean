/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Execution

/-!
# Security Definitions for Oracle.Spec Protocols

Oracle-side security definitions using the cast-free `Oracle.Spec` framework.

All output types are indexed by `PublicTranscript` rather than the full
`Spec.Transcript`, so output relations, oracle behaviors, and extractors are
definitionally independent of oracle message values.

## Main definitions

### Oracle behavior types
- `Oracle.InputImpl` — deterministic input-oracle behavior.
- `Oracle.OutputImpl` — `PublicTranscript`-indexed output-oracle behavior.
- `Oracle.OutputRealizes` — query-level agreement between behavior and concrete
  oracle family.

### Relations
- `Oracle.Reduction.InputRelation` — relative validity for reduction inputs.
- `Oracle.Reduction.OutputRelation` — relative validity for reduction outputs.
- `Oracle.Verifier.InputLanguage` — witness-free input language.
- `Oracle.Verifier.OutputLanguage` — witness-free output language.

### Reduction security
- `Oracle.Reduction.completeness` — honest completeness (with `OutputRealizes`).
- `Oracle.Reduction.perfectCompleteness` — completeness with error `0`.

### Verifier security
- `Oracle.Verifier.soundness` — oracle soundness.
- `Oracle.Verifier.knowledgeSoundness` — oracle knowledge soundness. The
  adversarial prover outputs only a witness `witOut`; the extractor sees the
  input statement and oracle, the full transcript, the verifier's output
  statement, the verifier's output-oracle simulator, and `witOut`, and must
  produce a valid input witness. The verifier's output oracle is defined by
  `simulate`, so the prover is **not** asked to produce concrete output oracle
  data.
- `Oracle.Verifier.knowledgeSoundness_implies_soundness` — KS implies soundness
  under a transcript-indexed `acceptWitness` and `hLangOut : langOut ⟹ relOut`.
-/

noncomputable section

open OracleComp
open scoped ENNReal

universe u v w

namespace Interaction
namespace Oracle

/-! ## Oracle behavior types -/

abbrev InputImpl
    {SharedIn : Type _}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (shared : SharedIn) :=
  QueryImpl [OStatementIn shared]ₒ Id

abbrev OutputImpl
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    (OStatementOut :
      (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Context shared)) →
      ιₛₒ shared pt → Type _)
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (shared : SharedIn)
    (pt : Spec.PublicTranscript (Context shared)) :=
  QueryImpl [OStatementOut shared pt]ₒ
    (OracleComp
      ([OStatementIn shared]ₒ +
        (Context shared).toOracleSpec (OracleDeco shared) pt))

/-- Query-level agreement between an output-oracle behavior and a concrete
output oracle family, relative to a deterministic input-oracle implementation.

Takes the full transcript `tr` (needed to answer oracle queries via
`Spec.answerQuery`) and computes the `PublicTranscript` index for the
output oracle types. -/
def OutputRealizes
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (shared : SharedIn)
    (inputImpl : InputImpl OStatementIn shared)
    (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec)
    (outputImpl :
      OutputImpl (Context := Context) (OracleDeco := OracleDeco)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut) shared
        ((Context shared).projectPublic tr))
    (oStatementOut :
      OracleStatement (OStatementOut shared ((Context shared).projectPublic tr))) :
    Prop :=
  let pt := (Context shared).projectPublic tr
  ∀ i (q : OracleInterface.Query (OStatementOut shared pt i)),
    simulateQ
        (QueryImpl.add inputImpl
          (Spec.answerQuery (Context shared) (OracleDeco shared) tr))
        (outputImpl ⟨i, q⟩) =
      pure (OracleInterface.answer (oStatementOut i) q)

/-! ## Reduction security -/

namespace Reduction

abbrev InputRelation
    {SharedIn : Type _}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (WitnessIn : SharedIn → Type _) :=
  (shared : SharedIn) →
  StatementIn shared →
  InputImpl OStatementIn shared →
  WitnessIn shared →
  Prop

abbrev OutputRelation
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _)
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _) :=
  (shared : SharedIn) →
  (inputImpl : InputImpl OStatementIn shared) →
  (pt : Spec.PublicTranscript (Context shared)) →
  StatementOut shared pt →
  OutputImpl (Context := Context) (OracleDeco := OracleDeco)
    (OStatementIn := OStatementIn) (OStatementOut := OStatementOut) shared pt →
  WitnessOut shared pt →
  Prop

namespace Extractor

/-- A straightline extractor for an oracle reduction. The extractor is a
deterministic function of:

- the shared context `shared` and input statement `stmt`,
- the deterministic input oracle implementation `inputImpl`,
- the **full transcript** `tr` (including the concrete prover oracle message
  values, which are needed to answer queries under `outputImpl` via
  `Spec.answerQuery`),
- the verifier's output statement `stmtOut` (indexed by `projectPublic tr`),
- the verifier's output oracle simulator `outputImpl` (a `QueryImpl` that
  defines the output oracle semantics relative to `inputImpl` and the full
  transcript),
- the adversarial prover's witness output `witOut`.

It reconstructs an input witness. Note that the extractor does *not* receive
concrete output oracle data: the output oracle's semantics are fully captured
by `outputImpl`, which the verifier defines. Access to the full transcript is
what lets the extractor actually evaluate `outputImpl` at any query, since
`outputImpl`'s underlying query spec uses `Spec.answerQuery` on `tr` to respond
to oracle-message queries. -/
structure Straightline
    (SharedIn : Type _)
    (Context : SharedIn → Spec)
    (OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared))
    (StatementIn : SharedIn → Type _)
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (WitnessIn : SharedIn → Type _)
    (StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _)
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _)
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _) where
  toFun : ∀ (shared : SharedIn)
      (_stmt : StatementIn shared)
      (_inputImpl : InputImpl OStatementIn shared)
      (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec)
      (_stmtOut : StatementOut shared ((Context shared).projectPublic tr)),
      OutputImpl (Context := Context) (OracleDeco := OracleDeco)
          OStatementIn OStatementOut shared ((Context shared).projectPublic tr) →
        WitnessOut shared ((Context shared).projectPublic tr) → WitnessIn shared

instance
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _} :
    CoeFun
      (Straightline
        (SharedIn := SharedIn) (Context := Context) (OracleDeco := OracleDeco)
        (StatementIn := StatementIn) (OStatementIn := OStatementIn)
        (WitnessIn := WitnessIn) (StatementOut := StatementOut)
        (OStatementOut := OStatementOut) (WitnessOut := WitnessOut))
      (fun _ => ∀ (shared : SharedIn)
        (_stmt : StatementIn shared)
        (_inputImpl : InputImpl OStatementIn shared)
        (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec)
        (_stmtOut : StatementOut shared ((Context shared).projectPublic tr)),
        OutputImpl (Context := Context) (OracleDeco := OracleDeco)
            OStatementIn OStatementOut shared
            ((Context shared).projectPublic tr) →
          WitnessOut shared ((Context shared).projectPublic tr) →
            WitnessIn shared) where
  coe E := E.toFun

end Extractor

/-- Honest completeness for an `Oracle.Reduction`. The honest prover produces
concrete output oracle data `oStmtOut`, and we check three conditions:
1. The prover's output statement agrees with the verifier's.
2. `OutputRealizes`: the verifier's simulate agrees with the prover's concrete
   `oStmtOut`.
3. The output relation `relOut` holds. -/
def completeness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    (reduction : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (relIn :
      InputRelation (StatementIn := StatementIn) (OStatementIn := OStatementIn)
        WitnessIn)
    (relOut :
      OutputRelation (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
        WitnessOut)
    (ε : ℝ≥0∞) : Prop :=
  ∀ (shared : SharedIn)
    (s : StatementWithOracles StatementIn OStatementIn shared)
    (w : WitnessIn shared),
      relIn shared s.stmt
        (OracleInterface.simOracle0 (OStatementIn shared) s.oracleStmt) w →
        let inputImpl := OracleInterface.simOracle0 (OStatementIn shared) s.oracleStmt
        1 - ε ≤ Pr[fun z =>
          let pt := (Context shared).projectPublic z.1
          z.2.1.stmt.stmt = z.2.2.1 ∧
            OutputRealizes shared inputImpl z.1
              (reduction.verifier.simulate shared pt)
              z.2.1.stmt.oracleStmt ∧
            relOut shared inputImpl pt z.2.2.1
              (reduction.verifier.simulate shared pt)
              z.2.1.wit
          | reduction.executeConcrete shared s w]

def perfectCompleteness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    (reduction : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (relIn :
      InputRelation (StatementIn := StatementIn) (OStatementIn := OStatementIn)
        WitnessIn)
    (relOut :
      OutputRelation (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
        WitnessOut) : Prop :=
  completeness reduction relIn relOut 0

end Reduction

/-! ## Verifier security -/

namespace Verifier

abbrev InputLanguage
    {SharedIn : Type _}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)] :=
  (shared : SharedIn) →
  StatementIn shared →
  InputImpl OStatementIn shared →
  Prop

abbrev OutputLanguage
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _)
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)] :=
  (shared : SharedIn) →
  (inputImpl : InputImpl OStatementIn shared) →
  (pt : Spec.PublicTranscript (Context shared)) →
  StatementOut shared pt →
  OutputImpl (Context := Context) (OracleDeco := OracleDeco)
    OStatementIn OStatementOut shared pt →
  Prop

def soundness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco StatementIn
      OStatementIn StatementOut OStatementOut)
    (langIn : InputLanguage (StatementIn := StatementIn) (OStatementIn := OStatementIn))
    (langOut :
      OutputLanguage (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut))
    (ε : ℝ≥0∞) : Prop :=
  ∀ (shared : SharedIn) (stmt : StatementIn shared)
      (inputImpl : InputImpl OStatementIn shared)
      {OutputP : Interaction.Spec.Transcript
        (Context shared).toInteractionSpec → Type _}
      (prover : Interaction.Spec.Strategy.withRoles (OracleComp oSpec)
        (Context shared).toInteractionSpec
        ((Context shared).toSpecRoles (Roles shared)) OutputP),
      ¬ langIn shared stmt inputImpl →
        Pr[fun z =>
          let pt := (Context shared).projectPublic z.1
          langOut shared inputImpl pt z.2.2.1
            (verifier.simulate shared pt)
          | verifier.run shared stmt inputImpl prover] ≤ ε

/-- Knowledge soundness for an `Oracle.Verifier`. The adversarial prover outputs
only a witness `witOut`; the extractor receives the input statement, input
oracle implementation, the **full transcript** `tr` (public transcript plus
concrete prover oracle messages), the verifier's output statement, the
verifier's output-oracle simulator, and `witOut`, and must produce a valid
input witness.

The bound is: `Pr[relOut(simulate, witOut) ∧ ¬ relIn(extractor …)] ≤ ε`.

The prover does **not** output concrete output oracle data: the output oracle's
semantics are defined by the verifier via `simulate`, not asserted by the
prover. See `Oracle/Security.lean`'s design notes for context. -/
def knowledgeSoundness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    (verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco StatementIn
      OStatementIn StatementOut OStatementOut)
    (relIn :
      Reduction.InputRelation (StatementIn := StatementIn)
        (OStatementIn := OStatementIn) WitnessIn)
    (relOut :
      Reduction.OutputRelation (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
        WitnessOut)
    (ε : ℝ≥0∞) : Prop :=
  ∃ extractor : Reduction.Extractor.Straightline
      SharedIn Context OracleDeco StatementIn OStatementIn WitnessIn
      StatementOut OStatementOut WitnessOut,
  ∀ (shared : SharedIn) (stmt : StatementIn shared)
      (inputImpl : InputImpl OStatementIn shared)
      (prover : Interaction.Spec.Strategy.withRoles (OracleComp oSpec)
        (Context shared).toInteractionSpec
        ((Context shared).toSpecRoles (Roles shared))
        (fun tr => WitnessOut shared ((Context shared).projectPublic tr))),
      Pr[fun z =>
        let pt := (Context shared).projectPublic z.1
        let witOut := z.2.1
        relOut shared inputImpl pt z.2.2.1
          (verifier.simulate shared pt) witOut ∧
          ¬ relIn shared stmt inputImpl
            (extractor shared stmt inputImpl z.1 z.2.2.1
              (verifier.simulate shared pt) witOut)
        | verifier.run shared stmt inputImpl prover] ≤ ε

/-- Knowledge soundness implies soundness, under a transcript-indexed choice
of accepting witness.

The caller supplies:
- `acceptWitness`: for every transcript `tr`, a candidate output witness at
  `projectPublic tr`.
- `hLang`: outside the input language, no witness satisfies the input relation
  (this makes `hLang` applicable to the extractor's output).
- `hLangOut`: whenever the verifier's output is in `langOut`, the output
  relation holds for `acceptWitness` at that transcript.

The proof constructs a KS adversary from the soundness adversary by mapping
its output through `acceptWitness`. Since `acceptWitness` depends only on the
full transcript, this is a valid `Strategy.mapOutputWithRoles` map. The
`Spec.runWithOracleCounterpart_mapOutputWithRoles` lemma guarantees this does
not change the transcript or verifier-side output distribution. -/
theorem knowledgeSoundness_implies_soundness
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    [LawfulMonad (OracleComp oSpec)] [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn StatementOut OStatementOut}
    {relIn :
      Reduction.InputRelation (StatementIn := StatementIn)
        (OStatementIn := OStatementIn) WitnessIn}
    {relOut :
      Reduction.OutputRelation (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
        WitnessOut}
    {ε : ℝ≥0∞}
    (hKS : knowledgeSoundness verifier relIn relOut ε)
    (langIn : InputLanguage (StatementIn := StatementIn)
      (OStatementIn := OStatementIn))
    (hLang :
      ∀ shared stmt inputImpl,
        ¬ langIn shared stmt inputImpl →
          ∀ w, ¬ relIn shared stmt inputImpl w)
    (langOut :
      OutputLanguage (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut))
    (acceptWitness :
      ∀ (shared : SharedIn)
        (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec),
        WitnessOut shared ((Context shared).projectPublic tr))
    (hLangOut :
      ∀ shared inputImpl
        (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec)
        (stmtOut : StatementOut shared ((Context shared).projectPublic tr)),
        langOut shared inputImpl ((Context shared).projectPublic tr) stmtOut
          (verifier.simulate shared ((Context shared).projectPublic tr)) →
        relOut shared inputImpl ((Context shared).projectPublic tr) stmtOut
          (verifier.simulate shared ((Context shared).projectPublic tr))
          (acceptWitness shared tr)) :
    soundness verifier langIn langOut ε := by
  rcases hKS with ⟨extractor, hKS⟩
  intro shared stmt inputImpl OutputP prover hs
  let proverKS :
      Interaction.Spec.Strategy.withRoles (OracleComp oSpec)
        (Context shared).toInteractionSpec
        ((Context shared).toSpecRoles (Roles shared))
        (fun tr => WitnessOut shared ((Context shared).projectPublic tr)) :=
    Interaction.Spec.Strategy.mapOutputWithRoles
      (fun tr _ => acceptWitness shared tr) prover
  have hrun :
      verifier.run shared stmt inputImpl proverKS =
        (fun z => ⟨z.1, acceptWitness shared z.1, z.2.2⟩) <$>
          verifier.run shared stmt inputImpl prover := by
    simp only [Verifier.run, proverKS]
    rw [Spec.runWithOracleCounterpart_mapOutputWithRoles]
    simp [Functor.map_map]
  have hKS' := hKS shared stmt inputImpl proverKS
  rw [hrun, probEvent_map] at hKS'
  refine le_trans ?_ hKS'
  refine probEvent_mono ?_
  intro z _ hz
  refine ⟨hLangOut shared inputImpl z.1 z.2.2.1 hz, ?_⟩
  exact hLang shared stmt inputImpl hs
    (extractor shared stmt inputImpl z.1 z.2.2.1
      (verifier.simulate shared ((Context shared).projectPublic z.1))
      (acceptWitness shared z.1))

end Verifier

end Oracle
end Interaction
