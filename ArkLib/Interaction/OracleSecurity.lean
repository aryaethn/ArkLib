import ArkLib.Interaction.OracleReification
import ArkLib.Interaction.Oracle.Continuation
import ArkLib.Interaction.Security

/-!
# Security Definitions for Interaction-Native Oracle Protocols

This module gives the oracle-side analog of `ArkLib.Interaction.Security`,
using the redesigned oracle-only reduction API from `ArkLib.Interaction.Oracle`.

The key design point is that verifier-side acceptance is phrased in terms of
*existence* of concrete output oracle statements compatible with the verifier's
query-level `simulate` interface, rather than by assuming a built-in
reification function. This means:

- The verifier never holds concrete oracle data; it only issues queries.
- Soundness asks: for any malicious prover, the probability that there *exists*
  a concrete output oracle family realizing the verifier's simulation *and*
  the resulting output passes the acceptance predicate is at most `ε`.
- Completeness asks: the honest prover produces concrete output oracle data
  that *does* realize the simulation, and the output passes acceptance.

## Main definitions

- `OracleReduction.completeness` — honest-execution completeness
- `OracleVerifier.soundness` — soundness against arbitrary provers
- `OracleVerifier.knowledgeSoundness` — knowledge soundness with a
  `Straightline` extractor
- `OracleStatement.Realizes` — coherence between a concrete oracle family
  and a deterministic query implementation

## See also

- `Security.lean` — plain (non-oracle) security definitions
- `OracleReification.lean` — optional concrete reification layer
-/

noncomputable section

open OracleComp
open scoped ENNReal

universe u v w

namespace Interaction
namespace OracleDecoration

namespace OracleStatement

/-- A concrete oracle statement `oStmt` realizes a deterministic query
implementation `impl` when every query is answered exactly as `oStmt` would
answer it. -/
def Realizes
    {ιₛ : Type v} {OStmt : ιₛ → Type w}
    [∀ i, OracleInterface (OStmt i)]
    (impl : QueryImpl [OStmt]ₒ Id) (oStmt : OracleStatement OStmt) : Prop :=
  ∀ i (q : OracleInterface.Query (OStmt i)),
    impl ⟨i, q⟩ = OracleInterface.answer (oStmt i) q

@[simp]
theorem realizes_simOracle0
    {ιₛ : Type v} {OStmt : ιₛ → Type w}
    [∀ i, OracleInterface (OStmt i)]
    (oStmt : OracleStatement OStmt) :
    Realizes (OracleInterface.simOracle0 OStmt oStmt) oStmt := by
  intro i q
  rfl

end OracleStatement

namespace OracleReduction

/-- Query-level agreement between a reduction's output-oracle simulation and
concrete output oracle data, relative to an arbitrary deterministic
implementation of the input oracle family. -/
def Simulates
    {ι : Type _} {oSpec : OracleSpec ι}
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (reduction : OracleReduction oSpec SharedIn Context Roles OD
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (shared : SharedIn) (inputImpl : QueryImpl [OStatementIn shared]ₒ Id)
    (tr : Spec.Transcript (Context shared))
    (oStatementOut : OracleStatement (OStatementOut shared tr)) : Prop :=
  ∀ i (q : OracleInterface.Query (OStatementOut shared tr i)),
    simulateQ
        (QueryImpl.add inputImpl
          (OracleDecoration.answerQuery
            (Context shared) (Roles shared) (OD shared) tr))
        (reduction.simulate shared tr ⟨i, q⟩) =
      pure (OracleInterface.answer (oStatementOut i) q)

/-- An abstract reduction input is in the input language when some concrete
oracle statement realizes the supplied input oracle implementation and yields a
full input statement in `langIn`. -/
def InLangIn
    {SharedIn : Type _}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (langIn : ∀ shared,
      Set (StatementWithOracles StatementIn OStatementIn shared))
    (shared : SharedIn) (stmt : StatementIn shared)
    (inputImpl : QueryImpl [OStatementIn shared]ₒ Id) : Prop :=
  ∃ oStatementIn : OracleStatement (OStatementIn shared),
    OracleStatement.Realizes inputImpl oStatementIn ∧
      ⟨stmt, oStatementIn⟩ ∈ langIn shared

namespace Extractor

/-- A straightline extractor for an oracle reduction observes a concrete
realized full input statement, the transcript, the full output statement, and
the malicious prover's terminal witness output. -/
structure Straightline
    (SharedIn : Type _)
    (Context : SharedIn → Spec)
    (StatementIn : SharedIn → Type _) {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (WitnessIn : SharedIn → Type _)
    (StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _)
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _)
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    (WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _) where
  toFun : ∀ (shared : SharedIn)
      (_ : StatementWithOracles StatementIn OStatementIn shared)
      (tr : Spec.Transcript (Context shared)),
      StatementWithOracles
          (fun _ => StatementOut shared tr) (fun _ => OStatementOut shared tr) shared →
        WitnessOut shared tr → WitnessIn shared

instance
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {StatementIn : SharedIn → Type _} {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _} :
    CoeFun
      (Straightline (SharedIn := SharedIn) (Context := Context)
        (StatementIn := StatementIn) (OStatementIn := OStatementIn)
        (WitnessIn := WitnessIn) (StatementOut := StatementOut)
        (OStatementOut := OStatementOut) (WitnessOut := WitnessOut))
      (fun _ => ∀ (shared : SharedIn)
        (_ : StatementWithOracles StatementIn OStatementIn shared)
        (tr : Spec.Transcript (Context shared)),
        StatementWithOracles
            (fun _ => StatementOut shared tr) (fun _ => OStatementOut shared tr) shared →
          WitnessOut shared tr → WitnessIn shared) where
  coe E := E.toFun

end Extractor

/-- Honest completeness for an oracle reduction. This quantifies over
arbitrary accumulated oracle context because oracle reductions can start after
an earlier phase of a larger protocol. -/
def completeness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (reduction : OracleReduction oSpec SharedIn Context Roles OD
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (relIn : ∀ (shared : SharedIn),
      StatementWithOracles StatementIn OStatementIn shared →
        WitnessIn shared → Prop)
    (relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      StatementWithOracles
          (fun _ => StatementOut shared tr) (fun _ => OStatementOut shared tr) shared →
        WitnessOut shared tr → Prop)
    (ε : ℝ≥0∞) : Prop :=
  ∀ (shared : SharedIn)
    (s : StatementWithOracles StatementIn OStatementIn shared)
    (w : WitnessIn shared) {ιₐ : Type _} (accSpec : OracleSpec ιₐ)
    (accImpl : QueryImpl accSpec Id),
      relIn shared s w →
        1 - ε ≤ Pr[fun z =>
          z.2.1.stmt.stmt = z.2.2.1 ∧
            Simulates reduction shared
              (OracleInterface.simOracle0 (OStatementIn shared) s.oracleStmt)
              z.1 z.2.1.stmt.oracleStmt ∧
            relOut shared z.1 z.2.1.stmt z.2.1.wit
          | reduction.execute shared s w accSpec accImpl]

/-- Perfect completeness for an oracle reduction: completeness with error `0`. -/
def perfectCompleteness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (reduction : OracleReduction oSpec SharedIn Context Roles OD
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (relIn : ∀ (shared : SharedIn),
      StatementWithOracles StatementIn OStatementIn shared →
        WitnessIn shared → Prop)
    (relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      StatementWithOracles
          (fun _ => StatementOut shared tr) (fun _ => OStatementOut shared tr) shared →
        WitnessOut shared tr → Prop) : Prop :=
  reduction.completeness relIn relOut 0

/-- An oracle reduction accepts a plain verifier output `stmtOut` when some
concrete output oracle statement both agrees with the reduction's oracle-only
semantics and lands in the target language. -/
def Accepts
    {ι : Type _} {oSpec : OracleSpec ι}
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (reduction : OracleReduction oSpec SharedIn Context Roles OD
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (langOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementWithOracles
        (fun _ => StatementOut shared tr) (fun _ => OStatementOut shared tr) shared))
    (shared : SharedIn) (inputImpl : QueryImpl [OStatementIn shared]ₒ Id)
    (tr : Spec.Transcript (Context shared))
    (stmtOut : StatementOut shared tr) : Prop :=
  ∃ oStatementOut : OracleStatement (OStatementOut shared tr),
    Simulates reduction shared inputImpl tr oStatementOut ∧
      ⟨stmtOut, oStatementOut⟩ ∈ langOut shared tr
end OracleReduction

end OracleDecoration

namespace OracleVerifier

/-- An abstract verifier input is in the input language when some concrete input
oracle statement realizes the supplied input implementation and yields a full
input in `langIn`. -/
def InLangIn
    {SharedIn : Type _}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (langIn : ∀ shared,
      Set (StatementWithOracles StatementIn OStatementIn shared))
    (shared : SharedIn) (stmt : StatementIn shared)
    (inputImpl : QueryImpl [OStatementIn shared]ₒ Id) : Prop :=
  ∃ oStatementIn : OracleStatement (OStatementIn shared),
    OracleDecoration.OracleStatement.Realizes inputImpl oStatementIn ∧
      ⟨stmt, oStatementIn⟩ ∈ langIn shared

/-- Query-level agreement between a verifier's output-oracle simulation and
concrete output oracle data, relative to an arbitrary deterministic
implementation of the input oracle family. -/
def Simulates
    {ι : Type _} {oSpec : OracleSpec ι}
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    (verifier : Interaction.OracleVerifier oSpec SharedIn Context Roles OD
      StatementIn OStatementIn StatementOut OStatementOut)
    (shared : SharedIn) (inputImpl : QueryImpl [OStatementIn shared]ₒ Id)
    (tr : Spec.Transcript (Context shared))
    (oStatementOut : OracleStatement (OStatementOut shared tr)) : Prop :=
  ∀ i (q : OracleInterface.Query (OStatementOut shared tr i)),
    simulateQ
        (QueryImpl.add inputImpl
          (OracleDecoration.answerQuery
            (Context shared) (Roles shared) (OD shared) tr))
        (verifier.simulate shared tr ⟨i, q⟩) =
      pure (OracleInterface.answer (oStatementOut i) q)

/-- A verifier-only oracle protocol accepts a plain output when some concrete
output oracle family realizes the verifier's simulation and lies in the target
language. -/
def Accepts
    {ι : Type _} {oSpec : OracleSpec ι}
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    (verifier : Interaction.OracleVerifier oSpec SharedIn Context Roles OD
      StatementIn OStatementIn StatementOut OStatementOut)
    (langOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementWithOracles
        (fun _ => StatementOut shared tr) (fun _ => OStatementOut shared tr) shared))
    (shared : SharedIn) (inputImpl : QueryImpl [OStatementIn shared]ₒ Id)
    (tr : Spec.Transcript (Context shared))
    (stmtOut : StatementOut shared tr) : Prop :=
  ∃ oStatementOut : OracleStatement (OStatementOut shared tr),
    Simulates verifier shared inputImpl tr oStatementOut ∧
      ⟨stmtOut, oStatementOut⟩ ∈ langOut shared tr

/-- Soundness for a verifier-only oracle protocol. The input oracle access may
be any deterministic implementation; invalidity means that no concrete full
input in `langIn` realizes that implementation. -/
def soundness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    (verifier : Interaction.OracleVerifier oSpec SharedIn Context Roles OD
      StatementIn OStatementIn StatementOut OStatementOut)
    (langIn : ∀ shared,
      Set (StatementWithOracles StatementIn OStatementIn shared))
    (langOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementWithOracles
        (fun _ => StatementOut shared tr) (fun _ => OStatementOut shared tr) shared))
    (ε : ℝ≥0∞) : Prop :=
  ∀ (shared : SharedIn) (stmt : StatementIn shared)
      (inputImpl : QueryImpl [OStatementIn shared]ₒ Id)
      {OutputP : Spec.Transcript (Context shared) → Type _}
      (prover : Spec.Strategy.withRoles (OracleComp oSpec) (Context shared)
        (Roles shared) OutputP)
      {ιₐ : Type _} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id),
      ¬ InLangIn langIn shared stmt inputImpl →
        Pr[fun z => Accepts verifier langOut shared inputImpl z.1 z.2.2.1
          | OracleVerifier.run verifier shared stmt inputImpl prover accSpec accImpl] ≤ ε

/-- Knowledge soundness for a verifier-only oracle protocol. The bad event says
that some realization of the input oracle access together with some compatible
realization of the output oracle access satisfies the output relation, yet the
extractor's recovered witness does not validate that realized full input. -/
def knowledgeSoundness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (verifier : Interaction.OracleVerifier oSpec SharedIn Context Roles OD
      StatementIn OStatementIn StatementOut OStatementOut)
    (relIn : ∀ shared,
      Set (StatementWithOracles StatementIn OStatementIn shared × WitnessIn shared))
    (relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementWithOracles
        (fun _ => StatementOut shared tr) (fun _ => OStatementOut shared tr) shared ×
          WitnessOut shared tr))
    (ε : ℝ≥0∞) : Prop :=
  ∃ extractor : OracleDecoration.OracleReduction.Extractor.Straightline
      SharedIn Context StatementIn OStatementIn WitnessIn
      StatementOut OStatementOut WitnessOut,
  ∀ (shared : SharedIn) (stmt : StatementIn shared)
      (inputImpl : QueryImpl [OStatementIn shared]ₒ Id)
      (prover : Spec.Strategy.withRoles (OracleComp oSpec) (Context shared)
        (Roles shared) (WitnessOut shared))
      {ιₐ : Type _} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id),
      Pr[fun z =>
        ∃ oStatementIn : OracleStatement (OStatementIn shared),
          ∃ oStatementOut : OracleStatement (OStatementOut shared z.1),
            OracleDecoration.OracleStatement.Realizes inputImpl oStatementIn ∧
              Simulates verifier shared inputImpl z.1 oStatementOut ∧
              (⟨z.2.2.1, oStatementOut⟩, z.2.1) ∈ relOut shared z.1 ∧
              (⟨stmt, oStatementIn⟩,
                extractor shared ⟨stmt, oStatementIn⟩ z.1
                  ⟨z.2.2.1, oStatementOut⟩ z.2.1) ∉ relIn shared
        | OracleVerifier.run verifier shared stmt inputImpl prover accSpec accImpl] ≤ ε
end OracleVerifier

end Interaction
