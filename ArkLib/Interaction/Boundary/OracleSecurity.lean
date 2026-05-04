import ArkLib.Interaction.Boundary.Compatibility
import ArkLib.Interaction.Oracle.Security

/-!
# Security Transport Helpers for Oracle Boundaries

This file contains the security-facing consequences of the native oracle
boundary layer. The core fact is query-level: if the inner verifier's output
oracle simulation is realized by a concrete inner output oracle, then the
pulled-back outer simulation is realized by the materialized outer output
oracle.
-/

namespace Interaction
namespace Boundary

open OracleComp OracleSpec

namespace OracleStatementReification

/-- Boundary pullback preserves concrete realization of output-oracle
simulations. This is the query-level lemma used by oracle completeness and
soundness transports. -/
theorem outputRealizes_pullbackSimulate
    {InnerContext : Interaction.Oracle.Spec}
    {Outerιₛᵢ : Type} {OuterOStmtIn : Outerιₛᵢ → Type}
    {Innerιₛᵢ : Type} {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      Interaction.Oracle.Spec.PublicTranscript InnerContext → Type}
    {InnerOStmtOut :
      (pt : Interaction.Oracle.Spec.PublicTranscript InnerContext) →
      Innerιₛₒ pt → Type}
    {Outerιₛₒ :
      Interaction.Oracle.Spec.PublicTranscript InnerContext → Type}
    {OuterOStmtOut :
      (pt : Interaction.Oracle.Spec.PublicTranscript InnerContext) →
      Outerιₛₒ pt → Type}
    [∀ pt i, OracleInterface (InnerOStmtOut pt i)]
    [∀ pt i, OracleInterface (OuterOStmtOut pt i)]
    (access :
      OracleStatementAccess
        (InnerContext := InnerContext)
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (reification :
      OracleStatementReification
        (InnerContext := InnerContext)
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (hRealizes : Realizes access reification)
    (oStmtIn : _root_.Interaction.OracleStatement OuterOStmtIn)
    (pt : Interaction.Oracle.Spec.PublicTranscript InnerContext)
    {ιₘ : Type}
    (msgSpec : OracleSpec ιₘ)
    (msgImpl : QueryImpl msgSpec Id)
    (innerOStmtOut : _root_.Interaction.OracleStatement (InnerOStmtOut pt))
    (simulateInner :
      QueryImpl [InnerOStmtOut pt]ₒ
        (OracleComp ([InnerOStmtIn]ₒ + msgSpec)))
    (hInner :
      ∀ q,
        simulateQ
            (QueryImpl.add
              (OracleInterface.simOracle0
                InnerOStmtIn
                (reification.materializeIn oStmtIn))
              msgImpl)
            (simulateInner q) =
          pure
            ((OracleInterface.simOracle0
              (InnerOStmtOut pt)
              innerOStmtOut) q)) :
    ∀ q,
      simulateQ
          (QueryImpl.add
            (OracleInterface.simOracle0 OuterOStmtIn oStmtIn)
            msgImpl)
          (OracleStatementAccess.pullbackSimulate
            (access := access)
            pt
            msgSpec
            simulateInner
            q) =
        pure
          ((OracleInterface.simOracle0
            (OuterOStmtOut pt)
            (reification.materializeOut oStmtIn pt innerOStmtOut)) q) :=
  pullbackSimulate_materialize
    access
    reification
    hRealizes
    oStmtIn
    pt
    msgSpec
    msgImpl
    innerOStmtOut
    simulateInner
    hInner

end OracleStatementReification

end Boundary
end Interaction
