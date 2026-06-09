/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemma
import ArkLib.OracleReduction.Security.StateRestoration
import ArkLib.OracleReduction.FiatShamir.SingleSalt

/-!
# Soundness and Knowledge Soundness of Duplex Sponge Fiat–Shamir (CO25 §6)

This file formalizes Theorems 6.1 and 6.2 from CO25 and Construction 6.3.

## Main results

- **Theorem 6.1** (`theorem_6_1_soundness`): if the interactive proof IP has
  state-restoration soundness, then the DSFS scheme is sound with error `κ + η★`.

- **Construction 6.3** (`dsfsStraightlineExtractor`): straightline extractor that
  reconstructs the IP transcript from the DSFS proof (via the sponge) and calls the IP SR
  extractor `E_IP` (with `default` logs, matching the SR-KS experiment).

- **Theorem 6.2** (`theorem_6_2_straightline`): if IP has SR-KS, then the DSFS scheme has
  straightline KS (via Construction 6.3) with error `κ + η★`, stated in the bespoke,
  query-bounded `dsfsKnowledgeSoundnessBounded`.

## Proof strategy

```
DSFS KS game  ≈  Hyb_0   (oracle identification using hyb0Init/hyb0Impl)
Hyb_0 ≈ Hyb_4 + η★        (Key Lemma 5.1)
Hyb_4 = IP SR game        (fsChallengeOracle = srChallengeOracle, alias)
IP SR game ≤ κ             (IP SR-soundness/KS hypothesis)
```

Steps 1–2 use `lemma_5_1`.  Step 3 (Hyb_4 = IP SR game) requires the
**Fiat–Shamir lifting theorem** (Seam #2 from `Section6_plan.md`) — currently
absent from `Implications.lean`.  See `SingleSalt.lean` for the single-salt
version (`theorem_3_18_soundness`, `theorem_3_19_straightline_ks`), from which
these theorems follow as corollaries.

## Type-level compatibility

- `Verifier.duplexSpongeFiatShamirSalted δ V` is a `NonInteractiveVerifier` (0
  challenge rounds), so its `srChallengeOracle` is empty and SR prover = plain
  `OracleComp` against `duplexSpongeChallengeOracle` = `MaliciousProver`.

- `hyb0Init`/`hyb0Impl oSpecImpl` (from `KeyLemma.lean`) are the canonical
  `(init, impl)` for `Verifier.soundness`/`.knowledgeSoundness` on the DSFS verifier.

- `fsChallengeOracle = srChallengeOracle` (alias), so `Hyb_4`'s oracle IS the
  SR challenge oracle for the salt-augmented IP `saltedIPVerifier V`.
-/

open OracleComp OracleSpec ProtocolSpec

/-- **Probability transfer across total-variation distance** (the `Pr`-level form of
`tvDist`).  For any event `p` and two probabilistic computations, the event probability under
`mx` is at most its probability under `my` plus `tvDist mx my`.  This is the standard fact
`μ(E) ≤ ν(E) + d_TV(μ, ν)`, lifted from VCVio's `Bool`-valued
`abs_probOutput_toReal_sub_le_tvDist` to a general `Prop`-valued event via the indicator map
`b ↦ decide (p b)`.

Used in `theorem_6_1_soundness` to turn the Key-Lemma `tvDist` bound between `Hyb_0` and
`Hyb_4` into a bound on the false-acceptance probability. -/
theorem probEvent_le_probEvent_add_ofReal_tvDist
    {β : Type} (mx my : ProbComp β) (p : β → Prop) :
    Pr[ p | mx] ≤ Pr[ p | my] + ENNReal.ofReal (tvDist mx my) := by
  classical
  -- Indicator map collapsing the event to a `Bool`.
  let g : β → Bool := fun b => decide (p b)
  -- `Pr[= true | g <$> mz] = Pr[p | mz]` for any `mz`.
  have key : ∀ mz : ProbComp β, Pr[= true | g <$> mz] = Pr[ p | mz] := by
    intro mz
    rw [← probEvent_eq_eq_probOutput, probEvent_map]
    refine probEvent_ext fun x _ => ?_
    simp [g, Function.comp]
  -- Bool-level transfer, then rewrite via `key`, then absorb `tvDist_map_le`.
  have hbool := abs_probOutput_toReal_sub_le_tvDist (g <$> mx) (g <$> my)
  rw [key mx, key my] at hbool
  have hmap : tvDist (g <$> mx) (g <$> my) ≤ tvDist mx my := tvDist_map_le g mx my
  have hreal : Pr[ p | mx].toReal ≤ Pr[ p | my].toReal + tvDist mx my := by
    have hle := (abs_le.mp hbool).2
    linarith
  -- Lift the real inequality back to `ℝ≥0∞`.
  have hd : 0 ≤ tvDist mx my := tvDist_nonneg mx my
  have ha : Pr[ p | mx] ≠ ⊤ := probEvent_ne_top
  have hb : Pr[ p | my] ≠ ⊤ := probEvent_ne_top
  have hsum_ne : Pr[ p | my] + ENNReal.ofReal (tvDist mx my) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hb, ENNReal.ofReal_ne_top⟩
  refine (ENNReal.toReal_le_toReal ha hsum_ne).mp ?_
  rw [ENNReal.toReal_add hb ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hd]
  exact hreal

/-- **Averaging / law-of-total-probability bound** (reusable toolkit). If the event `q` has
probability at most `r` under `f a` for *every* intermediate value `a`, then it has probability at
most `r` under `mx >>= f`, no matter how `mx` is distributed.

This is the workhorse for "adaptively-chosen-statement soundness ≤ per-statement soundness error":
instantiate `q := fun out => stmtIn out ∉ langIn ∧ accepts out`, which is `0` when the malicious
prover picks a *true* statement and `≤ ε` (verifier soundness) when it picks a *false* one — so the
hypothesis `∀ a, Pr[q | f a] ≤ ε` holds and the chosen-statement game is bounded by `ε`. Reused in
`hyb4_falseAccept_le_fsSoundnessError` (Theorem 3.5) and applicable to KS (Theorem 6.2) and ZK. -/
theorem probEvent_bind_le_const {α β : Type} (mx : ProbComp α) (f : α → ProbComp β)
    (q : β → Prop) (r : ENNReal) (h : ∀ a, Pr[ q | f a] ≤ r) :
    Pr[ q | mx >>= f] ≤ r := by
  rw [probEvent_bind_eq_tsum]
  calc ∑' a, Pr[= a | mx] * Pr[ q | f a]
      ≤ ∑' a, Pr[= a | mx] * r := by gcongr with a; exact h a
    _ = (∑' a, Pr[= a | mx]) * r := ENNReal.tsum_mul_right
    _ ≤ 1 * r := by gcongr; exact tsum_probOutput_le_one
    _ = r := one_mul r

namespace DuplexSpongeFS

open DuplexSpongeFS.ProverTransform DuplexSpongeFS.TraceTransform DuplexSpongeFS.DSTraceStorage
open DuplexSpongeFS.KeyLemma

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)]
  [codec : Codec pSpec U]
  {δ : Nat}
  {Salt : Type} [VCVCompatible Salt] [SaltCodec U δ Salt]
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]

noncomputable section

-- The `Fintype`/`DecidableEq` instances below are not referenced in the theorem *types*, but
-- are required in the proof *bodies* (by `dsfsStraightlineExtractor` and `lemma_5_1`).
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
## Construction 6.3: DSFS straightline extractor

`saltedIPVerifier`, `langInSalted`, and `relInSalted` are defined in
`ArkLib.OracleReduction.FiatShamir.SingleSalt` (available here via `KeyLemma`'s import).
-/

/-- CO25 Construction 6.3 — DSFS straightline extractor.

Given an IP SR extractor `E_IP` for the salt-augmented IP, extract the IP input
witness from a DSFS adversary view by:
1. Reading the DSFS proof `(τ, messages)` from the transcript (single P→V message).
2. Applying `D2STrace` to the DSFS prover query log to get the basic-FS log.
3. Reconstructing the IP transcript from `messages` and the FS oracle entries.
4. Calling `E_IP` on the reconstructed view.

The extractor operates over the `NonInteractiveVerifier` pSpec
`⟨!v[.P_to_V], !v[DSSaltedProof pSpec U δ]⟩`. -/
noncomputable def dsfsStraightlineExtractor
    [Fintype U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (E_IP : Extractor.StateRestoration oSpec (StmtIn × Salt) WitIn WitOut pSpec) :
    Extractor.Straightline
      (oSpec + duplexSpongeChallengeOracle StmtIn U)
      StmtIn WitIn WitOut
      ⟨!v[.P_to_V], !v[DSSaltedProof (pSpec := pSpec) (U := U) δ]⟩ :=
  fun stmtIn witOut transcript _proveQueryLog _verifyQueryLog => do
    -- Construction 6.3 (straightline). The SR-KS experiment (`coinKSExperimentProb`) feeds the IP
    -- extractor `default` query logs, so only the *transcript* is needed here — no `D2STrace` on
    -- the prover log is required for the extractor itself.
    -- 1. The single P→V message *is* the DSFS proof `(τ, messages)`.
    let saltedProof : DSSaltedProof (pSpec := pSpec) (U := U) δ := transcript 0
    -- 2-3. Reconstruct the IP `FullTranscript` from `messages` + salt `τ` via the duplex sponge —
    --      the *same* forward derivation the DSFS verifier uses (`deriveTranscriptDSFSSalted`).
    let ⟨_, ipTranscript⟩ ← OptionT.lift (liftComp
      (saltedProof.2.deriveTranscriptDSFSSalted (pSpec := pSpec) (oSpec := oSpec) (U := U)
        stmtIn saltedProof.1)
      (oSpec + duplexSpongeChallengeOracle StmtIn U))
    -- 4-5. Call the IP SR extractor on `(𝕩, encode τ)` + the reconstructed transcript, lifted from
    --      base `oSpec` to the DSFS spec.  (Logs are `default`, matching `coinKSExperimentProb`.)
    OptionT.lift (liftComp
      (E_IP (stmtIn, SaltCodec.encode saltedProof.1) witOut ipTranscript default default)
      (oSpec + duplexSpongeChallengeOracle StmtIn U))

/-! ## Theorem 6.1: IP SR-soundness → DSFS soundness -/

/-- The **false-acceptance event** for the DSFS soundness game, read off a
`BasicFiatShamirGameOutput` (the common output type of `Hyb_0` … `Hyb_4`): the malicious prover
submitted a statement `stmtIn ∉ langIn` yet the verifier accepted into `stmtOut ∈ langOut`.
`none` (an aborted run) is not a soundness break. -/
def dsfsSoundnessEvent (langIn : Set StmtIn) (langOut : Set StmtOut) :
    Option (BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt)) → Prop
  | some out => out.1 ∉ langIn ∧ out.2.1 ∈ langOut
  | none => False

/-- The **raw** false-acceptance event on a `DSFSGameOutput`, matching CO25's
`ε_NARG = Pr[ |𝕩| ≤ n ∧ 𝕩 ∉ ℒ(ℛ) ∧ 𝒱^{h,p}(𝕩,π) = 1 ]`. Same shape as `dsfsSoundnessEvent`,
but on the duplex-sponge game output *before* the §5.8 line-4 trace map is applied. -/
def dsfsRawEvent (langIn : Set StmtIn) (langOut : Set StmtOut) :
    Option (DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)) → Prop
  | some out => out.1 ∉ langIn ∧ out.2.1 ∈ langOut
  | none => False

/-- **CO25 §6.1 step L1** — `ε_NARG = Pr[Hyb₀]`.

The raw duplex-sponge game `dsfsGameDist` and the §5.8 trace-mapped `Hyb₀ = mappedDSFSGameDist`
assign the *same* false-acceptance probability: the line-4 trace map `D2STrace` only rewrites the
query-log component, leaving the `(𝕩, stmtOut)` pair — hence the acceptance event — untouched.

`mappedDSFSGameDist` keeps `(𝕩, stmtOut)` even when trace synthesis aborts (it returns
`some (𝕩, stmtOut, …, default)`, matching CO25 Hyb₀'s `tr = ⊥` bad event that preserves the
acceptance bit `b`), so the trace map never suppresses acceptance and the `(𝕩, stmtOut)` marginal
of `Hyb₀` equals the raw game's.

The hypothesis `hTraceNeverFail` is essential: the equality holds only when the trace map raises no
`OracleComp.failure` (it may legitimately produce `Option none`, the bad-trace value — that is kept
via `default` — but an `OracleComp` failure would cut probability mass). For the concrete
`d2sTraceSalted` this holds (its `failure`s are `OptionT.fail`, not `OracleComp.failure`); the
caller discharges it. -/
theorem dsfsGame_falseAccept_eq_hyb0
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sTraceTransform : D2STraceTransform (Salt := Salt) (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (duplexSpongeChallengeOracle StmtIn U)) :
    Pr[ dsfsRawEvent langIn langOut |
        dsfsGameDist hyb0Init (hyb0Impl oSpecImpl) V maliciousProver]
      = Pr[ dsfsSoundnessEvent langIn langOut |
          hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
            oSpecImpl V maliciousProver d2sTraceTransform] := by
  classical
  -- Expose `Hyb₀ = dsfsGameDist >>= F`, then decompose both probabilities over the game output `a`.
  unfold hyb_0 mappedDSFSGameDist
  rw [probEvent_bind_eq_tsum]
  conv_lhs => rw [← bind_pure (dsfsGameDist hyb0Init (hyb0Impl oSpecImpl) V maliciousProver)]
  rw [probEvent_bind_eq_tsum]
  refine tsum_congr fun a => ?_
  congr 1
  -- Per game output `a`: the post-processor `F a` and the raw event agree on `(𝕩, stmtOut)`.
  rcases a with _ | ⟨stmtIn, stmtOut, proof, fullTraceDS⟩
  · -- aborted game run: both sides reject.
    simp [dsfsRawEvent, dsfsSoundnessEvent]
  · -- accepting run: trace map keeps `(stmtIn, stmtOut)`; event is constant over the trace sampling.
    rw [probEvent_bind_of_const _
      (r := if stmtIn ∉ langIn ∧ stmtOut ∈ langOut then (1 : ENNReal) else 0)
      (fun o _ => by rcases o with _ | t <;> simp [dsfsSoundnessEvent])]
    simp [dsfsRawEvent]

/-! ### Canonical state-restoration oracle model matching `Hyb_4`

`Hyb_4` samples its Fiat–Shamir oracle eagerly from `D_IP_salted = OracleDistribution.uniform
(fsChallengeOracle (StmtIn × Salt) pSpec)`, whose carrier `OracleFamily (fsChallengeOracle …) =
(q : Domain) → Range q` is *definitionally* `QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id`
(recall `fsChallengeOracle = srChallengeOracle` and `Id α = α`).  The two definitions below package
that same uniform-function model as the `(init, impl)` pair consumed by
`Verifier.StateRestoration.soundness`, so the IP's SR-soundness hypothesis is stated against
exactly the oracle distribution `Hyb_4` uses. -/

/-- Canonical SR challenge-oracle `init` matching `Hyb_4`'s eager `𝒟_IP_salted` sampling:
draw one uniform Fiat–Shamir challenge function. -/
def srInitDIP :
    ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) :=
  (D_IP_salted (StmtIn := StmtIn) (Salt := Salt) pSpec).sample

/-- Canonical SR shared-oracle handler: answer `oSpec` queries via `oSpecImpl`, ignoring the
(pre-sampled, never-mutated) challenge function held in the state — matching the `.inl` branch of
`hybChallengeImpl`. -/
def srImplLift (oSpecImpl : QueryImpl oSpec ProbComp) :
    QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp) :=
  fun q => StateT.lift (oSpecImpl q)

/-- The sampler for `D2SAlgo`'s private coins `(Unit →ₒ U) + unifSpec`: alphabet samples via
`d2sUnitSampleImpl`, uniform `unifSpec` samples forwarded. This is the `auxImpl` that the
coin-bearing SR-soundness experiment uses to answer the compiled prover's coins — exactly what
`hybChallengeImpl`'s auxiliary branches do in `Hyb₄`. -/
def d2sAuxImpl [SampleableType U] :
    QueryImpl ((Unit →ₒ U) + unifSpec) ProbComp :=
  d2sUnitSampleImpl.addLift (fun q => (query (spec := unifSpec) q : ProbComp _))

/-- The §6.1 canonical SR handler for `Hyb₄`'s oracle model, written as an explicit 4-slot handler
(avoiding nested-`addLift` elaboration): `oSpec` via `srImplLift oSpecImpl`, the pre-sampled FS
challenge function via `srChallengeQueryImpl'`, `D2SAlgo`'s `(Unit →ₒ U)` coins via
`d2sUnitSampleImpl`, and its `unifSpec` coins forwarded.  This is exactly the per-slot reduction of
`(srImplLift oSpecImpl).addLift (srChallengeQueryImpl'.addLift d2sAuxImpl)` used by
`coinSRExperimentProb` (each `addLift` slot unfolds via `add_apply_inl/inr` + `liftTarget`). -/
def srHyb4Impl (oSpecImpl : QueryImpl oSpec ProbComp) :
    QueryImpl (oSpec + (srChallengeOracle (StmtIn × Salt) pSpec + ((Unit →ₒ U) + unifSpec)))
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp) :=
  fun
  | .inl qS => StateT.lift (oSpecImpl qS)
  | .inr (.inl qC) => srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec) qC
  | .inr (.inr (.inl qU)) => StateT.lift (d2sUnitSampleImpl (U := U) qU)
  | .inr (.inr (.inr qN)) => StateT.lift (query (spec := unifSpec) qN)

/-- **DSFS §6.1 handler identity.** The eager 4-slot hybrid handler `hybChallengeImpl` for the
salted FS oracle `𝒟_IP_salted` answers each of its four query slots *exactly* as the canonical SR
handler `srHyb4Impl`.  The only non-`rfl` slot is the challenge oracle: the eagerly-sampled uniform
function-table answers a query by applying the table
(`𝒟_IP_salted.toImpl k q = tableQueryImpl k q = pure (k q)`), which is precisely
`srChallengeQueryImpl'`; the other three slots are `StateT.lift`s of the same per-slot samplers
(the eager `get` is discarded). -/
theorem hybChallengeImpl_eq_srAddLift (oSpecImpl : QueryImpl oSpec ProbComp) :
    hybChallengeImpl (oSpec := oSpec) (U := U)
        (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec)
        oSpecImpl (D_IP_salted (StmtIn := StmtIn) (Salt := Salt) pSpec)
      = srHyb4Impl oSpecImpl := by
  ext q : 1
  rcases q with qS | qC | qU | qN
  · -- `oSpec` slot: `StateT.lift (oSpecImpl qS)` (the eager `get` is discarded).
    funext s
    simp [hybChallengeImpl, srHyb4Impl, StateT.lift, bind_pure]
  · -- challenge slot: `𝒟_IP_salted.toImpl k qC = pure (k qC)`, matching `srChallengeQueryImpl'`.
    funext s
    simp only [hybChallengeImpl, srHyb4Impl, srChallengeQueryImpl', D_IP_salted,
      OracleReduction.OracleDistribution.uniform, OracleReduction.OracleDistribution.functionTable,
      OracleReduction.tableQueryImpl, bind_pure]
    rfl
  · -- `(Unit →ₒ U)` coin slot: `StateT.lift (d2sUnitSampleImpl qU)`.
    funext s
    simp [hybChallengeImpl, srHyb4Impl, StateT.lift, bind_pure]
  · -- `unifSpec` coin slot: `StateT.lift (query unifSpec qN)`.
    funext s
    simp [hybChallengeImpl, srHyb4Impl, StateT.lift, bind_pure]

/-- Spec re-association rerouting `D2SAlgo`'s ambient `oSpec + (srChallengeOracle … + auxSpec)` to
the **Option A** state-restoration grouping `(oSpec + srChallengeOracle …) + auxSpec` (coins appended
after the SR interface).  A pure *associator* of the 3-way oracle sum (`simulateQ` reroute) — no slot
is swapped, only regrouped — so it preserves the computation's distribution; the result is a
coin-bearing SR prover `Prover.StateRestoration.SoundnessWithCoins oSpec … auxSpec`. -/
def srReassocImpl :
    QueryImpl (oSpec + (srChallengeOracle (StmtIn × Salt) pSpec + ((Unit →ₒ U) + unifSpec)))
      (OracleComp ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + ((Unit →ₒ U) + unifSpec))) :=
  fun
  | .inl qO => liftM (query (spec := (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
      + ((Unit →ₒ U) + unifSpec)) (Sum.inl (Sum.inl qO)))
  | .inr (.inl qC) => liftM (query (spec := (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
      + ((Unit →ₒ U) + unifSpec)) (Sum.inl (Sum.inr qC)))
  | .inr (.inr qA) => liftM (query (spec := (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
      + ((Unit →ₒ U) + unifSpec)) (Sum.inr qA))

/-- **CO25 §6.1 — `Hyb₄ ≡ IP coin-SR experiment`** (the structural game-match).

`Hyb₄`'s compiled prover `D2SAlgo^f(𝒫̃)` lives over `oSpec + (fsChallengeOracle … + ((Unit →ₒ U) +
unifSpec))`. Since `fsChallengeOracle = srChallengeOracle`, it *is* a coin-bearing SR-soundness
prover (`SoundnessWithCoins …`, `auxSpec := (Unit →ₒ U) + unifSpec`), and `Hyb₄` *is* that prover's
coin-SR experiment under the canonical model: FS oracle eagerly sampled (`srInitDIP`), `oSpec`
answered by `srImplLift oSpecImpl`, coins by `d2sAuxImpl`.

The remaining content is purely **structural** — eager↔function model for the FS oracle, oracle-spec
reassociation, and prover-output / `deriveTranscript` matching — with **no coin derandomization**
(the coins are answered inside the experiment by `auxImpl`). Stated as a `probEvent` (`= evalDist`)
equality. Left as `sorry`.

Non-circular, unlike the earlier free-existential form: the right-hand side is the *specific*
`coinSRExperimentProb` game (its shape `srSoundnessGameWithCoins … >>= verifier.run` is fixed), so
no trivial witness `perAuxGame := Hyb₄` can satisfy it. -/
theorem hyb4_eq_coinSRExperiment
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [DecidableEq ι]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    ∃ inducedProver :
        Prover.StateRestoration.SoundnessWithCoins oSpec (StmtIn × Salt) pSpec
          ((Unit →ₒ U) + unifSpec),
      Pr[ dsfsSoundnessEvent langIn langOut |
          hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
            oSpecImpl V maliciousProver d2sAlgoTransform]
        = Verifier.StateRestoration.coinSRExperimentProb
            (init := srInitDIP) (impl := srImplLift oSpecImpl)
            d2sAuxImpl (langInSalted langIn) langOut (saltedIPVerifier (Salt := Salt) V)
            inducedProver := by
  classical
  -- The induced SR prover is `D2SAlgo^f(𝒫̃)`, made a *bare* OG state-restoration prover over the
  -- extended ambient `oSpec + ((Unit →ₒ U) + unifSpec)`:  de-abort with the same `default` as
  -- `basicFiatShamirGame` (`·.getD default`), reassociate the output `(𝕩,(τ̂,msgs)) ↦ ((𝕩,τ̂),msgs)`,
  -- then `srReassocImpl` regroups the oracle spec `oSpec+(chal+aux) → (oSpec+aux)+chal` so it is
  -- `Prover.StateRestoration.Soundness (oSpec + aux)` — i.e. `SoundnessWithCoins`, no separate notion.
  refine ⟨(simulateQ srReassocImpl
      ((fun o : Option (StmtIn × FSSaltedProof pSpec Salt) =>
          let p := o.getD default; ((p.1, p.2.1), p.2.2))
        <$> (d2sAlgoTransform maliciousProver).run) :
      Prover.StateRestoration.SoundnessWithCoins oSpec (StmtIn × Salt) pSpec
        ((Unit →ₒ U) + unifSpec)), ?_⟩
  -- Remaining: the value-marginal game-match `Pr[evt | Hyb₄] = coinSRExperimentProb …`.
  -- The pieces, in decreasing order of "done-ness":
  --  • handler:  PROVEN above — `hybChallengeImpl_eq_srAddLift` gives `hybChallengeImpl oSpecImpl
  --    𝒟_IP_salted = srHyb4Impl oSpecImpl`; the `srReassocImpl` regroup makes `srHyb4Impl` answer
  --    the OG handler `(impl.addLift auxImpl).addLift srChallengeQueryImpl'` slot-for-slot (the
  --    reroute collapses under `simulateQ_simulateQ`).
  --  • init:     `hybChallengeInit 𝒟_IP_salted = srInitDIP` — both `= 𝒟_IP_salted.sample`.
  --  • logging:  GENERIC, already in VCVio — `loggingOracle.fst_map_run_simulateQ` /
  --    `run_simulateQ_bind_fst` peel `basicFiatShamirGame`'s prover/verifier logs (the event
  --    ignores the `QueryLog` component, so the `(stmtIn, stmtOut)` marginal is unchanged).
  --  • verifier: `saltedIPVerifier V (𝕩,τ̂) = V 𝕩` (def); `basicFiatShamirGame`'s `V.verify …
  --    |>.getM` rejects iff the lifted `(saltedIPVerifier V).run` rejects ⇒ same event both sides.
  --  • prover:   both sides run `D2SAlgo^f(𝒫̃)` and, on failure, the *same* `default` (de-abort) —
  --    so the abort branches agree pointwise (this is why the de-abort keeps the match exact).
  --  • transcript (the deep DSFS step): under the (regrouped) handler, the on-sponge routing
  --    `simulateQ liftFSSaltedQueriesToD2SChallengePlusUnit (deriveTranscriptFS (𝕩,τ̂))` agrees
  --    with `liftComp (deriveTranscriptSR (𝕩,τ̂))` (both answer FS challenge queries via the
  --    pre-sampled `srChallengeQueryImpl'`; `deriveTranscriptFS = deriveTranscriptSR` by alias).
  --  • output:   reassoc `(𝕩,(τ̂,m)) ↦ ((𝕩,τ̂),m)` (`srReassocImpl` + the output map).
  sorry

/-- **CO25 §6.1 step L3 — `Hyb₄` is the IP's state-restoration soundness game.** False acceptance in
`Hyb₄` is bounded by the IP's SR-soundness error `ε_sr`.

`Hyb₄` runs `𝒱_std^f` with `f ← 𝒟_IP_salted` (uniform FS oracle) against the compiled prover
`D2SAlgo^f(𝒫̃)`. Because `fsChallengeOracle = srChallengeOracle`, this *is* the state-restoration
soundness experiment for `saltedIPVerifier V` under the canonical model `(srInitDIP, srImplLift
oSpecImpl)`: both sample a uniform challenge function, both have the prover **output `stmtIn`**, and
both derive the transcript from the (identical) FS/SR oracle. So `h_IP_SR_sound` bounds it
**directly** — no adaptive↔selective gap (SR soundness is adaptive by construction), hence Theorem
3.18 (the general FS→SR bridge) is *not* on this path.

Left as `sorry`; it rests on the two structural correspondences `Hyb₄ ≡ SR experiment`:

1. **Eager ↔ pre-sampled-function model**: `hybChallengeInit/Impl 𝒟_IP_salted` (eager) and
   `srInitDIP` + `srChallengeQueryImpl'` (pre-sampled function) induce the *same* distribution —
   `𝒟_IP_salted = OracleDistribution.uniform …`, whose `toImpl g = fun q => pure (g q)` coincides
   with `srChallengeQueryImpl'` applying the immutable sampled function `g`.

2. **Compiled-prover / verifier-run correspondence**: `d2sAlgoTransform maliciousProver` (over
   `oSpec + D2SChallengePlusUnitOracle …`, with auxiliary `Unit`/`unifSpec` sampling) maps to an
   SR-soundness prover over `oSpec + srChallengeOracle (StmtIn × Salt) pSpec` (marginalizing the
   auxiliary randomness), and `basicFiatShamirGame`'s `deriveTranscriptFS` + `V.verify` matches
   `srSoundnessGame` + `(saltedIPVerifier V).run`. -/
theorem hyb4_falseAccept_le_srSoundnessError
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [DecidableEq ι]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (ε_sr : ENNReal)
    -- IP SR-soundness *against coin-bearing provers* (`auxSpec := (Unit →ₒ U) + unifSpec`,
    -- coins sampled by `d2sAuxImpl`) — the honest hypothesis: `D2SAlgo^f(𝒫̃)` is such a prover.
    (h_IP_SR_sound : Verifier.StateRestoration.soundnessWithCoins
        (init := srInitDIP) (impl := srImplLift oSpecImpl)
        ((Unit →ₒ U) + unifSpec) d2sAuxImpl
        (langInSalted langIn) langOut (saltedIPVerifier (Salt := Salt) V) ε_sr) :
    Pr[ dsfsSoundnessEvent langIn langOut |
        hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          oSpecImpl V maliciousProver d2sAlgoTransform] ≤ ε_sr := by
  -- `Hyb₄` *is* the coin-SR experiment for the prover induced by `D2SAlgo^f(𝒫̃)` (game-match), and
  -- the coin-bearing SR-soundness hypothesis bounds that experiment directly — no derandomization.
  obtain ⟨inducedProver, hEq⟩ :=
    hyb4_eq_coinSRExperiment V oSpecImpl langIn langOut maliciousProver d2sAlgoTransform
  rw [hEq]
  exact h_IP_SR_sound inducedProver

/-- **Adaptive, query-bounded soundness of the DSFS scheme** (CO25 `ε_NARG`) — the named, faithful
DSFS-level soundness notion that `theorem_6_1_soundness` concludes.

DSFS analog of `Verifier.StateRestoration.soundnessWithCoins` (and why we do *not* reuse the library
`Verifier.soundness`):
- **Adaptive**: the malicious prover `𝒫̃` (a `MaliciousProver`, i.e. an `OracleComp`) *outputs* its
  statement `𝕩`, and the break event reads `𝕩 ∉ langIn ∧ stmtOut ∈ langOut` off that output — exactly
  CO25's `ε_NARG`.  The library `Verifier.soundness` is instead *selective* (`∀ stmtIn ∉ langIn`)
  over the interactive `Prover` *structure*, so it does not match this game.
- **Query-bounded**: we quantify only over provers within the Key-Lemma permutation/hash budget
  `(tₕ,tₚ,tₚᵢ)` — the bound is intrinsic (`η★` controls only bounded provers), the one extra
  hypothesis `Verifier.soundness` lacks.  (No separate *coin* axis is needed: a randomized `𝒫̃`'s
  coins already live inside the `∀ OracleComp` quantifier — coins were specific to the SR-level
  *compiled* prover `D2SAlgo^f`.)

The oracle model is the canonical DSFS one (`hyb0Init`, `hyb0Impl oSpecImpl`). -/
def dsfsSoundnessBounded
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    [DecidableEq ι]
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (tShared : oSpec.Domain → ℕ) (tₕ tₚ tₚᵢ : ℕ)
    (error : ENNReal) : Prop :=
  ∀ maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ,
    IsLemma5_1QueryBound maliciousProver tShared tₕ tₚ tₚᵢ →
    Pr[ dsfsRawEvent langIn langOut |
        dsfsGameDist hyb0Init (hyb0Impl oSpecImpl) V maliciousProver] ≤ error

/-- CO25 **Theorem 6.1** — soundness of the duplex-sponge Fiat–Shamir scheme.

For every malicious prover making at most `(tₕ, tₚ, tₚᵢ)` permutation/hash queries
(`IsLemma5_1QueryBound`), its DSFS false-acceptance probability `ε_NARG` is at most `ε_sr + η★`,
where `ε_sr` is the IP's state-restoration soundness error and `η★` is the Key-Lemma additive
error.

**Statement shape (per design decision)**: phrased over `MaliciousProver` with an explicit query
bound — `Verifier.soundness`'s unbounded `∀ prover` form is unprovable here, since `η★` only
controls query-bounded provers. The bound is on the *raw* DSFS game `dsfsGameDist`
(`= ε_NARG`); the existential trace map of `lemma_5_1` is consumed internally.

**The proof follows the paper's §6.1 derivation, but collapses L3+L4: since `Hyb₄` *is* the IP's
SR-soundness game (`fsChallengeOracle = srChallengeOracle`), it is bounded by `ε_IP^sr` directly —
no Theorem 3.18 (FS→SR) detour, no adaptive↔selective gap.**
```
ε_NARG                                                              -- raw DSFS game
  = Pr[𝒱^{h,p}(𝕩,π)=1 ∧ 𝕩∉ℒ | (h,p,p⁻¹)←𝒟_𝔖; (𝕩,π)←𝒫̃]         -- (L1) ε_NARG = Pr[Hyb₀]
  ≤ Pr[𝒱_std^f(𝕩,π)=1 ∧ 𝕩∉ℒ | f←𝒟_IP; (𝕩,π)←D2SAlgo^f(𝒫̃)] + η★  -- (L2, Thm 5.1)
  ≤ ε_IP^sr(δ⋆, θ⋆(tₕ,tₚ,tₚ⁻¹), n) + η★                             -- (L3, Hyb₄ ≡ IP SR game)
```
The connective steps — L1 (`dsfsGame_falseAccept_eq_hyb0`, **fully proven**), the L2
`tvDist`→probability transfer (`probEvent_le_probEvent_add_ofReal_tvDist`, **proven**), and the
additive arithmetic — are `sorry`-free; the open seams are `lemma_5_1` (Thm 5.1) and
`hyb4_falseAccept_le_srSoundnessError` (L3, `Hyb₄ ≡ SR experiment`). -/
theorem theorem_6_1_soundness
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [DecidableEq ι]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (tShared : oSpec.Domain → ℕ) (tₕ tₚ tₚᵢ : ℕ)
    (hTp : tₚ ≥ max pSpec.totalNumPermQueriesMessage pSpec.totalNumPermQueriesChallenge)
    (ε_sr : ENNReal)
    -- IP SR-soundness against coin-bearing provers (canonical model `Hyb_4` uses: FS oracle sampled
    -- uniformly by `srInitDIP`, `oSpec` by `oSpecImpl`, the `D2SAlgo` coins by `d2sAuxImpl`).
    (h_IP_SR_sound : Verifier.StateRestoration.soundnessWithCoins
        (init := srInitDIP) (impl := srImplLift oSpecImpl)
        ((Unit →ₒ U) + unifSpec) d2sAuxImpl
        (langInSalted langIn) langOut (saltedIPVerifier (Salt := Salt) V) ε_sr) :
      -- ε_NARG(λ, (tₕ,tₚ,tₚ⁻¹), n) — now packaged as the named DSFS soundness notion:
      dsfsSoundnessBounded (U := U) (δ := δ) oSpecImpl V langIn langOut tShared tₕ tₚ tₚᵢ
        (ε_sr + ENNReal.ofReal
          (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries codec.decodingBias)) := by
  intro maliciousProver hBound
  -- Seam #1 (Theorem 5.1 / Key Lemma): the D2SAlgo prover transform, the D2STrace map, and the
  -- bound `tvDist (Hyb₀, Hyb₄) ≤ η★` for this query-bounded prover.
  obtain ⟨d2sAlgoTransform, d2sTraceTransform, hKey⟩ :=
    lemma_5_1 (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
      oSpecImpl V tShared tₕ tₚ tₚᵢ hTp
  have hTv := (hKey maliciousProver hBound).1
  -- L3 (Hyb₄ ≡ IP SR game): false acceptance in Hyb₄ ≤ the IP SR-soundness error ε_sr, directly.
  -- No Theorem 3.18 needed — Hyb₄ IS the SR game (fsChallengeOracle = srChallengeOracle, adaptive).
  have hL3 := hyb4_falseAccept_le_srSoundnessError V oSpecImpl langIn langOut
    maliciousProver d2sAlgoTransform ε_sr h_IP_SR_sound
  -- §6.1 derivation (open seams: `lemma_5_1` at L2, `hyb4_falseAccept_le_srSoundnessError` at L3):
  --   ε_NARG = Pr[ |𝕩|≤n ∧ 𝕩∉ℒ(ℛ) ∧ 𝒱^{h,p}(𝕩,π)=1 | (h,p,p⁻¹)←𝒟_𝔖; (𝕩,π)←𝒫̃^{h,p,p⁻¹} ]
  --     = Pr[ ... | Hyb₀ ]                                   -- (L1) trace map preserves acceptance
  --     ≤ Pr[ 𝒱_std^f(𝕩,π)=1 ∧ 𝕩∉ℒ | f←𝒟_IP; (𝕩,π)←D2SAlgo^f(𝒫̃) ] + η★   -- (L2, Thm 5.1)
  --     ≤ ε_IP^sr(δ⋆, θ⋆(tₕ,tₚ,tₚ⁻¹), n) + η★                 -- (L3, Hyb₄ ≡ IP SR game; direct)
  calc Pr[ dsfsRawEvent langIn langOut |
        dsfsGameDist hyb0Init (hyb0Impl oSpecImpl) V maliciousProver]
      = Pr[ dsfsSoundnessEvent langIn langOut |
          hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
            oSpecImpl V maliciousProver d2sTraceTransform] :=
        dsfsGame_falseAccept_eq_hyb0 V oSpecImpl langIn langOut maliciousProver
          d2sTraceTransform
    _ ≤ Pr[ dsfsSoundnessEvent langIn langOut |
          hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
            oSpecImpl V maliciousProver d2sAlgoTransform]
          + ENNReal.ofReal
              (tvDist
                (hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
                  (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
                  oSpecImpl V maliciousProver d2sTraceTransform)
                (hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
                  (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
                  oSpecImpl V maliciousProver d2sAlgoTransform)) :=
        probEvent_le_probEvent_add_ofReal_tvDist _ _ _
    _ ≤ Pr[ dsfsSoundnessEvent langIn langOut |
          hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
            oSpecImpl V maliciousProver d2sAlgoTransform]
          + ENNReal.ofReal (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries codec.decodingBias) :=
        add_le_add (le_refl _) (ENNReal.ofReal_le_ofReal hTv)
        -- (L3, Hyb₄ ≡ IP SR game) ≤ ε_IP^sr(δ⋆, θ⋆, n) + η★ — directly from SR soundness.
    _ ≤ ε_sr + ENNReal.ofReal (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries codec.decodingBias) :=
        add_le_add hL3 (le_refl _)
  -- (E, by CO25 Eq. 5) Unfolding `ηStar tₕ tₚ tₚ⁻¹` and using `tₕ + tₚ + tₚ⁻¹ ≤ t`, this bound is:
  --   ε_NARG(λ, (tₕ,tₚ,tₚ⁻¹), n)
  --     ≤ ε_IP^sr(δ⋆, θ⋆(t), n)
  --       + (7(tₕ+tₚ+tₚ⁻¹)² + 28(L+1)(tₕ+tₚ+tₚ⁻¹) + 14(L+1)² − 3(tₕ+tₚ+tₚ⁻¹) − 13(L+1)) / (2·|Σ|^c)
  --       + θ⋆·maxᵢ ε_cdc,ᵢ + Σᵢ ε_cdc,ᵢ
  --     ≤ ε_IP^sr(δ⋆, θ⋆(t), n) + 25t²/|Σ|^c + t·maxᵢ ε_cdc,ᵢ + Σᵢ ε_cdc,ᵢ
  --     = ε_IP^sr(δ⋆, θ⋆(t), n) + η★(λ, t).
  -- We keep `ηStar tₕ tₚ tₚ⁻¹` in the un-simplified form above (the same quantity).

/-! ## Theorem 6.2: IP SR-KS → DSFS straightline KS

Bespoke, query-bounded form mirroring `theorem_6_1_soundness`.  (An earlier attempt phrased the
conclusion in the *generic* `Verifier.knowledgeSoundness` and routed through the FS-lifting
`theorem_3_19_straightline_ks`; that notion is selective + **unbounded**, so it cannot carry the
query-bounded `η★` term — see `dsfsKnowledgeSoundnessBounded` for the faithful adaptive notion.) -/

/-- The **extraction-failure event** for the DSFS straightline-KS game, on the game's
`(stmtIn, extracted-witness?)` output: the verifier accepted but the extracted witness misses
`relIn` — or extraction produced no witness at all (still a failure). `none` (verifier rejected) is
not a knowledge break.  CO25 §6.2: `(𝕩, 𝕨) ∉ ℛ ∧ b = 1`. -/
def ksFailEvent (relIn : Set (StmtIn × WitIn)) :
    Option (StmtIn × Option WitIn) → Prop
  | some (stmtIn, some witIn) => (stmtIn, witIn) ∉ relIn
  | some (_, none) => True
  | none => False

/-- The DSFS **straightline knowledge-soundness game** (bespoke, query-bounded): run the malicious
prover `𝒫̃` and the DSFS verifier (the §5.8 `dsfsGame`), then run the straightline extractor
`dsfsExtractor` (Construction 6.3) on the proof + combined query log — all under the *same* eager
oracle handler `hyb0Impl oSpecImpl` so the extractor sees the prover's actual trace — and return the
`(stmtIn, extracted-witness?)` pair. `none` = verifier rejected (`b = 0`). -/
def dsfsKSGameDist [Inhabited WitOut]
    (dsfsExtractor : Extractor.Straightline (oSpec + duplexSpongeChallengeOracle StmtIn U)
      StmtIn WitIn WitOut ⟨!v[.P_to_V], !v[DSSaltedProof (pSpec := pSpec) (U := U) δ]⟩)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (Option (StmtIn × Option WitIn)) := do
  (simulateQ (hyb0Impl oSpecImpl) (do
    let out? ← (dsfsGame V maliciousProver).run
    match out? with
    | none => pure none
    | some ⟨stmtIn, _stmtOut, proof, log⟩ =>
        -- The non-interactive transcript is the single P→V message (the DSFS proof).
        let witIn? ← (dsfsExtractor stmtIn default
          (Fin.cons proof (fun i => i.elim0) :
            FullTranscript ⟨!v[.P_to_V], !v[DSSaltedProof (pSpec := pSpec) (U := U) δ]⟩)
          log []).run
        pure (some (stmtIn, witIn?)))).run' (← hyb0Init)

/-- **Adaptive, query-bounded straightline knowledge soundness of the DSFS scheme** — the named,
faithful DSFS-level KS notion that `theorem_6_2_straightline` concludes; the KS analog of
`dsfsSoundnessBounded`.

There exists a straightline extractor (Construction 6.3) such that, for every malicious prover within
the Key-Lemma query budget `(tₕ,tₚ,tₚᵢ)`, the DSFS straightline-KS extraction-failure probability is
bounded by `error`.  As with `dsfsSoundnessBounded`, this is *adaptive* (`𝒫̃` outputs `𝕩`) and
*query-bounded* — so it is **not** a coin-variant of the library `Verifier.knowledgeSoundness` (which
is unbounded and runs the interactive `Prover` structure on a fixed `stmtIn`). -/
def dsfsKnowledgeSoundnessBounded [Inhabited WitOut]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    [DecidableEq ι]
    (relIn : Set (StmtIn × WitIn))
    (tShared : oSpec.Domain → ℕ) (tₕ tₚ tₚᵢ : ℕ)
    (error : ENNReal) : Prop :=
  ∃ dsfsExtractor : Extractor.Straightline (oSpec + duplexSpongeChallengeOracle StmtIn U)
      StmtIn WitIn WitOut ⟨!v[.P_to_V], !v[DSSaltedProof (pSpec := pSpec) (U := U) δ]⟩,
  ∀ maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ,
    IsLemma5_1QueryBound maliciousProver tShared tₕ tₚ tₚᵢ →
    Pr[ ksFailEvent relIn |
        dsfsKSGameDist dsfsExtractor oSpecImpl V maliciousProver ] ≤ error

/-- **CO25 §6.2 game-match (the open structural seam).**  The DSFS straightline-KS game factors
through a common extractor kernel `k` (run `E_IP` on the basic-FS game output), as two probability
equalities:

* **`hL1` — the `Hyb₀` step.**  The DSFS KS game equals `Hyb₀ >>= k`.  KS analog of the *proven*
  soundness lemma `dsfsGame_falseAccept_eq_hyb0` (the §5.8 `D2STrace` line-4 map preserves the
  read-out), now with the extractor kernel threaded through.

* **`hL3` — the `Hyb₄` problem.**  `Hyb₄ >>= k` *is* the IP coin-SR-KS experiment for an induced
  prover.  This is the **KS twin of `hyb4_eq_coinSRExperiment`** — the deep eager↔presampled-function
  / `deriveTranscript` / prover-de-abort game-equivalence "Hyb₄ is the SR experiment", **shared in
  substance with §6.1** (whose soundness version `hyb4_eq_coinSRExperiment` is the analogous seam).

`theorem_6_2_straightline` closes around this purely by *proven* bridges — `B3`, data-processing
(`tvDist_bind_right_le`, valid for the shared kernel `k`), and `lemma_5_1`'s `tvDist ≤ η★`.  So this
lemma (together with the cited `lemma_5_1`) is the *only* §6.2 open seam.  Left `sorry`. -/
theorem dsfsKSGame_hybFactorization
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [DecidableEq ι] [Inhabited WitOut]
    (E_IP : Extractor.StateRestoration oSpec (StmtIn × Salt) WitIn WitOut pSpec)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sTraceTransform : D2STraceTransform (Salt := Salt) (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (duplexSpongeChallengeOracle StmtIn U))
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    ∃ (k : Option (BasicFiatShamirGameOutput (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (Salt := Salt)) →
          ProbComp (Option (StmtIn × Option WitIn)))
      (inducedProver : Prover.StateRestoration.KnowledgeSoundnessWithCoins
          oSpec (StmtIn × Salt) WitOut pSpec ((Unit →ₒ U) + unifSpec)),
      -- `hL1` — Hyb₀ step (KS analog of `dsfsGame_falseAccept_eq_hyb0`):
      Pr[ ksFailEvent relIn |
          dsfsKSGameDist (dsfsStraightlineExtractor E_IP) oSpecImpl V maliciousProver ]
        = Pr[ ksFailEvent relIn |
            hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
              (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
              oSpecImpl V maliciousProver d2sTraceTransform >>= k ] ∧
      -- `hL3` — the Hyb₄ problem (KS twin of `hyb4_eq_coinSRExperiment`):
      Pr[ ksFailEvent relIn |
          hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
            oSpecImpl V maliciousProver d2sAlgoTransform >>= k ]
        = Verifier.StateRestoration.coinKSExperimentProb
            (init := srInitDIP) (impl := srImplLift oSpecImpl) d2sAuxImpl E_IP
            (relInSalted relIn) relOut (saltedIPVerifier (Salt := Salt) V) inducedProver := by
  sorry

/-- CO25 **Theorem 6.2 (straightline knowledge soundness)** — bespoke, query-bounded form.

For every malicious prover making at most `(tₕ, tₚ, tₚᵢ)` permutation/hash queries, the DSFS
straightline-KS extraction-failure probability is at most `ε_sr + η★`, where `ε_sr` is the IP's
straightline state-restoration KS error and `η★` is the Key-Lemma additive error.  The extractor
witness is **Construction 6.3** (`dsfsStraightlineExtractor E_IP`): apply `D2STrace` to the DSFS
query log, then the IP SR extractor `E_IP`.

**Shape (per design, as for `theorem_6_1_soundness`)**: phrased over `MaliciousProver` with an
explicit query bound — the unbounded `Verifier.knowledgeSoundness` form is unprovable here (`η★` only
controls query-bounded provers).  Hypothesis is the *coin-bearing* SR-KS notion
`knowledgeSoundnessWithCoins` (the KS analog of `theorem_6_1`'s `soundnessWithCoins`): the compiled
prover `D2SAlgo^f(𝒫̃)` has private coins, answered by `d2sAuxImpl`; `E_IP` itself is straightline over
base `oSpec`.

**Proof flow (mirrors §6.1; every `≤` bridge is proven).**  Factoring both `Hyb₀` and `Hyb₄`
through a *common* extractor kernel `k` (run `E_IP` on the FS game output):
```
ε_NARG^ks = Pr[ksFail | DSFS KS game w/ Construction 6.3]
  = Pr[ksFail | Hyb₀ >>= k]                        -- (L1) game-match equality   [seam]
  ≤ Pr[ksFail | Hyb₄ >>= k] + tvDist(Hyb₀>>=k, …)  -- B3                          ✓
  ≤ Pr[ksFail | Hyb₄ >>= k] + tvDist(Hyb₀, Hyb₄)   -- data-processing      ✓ tvDist_bind_right_le
  ≤ Pr[ksFail | Hyb₄ >>= k] + η★                   -- Key Lemma                  ✓ lemma_5_1 (hTv)
  = coinKSExperimentProb(inducedProver) + η★        -- (L3) game-match equality   [seam]
  ≤ ε_sr + η★                                      -- SR-KS hypothesis           ✓ hE_IP
```
The data-processing step is the §6.2-specific workhorse: applying the *same* kernel `k` to both
hybrids can only *decrease* `tvDist` (`tvDist_bind_right_le`), so `lemma_5_1`'s `tvDist(Hyb₀,Hyb₄) ≤
η★` transports verbatim.  The **only** remaining `sorry` is the bundled game-match *equality* (`∃ k
inducedProver, L1 ∧ L3` — the KS analog of `hyb4_eq_coinSRExperiment`, the deep "Hyb is the SR game"
fact, still open for §6.1 too); plus `lemma_5_1` itself (Thm 5.1, cited). -/
theorem theorem_6_2_straightline
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [DecidableEq ι] [Inhabited WitOut]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (tShared : oSpec.Domain → ℕ) (tₕ tₚ tₚᵢ : ℕ)
    (hTp : tₚ ≥ max pSpec.totalNumPermQueriesMessage pSpec.totalNumPermQueriesChallenge)
    (ε_sr : ENNReal)
    (h_IP_SR_KS : Verifier.StateRestoration.knowledgeSoundnessWithCoins
        (init := srInitDIP) (impl := srImplLift oSpecImpl)
        ((Unit →ₒ U) + unifSpec) d2sAuxImpl
        (relInSalted relIn) relOut (saltedIPVerifier (Salt := Salt) V) ε_sr) :
    -- Packaged as the named DSFS straightline-KS notion (KS analog of `dsfsSoundnessBounded`):
    dsfsKnowledgeSoundnessBounded (U := U) (δ := δ) (WitOut := WitOut) oSpecImpl V relIn
      tShared tₕ tₚ tₚᵢ
      (ε_sr + ENNReal.ofReal
        (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries codec.decodingBias)) := by
  -- Extractor witness: Construction 6.3 over the IP SR-KS extractor `E_IP` (base `oSpec`).
  obtain ⟨E_IP, hE_IP⟩ := h_IP_SR_KS
  refine ⟨dsfsStraightlineExtractor E_IP, fun maliciousProver hBound => ?_⟩
  -- **Seam #1 (Key Lemma 5.1).** Prover/trace transforms + `tvDist(Hyb₀, Hyb₄) ≤ η★`.
  obtain ⟨d2sAlgoTransform, d2sTraceTransform, hKey⟩ :=
    lemma_5_1 (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
      oSpecImpl V tShared tₕ tₚ tₚᵢ hTp
  have hTv := (hKey maliciousProver hBound).1
  -- **Seam #2 (the §6.2 game-match) — now the named lemma `dsfsKSGame_hybFactorization`.**
  -- It supplies the common extractor kernel `k`, the induced prover, and the two equalities
  -- `hL1` (Hyb₀ step) ∧ `hL3` (the Hyb₄ problem = KS twin of `hyb4_eq_coinSRExperiment`).
  obtain ⟨k, inducedProver, hL1, hL3⟩ :=
    dsfsKSGame_hybFactorization E_IP V oSpecImpl relIn relOut maliciousProver
      d2sTraceTransform d2sAlgoTransform
  set H0 := hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      oSpecImpl V maliciousProver d2sTraceTransform with hH0
  set H4 := hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      oSpecImpl V maliciousProver d2sAlgoTransform with hH4
  -- All `≤` bridges below are **proven**: L1 (`hL1`), B3, data-processing (`tvDist_bind_right_le`),
  -- the Key-Lemma bound (`hTv`), the game-match (`hL3`), and the SR-KS hypothesis (`hE_IP`).
  calc Pr[ ksFailEvent relIn |
          dsfsKSGameDist (dsfsStraightlineExtractor E_IP) oSpecImpl V maliciousProver ]
      = Pr[ ksFailEvent relIn | H0 >>= k ] := hL1
    _ ≤ Pr[ ksFailEvent relIn | H4 >>= k ] + ENNReal.ofReal (tvDist (H0 >>= k) (H4 >>= k)) :=
        probEvent_le_probEvent_add_ofReal_tvDist _ _ _
    _ ≤ Pr[ ksFailEvent relIn | H4 >>= k ] + ENNReal.ofReal (tvDist H0 H4) :=
        add_le_add (le_refl _) (ENNReal.ofReal_le_ofReal (tvDist_bind_right_le k H0 H4))
    _ ≤ Pr[ ksFailEvent relIn | H4 >>= k ]
          + ENNReal.ofReal (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries codec.decodingBias) :=
        add_le_add (le_refl _) (ENNReal.ofReal_le_ofReal hTv)
    _ = Verifier.StateRestoration.coinKSExperimentProb
            (init := srInitDIP) (impl := srImplLift oSpecImpl) d2sAuxImpl E_IP
            (relInSalted relIn) relOut (saltedIPVerifier (Salt := Salt) V) inducedProver
          + ENNReal.ofReal (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries codec.decodingBias) := by
        rw [hL3]
    _ ≤ ε_sr + ENNReal.ofReal
            (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries codec.decodingBias) :=
        add_le_add (hE_IP inducedProver) (le_refl _)

end

end DuplexSpongeFS
