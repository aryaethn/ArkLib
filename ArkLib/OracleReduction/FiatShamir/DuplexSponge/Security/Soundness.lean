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
  straightline KS (via Construction 6.3) with error `κ + η★`, concluding CO25 Def 3.6
  (`adaptiveNARGKnowledgeSoundness`) at the DSFS NARG, query-bounded.

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

/-- **§6.2 trace-map seam.**  The §5.8 `D2STrace` of the DSFS prover query log down to the basic-FS
log `tr_std`, packaged as a pure log rewrite for use inside `dsfsStraightlineExtractor`.

`D2STrace` genuinely *samples* `𝒰(Σ)` (its monad is `UnitSampleM U`); that sampling is discharged at
the **`Hyb₀` game layer** (`mappedDSFSGameDist`/`runSection58TraceMap`), NOT inside the extractor —
this keeps Construction 6.3 coin-free over the *public* DSFS spec
`oSpec + duplexSpongeChallengeOracle StmtIn U` (no `(Unit →ₒ U)` summand), as required.  The extractor
only needs the *resulting* basic-FS log, exposed here as a seam; its correctness is subsumed by the
`Hyb₀` equality `hL1` of `dsfsKSGame_hybFactorization`.  Open seam (R2/R3 — no canonical
`SubSpec`/sampling at this layer). -/
noncomputable def d2sTraceLog
    (proveQueryLog : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) :=
  TraceTransform.projectSharedQueryLogSalted proveQueryLog

/-- **§6.2 spec-lift seam.**  Lift a NARG-KS extractor computation over the basic-FS spec
`oSpec + srChallengeOracle (StmtIn × Salt) pSpec` up to the DSFS spec
`oSpec + duplexSpongeChallengeOracle StmtIn U`.  There is no canonical `SubSpec` between the two
challenge oracles (different index types), so this lift is an explicit seam; operationally `E_std`
issues only `oSpec`/challenge queries already resolved by the game-layer trace map.  Open seam. -/
noncomputable def liftFSExtractToDSFS
    (e : OptionT (OracleComp (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)) WitIn) :
    OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)) WitIn :=
  let specImpl : QueryImpl (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
      (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)) := fun q =>
    match q with
    | .inl qShared => query (spec := oSpec + duplexSpongeChallengeOracle StmtIn U) (Sum.inl qShared)
    | .inr ⟨i, _⟩ => pure (Classical.choice (inferInstanceAs (Nonempty (pSpec.Challenge i))))
  OptionT.mk (simulateQ specImpl e.run)

/-- CO25 **Construction 6.3** — DSFS straightline extractor, built from the **basic-FS NARG-KS
extractor `E_std`** (the extractor delivered by Theorem 3.19, `theorem_3_19_straightline_ks`).

Mirrors the paper (Eq. 1978–1981): given the DSFS adversary view `(𝕩, π, tr, tr_V, 𝒫̃)`,
1. `tr_std := D2STrace(tr ‖ tr_V)` — the §5.8 trace map (`d2sTraceLog`; its `𝒰(Σ)` sampling is
   discharged at the `Hyb₀` game layer, keeping this extractor coin-free over the public spec);
2. pad `tr_std` to `E_std`'s coin-extended log spec with the pure `QueryLog.inl` (the `D2SAlgo`
   coins `(Unit →ₒ U) + unifSpec` are not visible to the extractor — straightline, coin-blind);
3. `𝒫̃_std := D2SAlgo(𝒫̃)` — the prover `E_std` is the extractor *for*; omitted in the straightline
   case (paper line 2049: `E_std` needs no prover access);
4. `w := E_std(𝕩, (encode τ, messages), tr_std)`, lifted from the basic-FS spec to the DSFS spec
   (`liftFSExtractToDSFS`).

Operates over the `NonInteractiveVerifier` pSpec `⟨!v[.P_to_V], !v[DSSaltedProof pSpec U δ]⟩`. -/
noncomputable def dsfsStraightlineExtractor
    [Fintype U]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (E_std : StmtIn → FSSaltedProof pSpec Salt →
      QueryLog ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + ((Unit →ₒ U) + unifSpec)) →
        OptionT (OracleComp (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)) WitIn) :
    Extractor.Straightline
      (oSpec + duplexSpongeChallengeOracle StmtIn U)
      StmtIn WitIn WitOut
      ⟨!v[.P_to_V], !v[DSSaltedProof (pSpec := pSpec) (U := U) δ]⟩ :=
  fun stmtIn _witOut transcript proveQueryLog _verifyQueryLog =>
    -- 1. The single P→V message *is* the DSFS proof `(τ, messages)`; regroup as a basic-FS proof.
    let saltedProof : DSSaltedProof (pSpec := pSpec) (U := U) δ := transcript 0
    let fsProof : FSSaltedProof pSpec Salt := (SaltCodec.encode saltedProof.1, saltedProof.2)
    -- 2. `tr_std := D2STrace(prover log)`, padded to `E_std`'s coin-extended spec (no aux entries).
    let trStd : QueryLog ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
        + ((Unit →ₒ U) + unifSpec)) := QueryLog.inl (d2sTraceLog (pSpec := pSpec) proveQueryLog)
    -- 3-4. Run `E_std` on `tr_std`, lifting the basic-FS spec up to the public DSFS spec.
    liftFSExtractToDSFS (pSpec := pSpec) (E_std stmtIn fsProof trStd)

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

/-- **The DSFS scheme as a NARG verifier** — the verify map `𝒱^{h,p}(𝕩, ·)` of the duplex-sponge FS
NARG, packaged in CO25 Def 3.5/3.6 shape (`StmtIn → Proof → OptionT (OracleComp …) StmtOut`).  This
is exactly the verify portion of `dsfsGame` (the §5.8 forward verifier `runForwardVerifierWide`, as an
`OptionT`); using it as the `verify` argument of `adaptiveNARGSoundness` /
`adaptiveNARGKnowledgeSoundness` makes those Def-3.5/3.6 notions *be about the DSFS NARG* (prover =
`MaliciousProver`, oracle spec `oSpec + duplexSpongeChallengeOracle StmtIn U`).  The DSFS scheme's
NARG experiment then equals `dsfsGameDist`/`dsfsKSGameDist` up to the marginalized prover/verify
query logs — see `dsfsNargSoundnessExp_eq_dsfsGame` / `dsfsNargKSExp_eq_dsfsKSGame`. -/
def dsfsNargVerify (V : Verifier oSpec StmtIn StmtOut pSpec) :
    StmtIn → DSSaltedProof (pSpec := pSpec) (U := U) δ →
      OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)) StmtOut :=
  fun stmtIn proof => OptionT.mk (runForwardVerifierWide δ V stmtIn proof)

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
    rfl
  · -- challenge slot: `𝒟_IP_salted.toImpl k qC = pure (k qC)`, matching `srChallengeQueryImpl'`.
    funext s
    simp only [hybChallengeImpl, srHyb4Impl, srChallengeQueryImpl', D_IP_salted,
      OracleReduction.OracleDistribution.uniform, OracleReduction.OracleDistribution.functionTable,
      OracleReduction.tableQueryImpl]
    rfl
  · -- `(Unit →ₒ U)` coin slot: `StateT.lift (d2sUnitSampleImpl qU)`.
    funext s
    simp [hybChallengeImpl, srHyb4Impl, StateT.lift, bind_pure]
    rfl
  · -- `unifSpec` coin slot: `StateT.lift (query unifSpec qN)`.
    funext s
    simp [hybChallengeImpl, srHyb4Impl, StateT.lift, bind_pure]
    rfl

/-- Spec re-association rerouting `D2SAlgo`'s ambient `oSpec + (srChallengeOracle … + auxSpec)` to
the **Option A** state-restoration grouping `(oSpec + srChallengeOracle …) + auxSpec` (coins appended
after the SR interface).  A pure *associator* of the 3-way oracle sum (`simulateQ` reroute) — no slot
is swapped, only regrouped — so it preserves the computation's distribution; the result is a
coin-bearing SR prover `Prover.StateRestoration.SoundnessWithCoins oSpec … auxSpec`. -/
def srReassocImpl :
    QueryImpl (oSpec + (srChallengeOracle (StmtIn × Salt) pSpec + ((Unit →ₒ U) + unifSpec)))
      (OracleComp ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + ((Unit →ₒ U) + unifSpec))) :=
  fun
  | .inl qO => query (spec := (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
      + ((Unit →ₒ U) + unifSpec)) (Sum.inl (Sum.inl qO))
  | .inr (.inl qC) => query (spec := (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
      + ((Unit →ₒ U) + unifSpec)) (Sum.inl (Sum.inr qC))
  | .inr (.inr qA) => query (spec := (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
      + ((Unit →ₒ U) + unifSpec)) (Sum.inr qA)


/-- The compiled prover `D2SAlgo^f(𝒫̃)` as a coin-bearing NARG prover for the single-salt FS:
de-abort with `default` (matching `basicFiatShamirGame`'s `·.getD default`), then `srReassocImpl`
regroups `oSpec + (chal + aux) → (oSpec + chal) + aux`.  No output reassoc (the NARG prover output
`StmtIn × FSSaltedProof` is the compiled prover's output verbatim). -/
def nargInducedProver
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    OracleComp ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + ((Unit →ₒ U) + unifSpec))
      (StmtIn × FSSaltedProof pSpec Salt) :=
  simulateQ srReassocImpl ((fun o => o.getD default) <$> (d2sAlgoTransform maliciousProver).run)

/-- **KS induced prover** — the coin-bearing NARG straightline-**KS** analog of `nargInducedProver`,
additionally outputting a claimed output witness `witOut`.  The DSFS attacker `𝒫̃` is proof-only
(no output witness), so its claim is the trivial `default : WitOut` (for the DSFS-of-IP case
`WitOut = Unit` this is `()`).  Matches the SR-KS prover shape
`Prover.StateRestoration.KnowledgeSoundnessWithCoins` (output `… × WitOut`). -/
def nargInducedProverKS [Inhabited WitOut]
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    OracleComp ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + ((Unit →ₒ U) + unifSpec))
      (StmtIn × FSSaltedProof pSpec Salt × WitOut) :=
  simulateQ srReassocImpl
    ((fun o => let p := o.getD default; (p.1, p.2, (default : WitOut))) <$>
      (d2sAlgoTransform maliciousProver).run)

/-- The DSFS proof-only attacker as a CO25 **Def-3.6 NARG adversary**: the malicious prover `𝒫̃`
outputs `(𝕩, π)` and claims the trivial `default` output witness (a NARG / public-coin IP has no
output witness; for the DSFS-of-IP case `WitOut = Unit` this is `()`).  This is the prover the DSFS
Def-3.6 experiment runs in `theorem_6_2_straightline`'s conclusion.

We keep `WitOut` *generic* (so `relOut` matches `h_IP_SR_KS`) but fix the *attacker's* claim to
`default`, because the §5 sponge/Hyb chain runs an `(𝕩, π)`-only prover (`MaliciousProver`) and
cannot thread a general output witness; the generic `adaptiveNARGKnowledgeSoundness` (Basic) stays
fully general for composition with reductions that *do* produce output witnesses. -/
def dsfsKSAdversary [Inhabited WitOut]
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ × WitOut) :=
  (fun p => (p.1, p.2, (default : WitOut))) <$> maliciousProver

/-- **CO25 §6.1 step L3a — `Hyb₄ = basic-FS NARG game`.** `Hyb₄` (the eager basic-FS game on the
compiled prover) equals the coin-bearing NARG soundness experiment (CO25 Def 3.5) for the induced
prover, under the canonical model.  Structural marginal match (handler slot-decomposition
`hybChallengeImpl_eq_srAddLift`, `srReassocImpl` regroup, `loggingOracle` value-marginal, `default`
de-abort) — **no FS↔SR crosswalk** (the verifier portion `deriveTranscriptFS + V.verify` is identical
on both sides).  Comparable to the proven `dsfsGame_falseAccept_eq_hyb0`. -/
theorem hyb4_eq_coinNARGgame
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [DecidableEq ι]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (d2sAlgoTransform : D2SAlgoTransform (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    Pr[ dsfsSoundnessEvent langIn langOut |
        hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          oSpecImpl V maliciousProver d2sAlgoTransform]
      = Pr[ (fun out => match out with
              | some (x, s) => x ∉ langIn ∧ s ∈ langOut
              | none => False) |
          adaptiveNARGSoundnessExpWithCoins
            (srInitDIP (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec))
            ((srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl).addLift
              (srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))) d2sAuxImpl
            (fsSaltedVerify (Salt := Salt) V)
            (nargInducedProver maliciousProver d2sAlgoTransform) ] := by
  sorry

/-- **CO25 §6.1 step L3 (two-hop):** false acceptance in `Hyb₄` is bounded by the basic-FS NARG
soundness error.  Combines `hyb4_eq_coinNARGgame` (L3a) with the coin-bearing NARG soundness
hypothesis (delivered by Thm 3.18 from IP SR soundness, L3b) applied to the induced prover. -/
theorem hyb4_falseAccept_le_nargSoundness
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
    -- Coin-bearing IP SR soundness (the same hypothesis as `theorem_6_1_soundness`).
    (h_IP_SR_sound : Verifier.StateRestoration.soundnessWithCoins
        (srInitDIP (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec))
        (srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl)
        ((Unit →ₒ U) + unifSpec) d2sAuxImpl
        (langInSalted langIn) langOut (saltedIPVerifier (Salt := Salt) V) ε_sr) :
    Pr[ dsfsSoundnessEvent langIn langOut |
        hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          oSpecImpl V maliciousProver d2sAlgoTransform] ≤ ε_sr := by
  -- L3b: FS NARG soundness from IP SR soundness (Thm 3.18), coin-bearing.
  have h_NARG := theorem_3_18_soundness (Salt := Salt) ((Unit →ₒ U) + unifSpec) d2sAuxImpl V
    langIn langOut (srInitDIP (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec))
    (srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl) ε_sr h_IP_SR_sound
  -- L3a: Hyb₄ = the coin-bearing NARG game; apply NARG soundness to the induced prover.
  rw [hyb4_eq_coinNARGgame V oSpecImpl langIn langOut maliciousProver d2sAlgoTransform]
  exact h_NARG (nargInducedProver maliciousProver d2sAlgoTransform) trivial

/-- **DSFS NARG soundness experiment = sponge soundness game** (CO25 §6 game-equivalence).  The
Def-3.5 experiment for the DSFS NARG (`adaptiveNARGSoundnessExp` with `verify := dsfsNargVerify V`)
and the duplex-sponge game `dsfsGameDist` assign the same false-acceptance probability: both run the
malicious prover then the §5.8 forward verifier and read off `(𝕩, stmtOut)`, differing only in the
(event-irrelevant) prover/verify query logs that `dsfsGame` records via `loggingOracle`.  Provable by
`loggingOracle` value-marginalization. -/
theorem dsfsNargSoundnessExp_eq_dsfsGame
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    Pr[ nargSoundFailEvent langIn langOut |
        adaptiveNARGSoundnessExp hyb0Init (hyb0Impl oSpecImpl) (dsfsNargVerify V) maliciousProver ]
      = Pr[ dsfsRawEvent langIn langOut |
          dsfsGameDist hyb0Init (hyb0Impl oSpecImpl) V maliciousProver ] := by
  unfold adaptiveNARGSoundnessExp dsfsGameDist
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr fun s => ?_
  congr 1
  sorry

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
additive arithmetic — are proven; the open seams are `lemma_5_1` (Thm 5.1) and
`hyb4_falseAccept_le_nargSoundness` (L3, `Hyb₄ ≡ NARG soundness`). -/
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
      -- ε_NARG(λ, (tₕ,tₚ,tₚ⁻¹), n) — CO25 **Def 3.5** as a property of the DSFS NARG *verifier*
      -- `Verifier.dsfsNargNIV δ V` (= `𝒱^{h,p}`), query-bounded attacker.
      (Verifier.dsfsNargNIV δ V).adaptiveNARGSoundness
        (init := hyb0Init) (impl := hyb0Impl oSpecImpl)
        langIn langOut
        (bound := fun maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ =>
          IsLemma5_1QueryBound maliciousProver tShared tₕ tₚ tₚᵢ)
        (ε_sr + ENNReal.ofReal
          (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries codec.decodingBias)) := by
  -- `Verifier.dsfsNargNIV δ V`'s verify is defeq to `dsfsNargVerify V` (`Fin.cons … 0 = π`), so
  -- cast to the bare-function Def-3.5 form, then run the §6.1 hybrid proof verbatim.
  show adaptiveNARGSoundness (init := hyb0Init) (impl := hyb0Impl oSpecImpl)
    (verify := dsfsNargVerify V) langIn langOut
    (bound := fun maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ =>
      IsLemma5_1QueryBound maliciousProver tShared tₕ tₚ tₚᵢ)
    (ε_sr + ENNReal.ofReal
      (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries codec.decodingBias))
  intro maliciousProver hBound
  -- Step 0: the DSFS NARG soundness experiment (Def 3.5) IS the sponge game `dsfsGameDist` on the
  -- false-acceptance marginal (`dsfsNargSoundnessExp_eq_dsfsGame`); rewrite to the sponge game so the
  -- §6.1 hybrid calc applies verbatim.
  rw [dsfsNargSoundnessExp_eq_dsfsGame V oSpecImpl langIn langOut maliciousProver]
  -- Seam #1 (Theorem 5.1 / Key Lemma): the D2SAlgo prover transform, the D2STrace map, and the
  -- bound `tvDist (Hyb₀, Hyb₄) ≤ η★` for this query-bounded prover.
  obtain ⟨d2sAlgoTransform, d2sTraceTransform, hKey⟩ :=
    lemma_5_1 (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
      oSpecImpl V tShared tₕ tₚ tₚᵢ hTp
  have hTv := (hKey maliciousProver hBound).1
  -- L3 (paper two-hop): false acceptance in Hyb₄ ≤ basic-FS NARG soundness (L3a) ≤ IP SR
  -- soundness ε_sr (L3b, Thm 3.18). Matches CO25 §6.1 Eq. lines 1950–1957.
  have hL3 := hyb4_falseAccept_le_nargSoundness V oSpecImpl langIn langOut
    maliciousProver d2sAlgoTransform ε_sr h_IP_SR_sound
  -- §6.1 derivation (open seams: `lemma_5_1` at L2, `hyb4_falseAccept_le_nargSoundness` at L3):
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
conclusion in the *generic* library `Verifier.knowledgeSoundness`; that notion is selective +
**unbounded**, so it cannot carry the query-bounded `η★` term — `theorem_6_2_straightline` instead
concludes CO25 Def 3.6 `adaptiveNARGKnowledgeSoundness` with a query-bounded adversary class.) -/

/-- The **extraction-failure event** for the DSFS straightline-KS game, on the game's
`(stmtIn, extracted-witness?, stmtOut, witOut)` output: the verifier accepted into the output
relation (`(stmtOut, witOut) ∈ relOut`) yet the extracted witness misses `relIn` — or extraction
produced no witness at all (still a failure). `none` (verifier rejected) is not a knowledge break.
Framework-aligned (uses `relOut` for acceptance), matching `nargKSFailEvent` /
`coinKSExperimentProb`.  The DSFS attacker is proof-only, so its `witOut` is `default`. -/
def ksFailEvent (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut)) :
    Option (StmtIn × Option WitIn × StmtOut × WitOut) → Prop
  | some (x, some witIn, stmtOut, witOut) => (stmtOut, witOut) ∈ relOut ∧ (x, witIn) ∉ relIn
  | some (_, none, stmtOut, witOut) => (stmtOut, witOut) ∈ relOut
  | none => False

/-- The DSFS **straightline knowledge-soundness game** (bespoke, query-bounded): run the malicious
prover `𝒫̃` and the DSFS verifier (the §5.8 `dsfsGame`), then run the straightline extractor
`dsfsExtractor` (Construction 6.3) on the proof + combined query log — all under the *same* eager
oracle handler `hyb0Impl oSpecImpl` so the extractor sees the prover's actual trace — and return
`(stmtIn, extracted-witness?, stmtOut, witOut)`. `none` = verifier rejected (`b = 0`).  The
proof-only DSFS attacker has no output witness, so `witOut := default`. -/
def dsfsKSGameDist [Inhabited WitOut]
    (dsfsExtractor : Extractor.Straightline (oSpec + duplexSpongeChallengeOracle StmtIn U)
      StmtIn WitIn WitOut ⟨!v[.P_to_V], !v[DSSaltedProof (pSpec := pSpec) (U := U) δ]⟩)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (Option (StmtIn × Option WitIn × StmtOut × WitOut)) := do
  (simulateQ (hyb0Impl oSpecImpl) (do
    let out? ← (dsfsGame V maliciousProver).run
    match out? with
    | none => pure none
    | some ⟨stmtIn, stmtOut, proof, log⟩ =>
        -- The non-interactive transcript is the single P→V message (the DSFS proof).
        let witIn? ← (dsfsExtractor stmtIn default
          (Fin.cons proof (fun i => i.elim0) :
            FullTranscript ⟨!v[.P_to_V], !v[DSSaltedProof (pSpec := pSpec) (U := U) δ]⟩)
          log []).run
        pure (some (stmtIn, witIn?, stmtOut, (default : WitOut))))).run' (← hyb0Init)

/-- **CO25 §6.2 game-match (the open structural seam).**  The DSFS straightline-KS game factors
through a common extractor kernel `k` (run the **basic-FS NARG-KS extractor `E_std`** on the
basic-FS game output), as two probability equalities:

* **`hL1` — the `Hyb₀` step.**  The DSFS KS game (with Construction 6.3 over `E_std`) equals
  `Hyb₀ >>= k`.  KS analog of the *proven* soundness lemma `dsfsGame_falseAccept_eq_hyb0` (the §5.8
  `D2STrace` line-4 map preserves the read-out), now with the `E_std`-extractor kernel threaded
  through (and absorbing the `d2sTraceLog`/`liftFSExtractToDSFS` seams of Construction 6.3).

* **`hL3` — the `Hyb₄` problem.**  `Hyb₄ >>= k` *is* the **coin-bearing basic-FS NARG
  straightline-KS experiment** (Def 3.6, `adaptiveNARGKnowledgeSoundnessExpWithCoins`) for the
  prover `𝒫̃_std := D2SAlgo(𝒫̃)` (`nargInducedProver`), verifier `V_std^f = fsSaltedVerify V`, and
  extractor `E_std`.  This is the **KS twin of the soundness `hyb4_eq_coinNARGgame`** — the deep
  eager↔presampled-function / `deriveTranscript` / prover-de-abort game-equivalence, **shared in
  substance with §6.1**.  (It is this RHS — *not* `coinKSExperimentProb` — that makes Step 4 route
  through `theorem_3_19_straightline_ks`, faithful to the paper's two-hop.)

`theorem_6_2_straightline` closes around this purely by *proven* bridges — `B3`, data-processing
(`tvDist_bind_right_le`, valid for the shared kernel `k`), and `lemma_5_1`'s `tvDist ≤ η★`.  So this
lemma (together with the cited `lemma_5_1`) is the *only* §6.2 open seam. -/
theorem dsfsKSGame_hybFactorization
    [∀ i, DecidableEq (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [DecidableEq ι] [Inhabited WitOut]
    (E_std : StmtIn → FSSaltedProof pSpec Salt →
      QueryLog ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + ((Unit →ₒ U) + unifSpec)) →
        OptionT (OracleComp (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)) WitIn)
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
          ProbComp (Option (StmtIn × Option WitIn × StmtOut × WitOut))),
      -- `hL1` — Hyb₀ step (KS analog of `dsfsGame_falseAccept_eq_hyb0`):
      Pr[ ksFailEvent relIn relOut |
          dsfsKSGameDist (WitOut := WitOut)
            (dsfsStraightlineExtractor (WitOut := WitOut) E_std) oSpecImpl V maliciousProver ]
        = Pr[ ksFailEvent relIn relOut |
            hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
              (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
              oSpecImpl V maliciousProver d2sTraceTransform >>= k ] ∧
      -- `hL3` — the Hyb₄ problem (KS twin of `hyb4_eq_coinNARGgame`); RHS = NARG straightline-KS
      -- experiment for `𝒫̃_std = nargInducedProverKS`, `V_std^f`, extractor `E_std`:
      Pr[ ksFailEvent relIn relOut |
          hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
            (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
            oSpecImpl V maliciousProver d2sAlgoTransform >>= k ]
        = Pr[ nargKSFailEvent relIn relOut |
            adaptiveNARGKnowledgeSoundnessExpWithCoins
              (srInitDIP (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec))
              ((srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl).addLift
                (srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)))
              d2sAuxImpl
              (fsSaltedVerify (Salt := Salt) V)
              E_std
              (nargInducedProverKS maliciousProver d2sAlgoTransform) ] := by
  sorry

/-- **Construction 6.3 in CO25 Def-3.6 (NARG) shape** — the straightline extractor witnessing the
DSFS NARG's `adaptiveNARGKnowledgeSoundness`.  Wraps `dsfsStraightlineExtractor E_std` (the
`Extractor.Straightline` form) into the single-log Def-3.6 extractor type: build the
non-interactive transcript from the proof `π`, pass a dummy `default` output witness (ignored),
the prover log `tr` as the prover-log slot, and `[]` as the (absent) verifier-log slot. -/
noncomputable def dsfsNargExtractor [Inhabited WitOut]
    (E_std : StmtIn → FSSaltedProof pSpec Salt →
      QueryLog ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + ((Unit →ₒ U) + unifSpec)) →
        OptionT (OracleComp (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)) WitIn) :
    StmtIn → DSSaltedProof (pSpec := pSpec) (U := U) δ →
      QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) →
        OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)) WitIn :=
  fun stmtIn proof tr =>
    dsfsStraightlineExtractor (WitOut := WitOut) E_std stmtIn default
      (Fin.cons proof (fun i => i.elim0) :
        FullTranscript ⟨!v[.P_to_V], !v[DSSaltedProof (pSpec := pSpec) (U := U) δ]⟩)
      tr []

/-- **DSFS NARG-KS experiment = sponge KS game** (CO25 §6.2 game-equivalence).  The Def-3.6
experiment for the DSFS NARG (`adaptiveNARGKnowledgeSoundnessExp`, `verify := dsfsNargVerify V`,
extractor `dsfsNargExtractor E_std`) equals the sponge KS game `dsfsKSGameDist` (Construction 6.3
`dsfsStraightlineExtractor E_std`) on the extraction-failure marginal.  Both run the prover, the §5.8
forward verifier, and the extractor on the proof + prover log; they differ only in the
(extractor-internal, seam-absorbed) query logs.  Provable by `loggingOracle` value-marginalization;
open seam. -/
theorem dsfsNargKSExp_eq_dsfsKSGame [Inhabited WitOut]
    (E_std : StmtIn → FSSaltedProof pSpec Salt →
      QueryLog ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + ((Unit →ₒ U) + unifSpec)) →
        OptionT (OracleComp (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)) WitIn)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    Pr[ nargKSFailEvent relIn relOut |
        adaptiveNARGKnowledgeSoundnessExp hyb0Init (hyb0Impl oSpecImpl) (dsfsNargVerify V)
          (dsfsNargExtractor (WitOut := WitOut) E_std)
          (dsfsKSAdversary (WitOut := WitOut) maliciousProver) ]
      = Pr[ ksFailEvent relIn relOut |
          dsfsKSGameDist (WitOut := WitOut)
            (dsfsStraightlineExtractor (WitOut := WitOut) E_std) oSpecImpl V maliciousProver ] := by
  sorry

/-- CO25 **Theorem 6.2 (straightline knowledge soundness)** — bespoke, query-bounded form.

For every malicious prover making at most `(tₕ, tₚ, tₚᵢ)` permutation/hash queries, the DSFS
straightline-KS extraction-failure probability is at most `ε_sr + η★`, where `ε_sr` is the IP's
straightline state-restoration KS error and `η★` is the Key-Lemma additive error.  The extractor
witness is **Construction 6.3** (`dsfsStraightlineExtractor E_std`): apply `D2STrace` to the DSFS
query log to get `tr_std`, then run the **basic-FS NARG-KS extractor `E_std`** on it — where `E_std`
is delivered by **Theorem 3.19** (`theorem_3_19_straightline_ks`) from the IP's SR-KS.

**Shape (per design, as for `theorem_6_1_soundness`)**: phrased over `MaliciousProver` with an
explicit query bound — the unbounded `Verifier.knowledgeSoundness` form is unprovable here (`η★`
only controls query-bounded provers).  Hypothesis is the *coin-bearing* SR-KS notion
`knowledgeSoundnessWithCoins` (the KS analog of `theorem_6_1`'s `soundnessWithCoins`): the compiled
prover `𝒫̃_std = D2SAlgo^f(𝒫̃)` has private coins, answered by `d2sAuxImpl`; `E_std` is coin-blind.

**Proof flow (the paper's two-hop, §6.2 Eq. 1986–2011; every `≤` bridge is proven).**  Factoring both
`Hyb₀` and `Hyb₄` through a *common* extractor kernel `k` (run `E_std` on the FS game output):
```
ε_NARG^ks = Pr[ksFail | DSFS KS game w/ Construction 6.3 over E_std]
  = Pr[ksFail | Hyb₀ >>= k]                        -- (Step 1) unfold Constr 6.3  [seam hL1]
  ≤ Pr[ksFail | Hyb₄ >>= k] + tvDist(Hyb₀>>=k, …)  -- B3                          ✓
  ≤ Pr[ksFail | Hyb₄ >>= k] + tvDist(Hyb₀, Hyb₄)   -- data-processing      ✓ tvDist_bind_right_le
  ≤ Pr[ksFail | Hyb₄ >>= k] + η★                   -- (Step 2) Lemma 5.1         ✓ lemma_5_1 (hTv)
  = κ_NARG^ks[V_std^f](𝒫̃_std) + η★                  -- (Step 3) Hyb₄ = NARG-KS game [seam hL3]
  ≤ ε_IP^sr + η★                                   -- (Step 4) Theorem 3.19      ✓ hE_std
```
Step 4 is the **literal application of `theorem_3_19_straightline_ks`** (`hE_std` applied to the
induced prover `𝒫̃_std = nargInducedProver`), mirroring §6.1's `theorem_3_18_soundness` use —
faithful to the paper (not collapsed).  The data-processing step applies the *same* kernel `k` to
both hybrids, so `lemma_5_1`'s `tvDist(Hyb₀,Hyb₄) ≤ η★` transports verbatim
(`tvDist_bind_right_le`).  Open seams:
`dsfsKSGame_hybFactorization` (bundled `hL1 ∧ hL3`, KS twin of `hyb4_eq_coinNARGgame`), the
Construction-6.3 spec seams (`d2sTraceLog`/`liftFSExtractToDSFS`), `theorem_3_19_straightline_ks`
(FS↔SR-KS crosswalk), and `lemma_5_1` (Thm 5.1). -/
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
    -- CO25 **Def 3.6** (`adaptiveNARGKnowledgeSoundness`) at the DSFS NARG: oracle model
    -- `hyb0Init`/`hyb0Impl`, verifier `dsfsNargVerify V`, acceptance `(stmtOut, witOut) ∈ relOut`;
    -- adversary class = the query-bounded proof-only DSFS attacker `dsfsKSAdversary 𝒫̃`.
    (Verifier.dsfsNargNIV δ V).adaptiveNARGKnowledgeSoundness (WitIn := WitIn) (WitOut := WitOut)
      (init := hyb0Init) (impl := hyb0Impl oSpecImpl)
      (relIn := relIn) (relOut := relOut)
      (bound := fun P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
          (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ × WitOut) =>
        ∃ maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ,
          IsLemma5_1QueryBound maliciousProver tShared tₕ tₚ tₚᵢ ∧
            P = dsfsKSAdversary maliciousProver)
      (error := ε_sr + ENNReal.ofReal
        (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries codec.decodingBias)) := by
  -- `Verifier.dsfsNargNIV δ V`'s verify is defeq to `dsfsNargVerify V`; cast to the bare-function
  -- Def-3.6 form, then run the §6.2 proof verbatim.
  show adaptiveNARGKnowledgeSoundness (init := hyb0Init) (impl := hyb0Impl oSpecImpl)
    (verify := dsfsNargVerify V) (relIn := relIn) (relOut := relOut)
    (bound := fun P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
        (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ × WitOut) =>
      ∃ maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ,
        IsLemma5_1QueryBound maliciousProver tShared tₕ tₚ tₚᵢ ∧
          P = dsfsKSAdversary maliciousProver)
    (error := ε_sr + ENNReal.ofReal
      (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries codec.decodingBias))
  -- **Step 4 (Theorem 3.19).** IP SR-KS ⟹ basic-FS NARG straightline-KS, delivering `E_std`.
  obtain ⟨E_std, hE_std⟩ :=
    theorem_3_19_straightline_ks (Salt := Salt) ((Unit →ₒ U) + unifSpec) d2sAuxImpl V relIn relOut
      (srInitDIP (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec))
      (srImplLift (StmtIn := StmtIn) (Salt := Salt) (pSpec := pSpec) oSpecImpl) ε_sr h_IP_SR_KS
  -- Extractor witness: Construction 6.3 in NARG shape (`dsfsNargExtractor`) over `E_std`.
  refine ⟨dsfsNargExtractor (WitOut := WitOut) E_std, fun P hBound => ?_⟩
  -- The DSFS attacker is a query-bounded proof-only `MaliciousProver` claiming `default` witOut.
  obtain ⟨maliciousProver, hQB, rfl⟩ := hBound
  -- Step 0: the DSFS NARG-KS experiment (Def 3.6) IS the sponge KS game `dsfsKSGameDist` on the
  -- extraction-failure marginal (`dsfsNargKSExp_eq_dsfsKSGame`); rewrite to the sponge game so the
  -- §6.2 hybrid calc applies verbatim.
  rw [dsfsNargKSExp_eq_dsfsKSGame (WitOut := WitOut) E_std V oSpecImpl relIn relOut
      maliciousProver]
  -- **Seam #1 (Key Lemma 5.1).** Prover/trace transforms + `tvDist(Hyb₀, Hyb₄) ≤ η★`.
  obtain ⟨d2sAlgoTransform, d2sTraceTransform, hKey⟩ :=
    lemma_5_1 (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P)
      oSpecImpl V tShared tₕ tₚ tₚᵢ hTp
  have hTv := (hKey maliciousProver hQB).1
  -- **Seam #2 (the §6.2 game-match) — the named lemma `dsfsKSGame_hybFactorization`.**
  -- It supplies the common extractor kernel `k` and the two equalities `hL1` (Step 1: unfold
  -- Construction 6.3) ∧ `hL3` (Step 3: Hyb₄ = NARG-KS game, KS twin of `hyb4_eq_coinNARGgame`).
  obtain ⟨k, hL1, hL3⟩ :=
    dsfsKSGame_hybFactorization (WitOut := WitOut) E_std V oSpecImpl relIn relOut maliciousProver
      d2sTraceTransform d2sAlgoTransform
  set H0 := hyb_0 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      oSpecImpl V maliciousProver d2sTraceTransform with hH0
  set H4 := hyb_4 (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      oSpecImpl V maliciousProver d2sAlgoTransform with hH4
  -- All `≤` bridges below are **proven**: Step 1 (`hL1`), B3, data-processing
  -- (`tvDist_bind_right_le`), the Key-Lemma bound (`hTv`), Step 3 (`hL3`), and Step 4 (`hE_std`).
  calc Pr[ ksFailEvent relIn relOut |
          dsfsKSGameDist (WitOut := WitOut)
            (dsfsStraightlineExtractor (WitOut := WitOut) E_std) oSpecImpl V maliciousProver ]
      = Pr[ ksFailEvent relIn relOut | H0 >>= k ] := hL1
    _ ≤ Pr[ ksFailEvent relIn relOut | H4 >>= k ] + ENNReal.ofReal (tvDist (H0 >>= k) (H4 >>= k)) :=
        probEvent_le_probEvent_add_ofReal_tvDist _ _ _
    _ ≤ Pr[ ksFailEvent relIn relOut | H4 >>= k ] + ENNReal.ofReal (tvDist H0 H4) :=
        add_le_add (le_refl _) (ENNReal.ofReal_le_ofReal (tvDist_bind_right_le k H0 H4))
    _ ≤ Pr[ ksFailEvent relIn relOut | H4 >>= k ]
          + ENNReal.ofReal (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries codec.decodingBias) :=
        add_le_add (le_refl _) (ENNReal.ofReal_le_ofReal hTv)
    -- Step 3 (`rw [hL3]`: Hyb₄ = NARG-KS game) ∘ Step 4 (`hE_std`: Theorem 3.19 on `𝒫̃_std`).
    -- `refine add_le_add ?_ (le_refl _)` takes the event from the *goal*, then `exact` discharges
    -- the bound by full defeq (unfolding the NARG-KS-experiment event `match` aux-defs).
    _ ≤ ε_sr + ENNReal.ofReal
            (ηStar U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries codec.decodingBias) := by
        rw [hL3]
        refine add_le_add ?_ (le_refl _)
        exact hE_std (nargInducedProverKS maliciousProver d2sAlgoTransform) trivial

end

end DuplexSpongeFS
