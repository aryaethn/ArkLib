# Proximity-Prize "bits of security" leaderboard

A machine-checked leaderboard for the soundness of the ABF26 §6 toy protocol. It
turns the Ethereum Foundation **Proximity Prize** (proximityprize.org, $1M)
question — *how big is the gap between what we can prove and the best known
attack?* — into a single Lean scalar that contestants minimise.

- **Code:** [`ArkLib/ProofSystem/ToyProblem/Leaderboard.lean`](../../ArkLib/ProofSystem/ToyProblem/Leaderboard.lean)
- **Paper:** Arnon–Boneh–Fenzi, *Open Problems in List Decoding and Correlated
  Agreement* (eprint 2026/680), §6.2 (Lemma 6.8), §6.4 (Lemmas 6.12, 6.13),
  §6.3 (Tables 2–5). The attack side is also Fenzi–Sanso, eprint 2025/2197
  (Construction 4.2 = C6.2, Lemma 4.4 = Lemma 6.12).

## The one quantity both sides bound

The whole design hinges on a single decision: the two leaderboard sides must
bound the **same** quantity, or the gap between them is meaningless. That common
quantity is the protocol's **actual soundness error**

```
soundnessError := winningSetSoundness C δ
```

`winningSetSoundness` is the soundness error of the **simplified IOR** `T'[C]`
(Construction 6.9, the §6.4 attack target) per ABF26 Definition 6.11: the
worst-case winning-challenge fraction `|Ω| / |F|` over instances that
**violate** the relaxed relation `R̃²` (the violating constraint is essential —
a *valid* instance has `Ω = F`, fraction 1). It is the object the §6.4 attacks
*directly* lower-bound and Lemma 6.10 upper-bounds. It is **`t`-independent**:
`T'[C]` is single-round, so there is no `(1-δ)^t` spot-check term — that round
belongs to the *full* protocol C6.2 and lives only in the X-side vehicle below.
(Folding `(1-δ)^t` into the common quantity would be unfaithful: at the prize
regime `(1/√2)^128 = 2^(-64) > 2^(-116)`, so it would make the attack side
trivial — and at smaller `δ` make the provable side a *falsehood*.)

Two bounds sandwich it:

```
   2^(-Y)  ≤   soundnessError   ≤   2^(-X)
 (attack)     (C6.9 error)       (provable)
```

- **X side (provable security).** `soundnessError ≤ toySoundnessError ≤ 2^(-X)`,
  where `toySoundnessError = max (ε_mca(C,δ) + |Λ(C^{≡2},δ)|/|F|) ((1-δ)^t)`
  reuses the **exact** per-round error terms of the *full*-protocol Lemmas 6.6 /
  6.8 (`protocol62_knowledgeSound`). It upper-bounds `winningSetSoundness` via
  Lemma 6.10 (the `ε_mca + |Λ|/|F|` branch already dominates the simplified-IOR
  error). `toySoundnessError` is the *vehicle*, not the leaderboard quantity; at
  the prize regime its spot-check branch `(1/√2)^128 = 2^(-64)` is the binding
  cap, so provable security tops out at 64 bits.
- **Y side (best attack).** `soundnessError ≥ |Ω|/|F| ≥ 2^(-Y)`, where the
  winning-set lower bound is the attack of Lemma 6.12 / 6.13.

**Why the upper bound is stated against `soundnessError`, not
`toySoundnessError`.** If we stated "we can prove X bits" against the RBR bound
`toySoundnessError`, a contestant could "win" by *inflating* the RBR analysis
rather than by exhibiting a real attack — unfaithful. Stating both sides against
the actual `soundnessError` forces the attack side to produce a genuine
winning-set witness.

## How to submit

A submission is an *inhabitant* of one of two structures, both at the fixed
anchor parameter point `koalaIRS : ToyParams`:

```lean
open ToyProblem

-- "We can prove ≥ 70 bits of security."
def myLowerBound : SecurityLowerBound koalaIRS where
  bits  := 70
  proof := by
    -- show  koalaIRS.soundnessError ≤ (2 : ℝ≥0) ^ (-(70 : ℝ))
    sorry

-- "No analysis can prove > 110 bits."
def myAttack : SecurityUpperBound koalaIRS where
  bits  := 110
  proof := by
    -- show  koalaIRS.soundnessError ≥ (2 : ℝ≥0) ^ (-(110 : ℝ))
    sorry
```

- `bits : ℝ` (not `ℕ`), so fractional bits like `116.5` are representable.
- `(2 : ℝ≥0) ^ (-bits)` is `NNReal.rpow` (real exponent).
- A better lower-bound submission *raises* `X`; a better attack *lowers* `Y`.

## The metric

```lean
securityGap (lo : SecurityLowerBound p) (hi : SecurityUpperBound p) : ℝ
  := hi.bits - lo.bits
```

This is the scalar contestants minimise. It is always `≥ 0`:
`SecurityLowerBound.bits_le_of` proves `lo.bits ≤ hi.bits` directly from the two
inequalities (`2^(-hi.bits) ≤ soundnessError ≤ 2^(-lo.bits)` and the strict
antitonicity of `x ↦ 2^(-x)`), and `securityGap_nonneg` packages it. Both are
**axiom-clean** (`#print axioms` shows only `propext`/`Classical.choice`/
`Quot.sound`, no `sorryAx`) — the honesty of the metric does not depend on any
owed §6 proof.

## Current anchors (the 64 / 116 frontier)

At the KoalaBear-sextic regime (`q = 2^31 - 2^24 + 1`, sextic extension,
`ρ = 1/2`, `t = 128`):

| Anchor | `bits` | Basis |
|---|---|---|
| `arklib_lowerBound_irs_t128 : SecurityLowerBound koalaIRS` | ≈ **64** | ABF26 Lemmas 6.10 / 6.6 RBR bound at §6.3 Tables 2–3 (spot-check-limited) |
| `fenziSanso_upperBound_attack : SecurityUpperBound koalaIRS` | ≈ **116** | ABF26 Lemma 6.12 (cf. Fenzi–Sanso 2025/2197 Lemma 4.4) |

so `securityGap = 116 − 64 = 52` (the lemma `securityGap_koalaIRS_anchors`
evaluates this). Both anchors are `sorry`-tagged by design — the soundness
*inequalities* are genuine propositions; their §6 proofs are Phase 3 and the
KoalaBear numerics are Phase 5 (see the plan doc). Notes:

- The **64** is the *full-protocol* (C6.2) provable ceiling — at `t = 128`,
  `δ ≈ 1-1/√2`, the spot-check term `(1/√2)^128 = 2^(-64)` dominates the RBR
  bound `max(2^(-71.5), 2^(-64))` (ABF26 §6.3). As a bound on the simplified-IOR
  `winningSetSoundness` it is *conservative* (the `ε_mca + |Λ|/|F|` branch is the
  tighter ≈`2^(-71.5)`), hence an improvable leaderboard entry.
- The anchor carrier is `GaloisField 2 128` (size `2^128`), a same-*order*
  stand-in for the `≈2^186`-element KoalaBear-sextic field, with an **opaque**
  placeholder code. The large field is required for the `[2^(-116), 2^(-64)]`
  window to be representable, and opacity keeps `winningSetSoundness` irreducible
  so neither anchor is provably true or false. Phase 5 substitutes the genuine
  RS/IRS KoalaBear-sextic field and code.

## Connection to the grand challenges (Phase 1)

The X side improves whenever `ε_mca` or the list size `|Λ|` shrinks. The Phase-1
framework in
[`ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean`](../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean)
captures exactly this: a tighter `MCALowerWitness` (a verified `ε_mca(C,δ) ≤ ε*`)
shrinks the `ε_mca` term inside `toySoundnessError`, which raises the provable
lower bound `X` and so narrows `securityGap`. Resolving the Grand MCA / List
Decoding Challenges feeds the leaderboard's lower side directly.

## Prior art

The only loose precedent is competition-style program verification (e.g.
VerifyThis), where entrants submit machine-checked artifacts judged against a
fixed specification. This leaderboard differs in that the *metric itself* — the
provable-vs-attack security gap — is a Lean scalar, and both "sides" are
adversarial inhabitants of opposing structures over one common soundness
quantity.
