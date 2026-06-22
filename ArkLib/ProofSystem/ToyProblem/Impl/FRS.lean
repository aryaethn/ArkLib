/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Folded
import ArkLib.ProofSystem.ToyProblem.Leaderboard

/-!
# Toy problem — folded Reed–Solomon instantiation (ABF26 §6.3.2)

The second concrete leaderboard entry for the §6 toy-problem frontier: take the
underlying code to be a **folded** Reed–Solomon code `FRS[F, L, k, s, ω]` with
folding parameter `s > 1`, so a codeword symbol is a length-`s` tuple
`Fin s → F` rather than a scalar `F` (ABF26 Definition 2.15 [GR08]). This is the
`A = Fin s → F` instantiation of the alphabet-generic toy problem (the `A = F`
scalar case is the interleaved-RS entry `koalaIRS` in `Leaderboard.lean`).

Folding is the lever behind the paper's §6.3.2 *subspace-design* analysis: the
`τ`-subspace-design list-decodability of FRS (`τ(r) = s·ρ/(s − r + 1)`) drives
the list-size term, and the construction's **argument-size at enforced 128-bit
security** improves over interleaved RS for large folding. Here we record the
KoalaBear-sextic FRS leaderboard anchors for the **`s = 2^5 = 32` row** — the
paper's primary fully-worked example (`tab:subspace-design-security-analysis`
and `tab:subspace-elias-lowerbound-thresholds`, both at `t = 128`).

## The `s = 32` row at `t = 128` (ABF26 §6.3.2)

* Field `F = KoalaSextic` (`|F| = q^6 ≈ 2^186`), rate `ρ = 1/2`, evaluation
  domain `|L| = 2^16`, message size `k = 2^20`, folding `s = 2^5 = 32`
  (so `k = 2^20 ≤ s·|L| = 2^21`).
* **Provable** RBR knowledge soundness (X side, `tab:subspace-design-security-`
  `analysis`, `r = 8`): `bestProvableError ≤ 2^(-29.11)` — the convex
  combination of the spot-check term `(τ(r+1) + 3/(2r))^128 ≈ 2^(-29.11)` and
  the list-size term `≈ 2^(-166.8)`.
* **Attack** (Y side): `bestProvableError ≥ 2^(-128.01)`. This is the **sweep
  floor** `⨅_δ (1-δ)^t + …`, certified from the **spot-check term alone** — the
  convex combination dominates `(1-δ)^t`, whose infimum over the window
  `(0, δ_min)` is `(1-δ_min)^128 ≈ 2^(-128.006)` because the folded code's MDS
  relative distance `δ_min = D/|L| = 32769/65536 ≈ 0.50002` (a degree-`< k`
  polynomial has `< k` roots, hence `< (k-1)/s = 32767` zero folded-symbols).
  No Elias/list-size lower bound is needed for this ceiling. The paper's
  per-`δ*` Elias value (`tab:subspace-elias-lowerbound-thresholds`, `δ* = 0.499`)
  is the *weaker* point reading `2^(-127.63) = (1-0.499)^128`; it is **not** the
  sweep floor (just above `δ*` the spot-check keeps dropping toward `2^(-128)`,
  so `2^(-127.63)` is not a valid floor unless the list-size term is active
  across the whole `(δ*, δ_min)` sliver — the same sub-band subtlety that bumped
  the interleaved ceiling `116.49 → 117`). The ceiling rounds **up** to `128.01`.
* `securityGap = 128.01 − 29.11 = 98.90` bits.

**Reading the gap honestly.** At a *fixed* `t = 128`, `s = 32` folding gives a
*larger* `bestProvableError` gap than the interleaved entry (`koalaIRS`:
`53.01`). This is faithful, not a defect: folding at fixed `t` does not by
itself improve the δ-swept provable frontier (for `s ≤ 2^4` the paper proves
*no* soundness at all at `t = 128`). The FRS advantage lives on a **different
axis** the toy `bestProvableError` (a fixed-`t` δ-sweep) does not capture:

* **larger folding closes the gap** — at `s = 2^12` the provable side reaches
  `2^(-118.14)` (`r = 108`), a `≈ 10`-bit gap to the `≈ 2^(-128)` attack; and
* **argument-size at enforced 128-bit security** — the `s = 2^5` row reaches
  full `2^(-128.03)` provable soundness at repetition `t = 563`, `r = 8` with
  argument size `417.9 KiB` (`tab:subspace-design-128bit-security`), the metric
  on which folding genuinely beats interleaving.

Both are recorded in the docstrings of `frsLowerBound` / `securityGap_koalaFRS`
(cited, not re-derived — the lower-bound numerics are owed external coding-theory
results, exactly as for `koalaIRS`; the attack ceiling, by contrast, is owed only
the folded MDS relative distance — see `frsUpperBound_attack`).

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§6.3.2, Tables for folded Reed–Solomon).
-/

namespace ToyProblem

namespace Impl.FRS

open scoped NNReal ENNReal
open Polynomial ReedSolomon.Folded

/-- The folding multiplier `ω` for the `s = 32` folded RS code. A faithful
instantiation takes the paper's `ω` (a field element whose folded orbits
`{α · ω^i : α ∈ L, i < s}` are pairwise distinct — the GR08 `(L, s)`-admissibility
condition, `ReedSolomon.Folded.Admissible`). Over the **noncomputable**
`GaloisField KoalaBear.fieldSize 6` the multiplicative-order facts establishing
admissibility are not available `sorry`-free (the multiplicative analogue of the
additive distinctness used for `koalaDomain`); admissibility — and hence encoder
injectivity — is therefore an owed structural fact (`koalaFRSEnc_injective`). The
concrete witness here is documentary. -/
noncomputable def koalaFoldω : KoalaSextic := 7

/-- The `2^16`-point folded-RS evaluation domain `{1, 2, …, 2^16} ⊆ KoalaSextic`
— deliberately **zero-free** (each point is `i + 1`). Distinctness is injectivity
of `Nat.cast` below the characteristic (`2^16 + 1 ≤ KoalaBear.fieldSize ≈ 2^31`),
exactly as for `koalaDomain`.

The paper's folded-RS evaluation domain is a *smooth multiplicative coset*
(`{g · h^j}`, [ABF26] §6.3 "common case"), which is zero-free; we exclude `0`
here for the same reason it matters downstream: the GR08 admissibility condition
(`ReedSolomon.Folded.Admissible`) requires the folded orbits `{α · ω^i}` to be
pairwise distinct, and its intra-orbit clause `α · ω^i ≠ α` (for `0 < i < s`) is
*false* at `α = 0` (`0 · ω^i = 0`). A domain containing `0` could therefore never
be admissible; a zero-free domain keeps admissibility a genuinely-owed (not
provably-false) side condition (see `koalaFRSEnc_injective`). -/
noncomputable def koalaFRSDomain : Fin (2 ^ 16) ↪ KoalaSextic where
  toFun i := ((i.val + 1 : ℕ) : KoalaSextic)
  inj' i j hij := by
    have hil : (i : ℕ) < 2 ^ 16 := i.isLt
    have hjl : (j : ℕ) < 2 ^ 16 := j.isLt
    have hchar : (2 ^ 16 : ℕ) < KoalaBear.fieldSize := by norm_num [KoalaBear.fieldSize]
    have hi : (i.val + 1) ∈ Set.Iio KoalaBear.fieldSize := Set.mem_Iio.mpr (by omega)
    have hj : (j.val + 1) ∈ Set.Iio KoalaBear.fieldSize := Set.mem_Iio.mpr (by omega)
    have hnat : i.val + 1 = j.val + 1 :=
      CharP.natCast_injOn_Iio KoalaSextic KoalaBear.fieldSize hi hj hij
    exact Fin.val_injective (by omega)

/-- The genuine §6.3.2 folded encoder: the degree-`< 2^20` folded Reed–Solomon
evaluation map on the `2^16` points of `koalaFRSDomain` with folding `s = 32`
(`k = 2^20`, `|L| = 2^16`, `s = 2^5`, rate `ρ = 1/2`), as an `F`-linear map
`(Fin 2^20 → F) →ₗ (Fin 2^16 → Fin 32 → F)`. Built as
`frsEvalOnPoints ∘ (degreeLTEquiv).symm`, mirroring `koalaEnc` with
`ReedSolomon.Folded.frsEvalOnPoints` in place of `evalOnPoints` (the scalar
`s = 1` case). The codeword alphabet is `A = Fin 32 → KoalaSextic`. -/
noncomputable def koalaFRSEnc :
    (Fin (2 ^ 20) → KoalaSextic) →ₗ[KoalaSextic] (Fin (2 ^ 16) → Fin 32 → KoalaSextic) :=
  (frsEvalOnPoints koalaFRSDomain 32 koalaFoldω).domRestrict
      (Polynomial.degreeLT KoalaSextic (2 ^ 20))
    ∘ₗ (Polynomial.degreeLTEquiv KoalaSextic (2 ^ 20)).symm.toLinearMap

/-- **Injectivity of the folded encoder** ([ABF26] Definition 6.1's "code as the
injective map"). Mathematically this would follow from `(L, s)`-admissibility of
`koalaFoldω` (`ReedSolomon.Folded.Admissible`, the GR08 condition that the `s·|L|`
folded evaluation points `{α · ω^i}` are pairwise distinct) together with
`k ≤ s·|L|` (here `2^20 ≤ 32·2^16 = 2^21`): a degree-`< k` polynomial vanishing
on `s·|L| ≥ k` distinct points is zero, so the unfolded evaluation — hence
`frsEvalOnPoints` on `degreeLT k` — would be injective. `koalaFRSDomain` is
zero-free precisely so `Admissible koalaFoldω` is not *provably false* (its
intra-orbit clause fails at `0`; see `koalaFRSDomain`).

**Owed (structural), in two parts.** (1) `ReedSolomon.Folded` provides **no**
`Admissible ω → Function.Injective (frsEvalOnPoints …)` bridge — `dim_frsCode`
takes encoder injectivity as a *hypothesis* (`h_encoder_inj`); that general lemma
would have to be added (unlike the interleaved case, whose `koalaEnc_injective`
*did* have the in-tree bridge `ReedSolomon.evalOnPoints_domRestrict_injective`).
(2) Even with the bridge, `Admissible koalaFoldω` requires multiplicative-order
facts about `ω` in the **noncomputable** `GaloisField KoalaBear.fieldSize 6`,
not available `sorry`-free here (the multiplicative analogue of the additive
characteristic argument behind `koalaDomain`; cf. the Session 1a finding). This
is the FRS counterpart of the owed external dependencies carried by the
`koalaIRS` anchors — a named, legitimately-owed gap, not a hand-wave. -/
theorem koalaFRSEnc_injective : Function.Injective koalaFRSEnc := by
  sorry

/-- The folded-RS Proximity-Prize parameter point: the KoalaBear-sextic regime
with folding `s = 2^5 = 32` (`|F| = q^6 ≈ 2^186`, `ρ = 1/2`, eval domain
`|L| = 2^16`, message `k = 2^20`, `t = 128`). The codeword alphabet is the folded
`A = Fin 32 → KoalaSextic`; the `A = F` scalar case is `koalaIRS`. As with
`koalaIRS`, δ is swept inside `bestProvableError` (no pinned δ). -/
noncomputable def koalaFRS : ToyParams := by
  haveI : Fintype KoalaSextic := Fintype.ofFinite _
  classical
  exact
    { F := KoalaSextic
      ι := Fin (2 ^ 16)
      A := Fin 32 → KoalaSextic
      k := 2 ^ 20
      enc := koalaFRSEnc
      enc_injective := koalaFRSEnc_injective
      t := 128
      q := KoalaBear.fieldSize
      ext := 6
      ρ := 1 / 2
      s := 32
      n := 2 ^ 16 }

/-- **Folded-RS provable lower bound (≈29 bits) at the KoalaBear/`s=32`/`t=128`
point.** Cites the §6.3.2 subspace-design analysis
(`tab:subspace-design-security-analysis`, `s = 2^5`, minimizing `r = 8`): the RBR
knowledge soundness is `≤ 2^(-29.11)`, the convex combination of the spot-check
term `(τ(9) + 3/16)^128 = (2/3 + 3/16)^128 ≈ 2^(-29.11)` and the
subspace-design list-size term `≈ 2^(-166.8)` (with `τ(r) = s·ρ/(s − r + 1)`).

`sorry`-backed by design: the τ-subspace-design list-decodability bound
(`lemma:subspace-design-are-list-decodable` + `lemma:interleaving-list-decoding`)
and the `ε_mca` term are external coding-theory results — the FRS counterpart of
the owed numerics in `arklib_lowerBound_irs_t128`.

**Why folding at fixed `t = 128` is not where FRS wins.** `s = 32` gives only
`≈ 29` provable bits (for `s ≤ 2^4` *no* soundness is provable at `t = 128`).
Folding's payoff is on two other axes: larger folding closes the gap
(`s = 2^12`, `r = 108`: `2^(-118.14)`, a `≈ 10`-bit gap), and the
128-bit-enforcing construction reaches `2^(-128.03)` provable soundness at
repetition `t = 563`, `r = 8`, argument size `417.9 KiB`
(`tab:subspace-design-128bit-security`) — the argument-size metric on which FRS
beats interleaved RS. -/
noncomputable def frsLowerBound : SecurityLowerBound koalaFRS where
  bits := 29.11
  proof := by
    -- ABF26 §6.3.2 subspace-design analysis (tab:subspace-design-security-analysis,
    -- s = 2^5, r = 8). Provable RBR soundness ≤ 2^(-29.11); the τ-subspace-design
    -- list-decodability bound + ε_mca are owed external coding-theory results
    -- (the FRS counterpart of the koalaIRS owed numerics). Phase-5/external-owed.
    sorry

/-- **Folded-RS attack upper bound (`128.01` bits) at the KoalaBear/`s=32`/`t=128`
point — the δ-sweep floor, certified from the spot-check term alone.** No
δ-relaxation analysis proves more than `128.01` bits: for *every* admissible δ the
convex combination dominates its round-2 spot-check term `(1-δ)^t`, and over the
window `(0, δ_min)` that term's infimum is `(1-δ_min)^128`. The folded code's
**MDS relative distance** is `δ_min = D/|L| = 32769/65536 ≈ 0.50002` — a
degree-`< k = 2^20` polynomial has `< k` roots, hence `< (k-1)/s = 32767` zero
folded-symbols, so `D ≥ |L| - 32767 = 32769`. Therefore
`bestProvableError ≥ (1-δ_min)^128 ≈ 2^(-128.006)`, and the ceiling rounds **up**
to `128.01`.

**This is stronger and less owed than the paper's per-`δ*` reading.** The §6.3.2
Elias table (`tab:subspace-elias-lowerbound-thresholds`, `s = 2^5`, `δ* = 0.499`)
reports `2^(-127.63) = (1-0.499)^128`, the *point* soundness at `δ*`. That is
**not** the sweep floor: just above `δ* = 0.499` the spot-check keeps dropping
toward `2^(-128)` at `δ_min ≈ 0.50002`, so `2^(-127.63)` is a valid floor only if
the list-size term stays active across the whole `(δ*, δ_min)` sliver — the same
sub-band gap that forced the interleaved ceiling `116.49 → 117`
(`listDecoding_upperBound_attack`). The spot-check route sidesteps the Elias
list-size lower bound entirely; what remains owed is only the **folded MDS
distance** `minRelHammingDistCode (frsCode …) ≥ 32769/65536` (no such lemma is in
`ReedSolomon.Folded` yet — it has only `dim_frsCode` — so this stays `sorry`-backed
pending that distance lemma; cf. the scoped FRS-anchor-reduction session). Unlike
the interleaved attack, the owed fact here is a *distance* bound, not a list-size
lower bound. -/
noncomputable def frsUpperBound_attack : SecurityUpperBound koalaFRS where
  bits := 128.01
  proof := by
    -- Sweep floor from the spot-check term alone: for every δ ∈ (0, δ_min) the
    -- convex combination ≥ (1-δ)^128 ≥ (1-δ_min)^128 ≈ 2^(-128.006), where the
    -- folded MDS relative distance δ_min = 32769/65536 ≈ 0.50002. Rounds up to
    -- 128.01. No Elias/list-size bound needed; owed only the folded distance
    -- `minRelHammingDistCode (frsCode …) ≥ 32769/65536` (absent from
    -- ReedSolomon.Folded — has only dim_frsCode). Phase-5/external-owed (distance).
    sorry

/-- **The folded-RS leaderboard frontier (`s = 32`, `t = 128`).** The honest
certified anchors are `29.11` provable bits and a `128.01`-bit attack ceiling (the
spot-check sweep floor; see `frsUpperBound_attack`), so the §6.3.2 gap at this
folded point is `128.01 − 29.11 = 98.90` bits. As with
`securityGap_koalaIRS_anchors`, this is a pure arithmetic readoff of the two
`bits` fields (it inherits the anchors' owed `sorry`s). At fixed `t = 128` this
gap is *wider* than the interleaved `koalaIRS` frontier (`53.01`) — folding's
advantage is argument-size at enforced 128-bit security and gap-closing at large
folding, not the fixed-`t` δ-swept frontier (see `frsLowerBound`). -/
theorem securityGap_koalaFRS :
    securityGap frsLowerBound frsUpperBound_attack = 98.90 := by
  simp only [securityGap, frsLowerBound, frsUpperBound_attack]
  norm_num

end Impl.FRS

end ToyProblem
