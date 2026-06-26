/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Cardinality
import ArkLib.Data.Lattices.CyclotomicRing.Norms

/-!
# The Norm Bound `‖ψ(a)‖∞ ≤ 2β` (Hachi §3, Lemma 6)

Hachi [NOZ26, §3, Lemma 6]: if `a` is a vector over `R_q^H` with `‖a‖∞ ≤ β` and `ψ` is
the packing map of Theorem 2 (Eq. 8), then `‖ψ(a)‖∞ ≤ 2β`.

The paper derives this "directly from the explicit formula in Equation (9), where some
coefficients of `ψ(a)` are equal to the sum of two coefficients of `a`". Concretely: every
entry `a_j ∈ R_q^H` is supported on the coefficient positions `(d/2k)·s` (Eq. 7), the
packing exponents `packExp j` of distinct summands of `ψ(a)` are distinct modulo `d/2k`
*within* each half of the index range, and the `X^{d/2}`-shift of the second half realigns
it with the first (`d/2 = k·(d/2k)`). Hence each coefficient of `ψ(a)` receives
contributions (with signs, from the `X^d = -1` folding) from **at most two** coefficients
of the entries of `a` — one from the first half and one from the second — which gives the
factor `2`.

Norms are the centered coefficient norms of `Norms.lean` with the balanced representative
`zmodCenteredView` (`ZMod.valMinAbs`, the paper's `mod± q` convention); `‖a‖∞` is the
entrywise maximum `vecCInfNorm`, matching the vector norm of [NOZ26, §2.1].

## Main statement

* `cInfNorm_psi_le` — **Lemma 6** (proven; see its docstring for the proof outline).

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open CompPoly Finset

namespace ArkLib.Lattices.CyclotomicModulus

variable (q : ℕ) [Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)]

section Support

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]

/-- **`σ_{-1}(X^e) = -X^{d-e}`** for `0 < e < d`: the conjugate of a sub-`d/2` monomial is minus
the complementary monomial. The only nonzero coefficient of `σ_{-1}(X^e)` sits at `d - e`, with
sign `-1`: from `e·conjExp ≡ 2^{α+1} - e (mod 2^{α+1})` we get
`σ_{-1}(X^e) = X^{d + (d-e)} = -X^{d-e}`. -/
theorem conjAut_Xpow_eq_neg (α : ℕ) {e : ℕ} (he0 : 0 < e) (heα : e < 2 ^ α) :
    conjAut α (Xpow (powTwoCyclotomic (R := R) α) e)
      = - Xpow (powTwoCyclotomic (R := R) α) (2 ^ α - e) := by
  have hc : conjExp α + 1 = 2 ^ (α + 1) := Nat.sub_add_cancel Nat.one_le_two_pow
  have h2 : (2 : ℕ) ^ (α + 1) = 2 * 2 ^ α := by rw [pow_succ]; ring
  rw [conjAut_Xpow]
  have hper : (e * conjExp α) % 2 ^ (α + 1) = (2 ^ α + (2 ^ α - e)) % 2 ^ (α + 1) := by
    have harith : 2 ^ α + (2 ^ α - e) = 2 ^ (α + 1) - e := by omega
    rw [harith]
    have hmod : e * conjExp α ≡ 2 ^ (α + 1) - e [MOD 2 ^ (α + 1)] := by
      apply Nat.ModEq.add_right_cancel' e
      rw [Nat.sub_add_cancel (by omega : e ≤ 2 ^ (α + 1))]
      have hsum : e * conjExp α + e = e * 2 ^ (α + 1) := by rw [← hc]; ring
      rw [hsum]
      exact (Nat.modEq_zero_iff_dvd.mpr ⟨e, by ring⟩).trans
        (Nat.modEq_zero_iff_dvd.mpr (dvd_refl _)).symm
    exact hmod
  rw [Xpow_congr_mod α hper, Xpow_add, Xpow_natDegree, neg_one_mul]

/-- **Full coefficient formula for the basis element `v_j`.** For every position `p < d`, the
`p`-th coefficient of `v_j = X^{(d/2k)·j} + σ_{-1}(X^{(d/2k)·j})` is: `2` at `p = 0` when `j = 0`;
otherwise `+1` at `p = (d/2k)·j`, `-1` at the complementary position `p = d - (d/2k)·j`, and `0`
elsewhere. This extends `vElt_coeff` (which only covers the positions `(d/2k)·s`) to all positions,
pinning down the *support* of `v_j` — at most two nonzero coefficients. -/
theorem vElt_coeff_full (α κ : ℕ) (hκ : κ + 1 ≤ α) (j : Fin (2 ^ κ)) {p : ℕ} (hp : p < 2 ^ α) :
    (vElt α κ hκ j).val.1.coeff p
      = if (j : ℕ) = 0 then (if p = 0 then (2 : R) else 0)
        else if p = 2 ^ (α - κ - 1) * (j : ℕ) then 1
             else if p = 2 ^ α - 2 ^ (α - κ - 1) * (j : ℕ) then -1 else 0 := by
  have hα : 1 ≤ α := by omega
  have hhalf : (2 : ℕ) ^ (α - 1) = 2 ^ (α - κ - 1) * 2 ^ κ := by rw [← pow_add]; congr 1; omega
  have hd2 : (2 : ℕ) ^ α = 2 * 2 ^ (α - 1) := by rw [← pow_succ']; congr 1; omega
  rw [vElt_coe, Rq.add_val, CPolynomial.coeff_add]
  set e := 2 ^ (α - κ - 1) * (j : ℕ) with he_def
  have hej : e < 2 ^ (α - 1) := by
    rw [he_def, hhalf]; exact mul_lt_mul_of_pos_left j.isLt (by positivity)
  have hejα : e < 2 ^ α := by omega
  rw [Xpow_coeff_of_lt α hejα p]
  by_cases hj0 : (j : ℕ) = 0
  · have he0 : e = 0 := by rw [he_def, hj0, Nat.mul_zero]
    rw [if_pos hj0, he0, conjAut_Xpow, Nat.zero_mul, Xpow_coeff_of_lt α (by positivity) p]
    split_ifs with h <;> norm_num
  · have hepos : 0 < e := by
      rw [he_def]; exact Nat.mul_pos (by positivity) (Nat.pos_of_ne_zero hj0)
    rw [if_neg hj0, conjAut_Xpow_eq_neg α hepos hejα, Rq.neg_val, CPolynomial.coeff_neg,
      Xpow_coeff_of_lt α (by omega : 2 ^ α - e < 2 ^ α) p]
    split_ifs with h1 h2 <;> first | (exfalso; omega) | ring

/-- Right-multiplying a (folded or unfolded) monomial by `X^e` adds `e` to the exponent:
`(c·X^k)·X^e = c·X^{k+e}` in `R_q`. -/
theorem mk_monomial_mul_Xpow (α k e : ℕ) (c : R) :
    Rq.mk (powTwoCyclotomic (R := R) α) (CompPoly.CPolynomial.monomial k c)
        * Xpow (powTwoCyclotomic α) e
      = Rq.mk (powTwoCyclotomic α) (CompPoly.CPolynomial.monomial (k + e) c) := by
  rw [mk_monomial_eq, mk_monomial_eq, Xpow_add]; ring

/-- **Full coefficient of a (possibly high-degree) scaled monomial.** For `p < d`, the `p`-th
coefficient of the reduced `c·X^m` is `(-1)^{m/d}·c` at the folded position `p = m mod d`, and `0`
elsewhere — the sign records how many times the exponent wrapped past `X^d = -1`. -/
theorem mk_monomial_coeff_full (α m : ℕ) (c : R) (p : ℕ) :
    (Rq.mk (powTwoCyclotomic (R := R) α) (CompPoly.CPolynomial.monomial m c)).1.coeff p
      = if p = m % 2 ^ α then (-1 : R) ^ (m / 2 ^ α) * c else 0 := by
  have hmod : m % 2 ^ α < 2 ^ α := Nat.mod_lt _ (by positivity)
  rw [mk_monomial_fold]
  rcases Nat.even_or_odd (m / 2 ^ α) with he | ho
  · rw [he.neg_one_pow, _root_.one_mul, mk_monomial_coeff_lt α hmod]
    simp [he.neg_one_pow]
  · rw [ho.neg_one_pow, neg_one_mul, Rq.neg_val, CPolynomial.coeff_neg,
      mk_monomial_coeff_lt α hmod, ho.neg_one_pow]
    split_ifs <;> ring

/-- **Coefficient of an `X^e`-shift of a reduced element.** For `e < d`, `p < d` and any `x : R_q`,
the `p`-th coefficient of `x·X^e` is the `(p-e)`-th coefficient of `x` (no wrap, `e ≤ p`), or minus
the `(p+d-e)`-th coefficient (one wrap past `X^d = -1`, `p < e`). This is the only place the proof
needs the ring's multiplication; everything downstream is coefficient bookkeeping. -/
theorem Xpow_mul_coeff (α e : ℕ) (he : e < 2 ^ α) (x : Rq (powTwoCyclotomic (R := R) α))
    {p : ℕ} (hp : p < 2 ^ α) :
    (x * Xpow (powTwoCyclotomic α) e).1.coeff p
      = if e ≤ p then x.1.coeff (p - e) else - x.1.coeff (p + 2 ^ α - e) := by
  have hexp : x = ∑ k ∈ Finset.range (2 ^ α),
      Rq.mk (powTwoCyclotomic α) (CompPoly.CPolynomial.monomial k (x.1.coeff k)) := by
    conv_lhs => rw [← galoisAut_one_eq α x]
    rw [galoisAut_eq_sum]
    simp only [mul_one, powTwoCyclotomic_natDegree]
  conv_lhs => rw [hexp, Finset.sum_mul, ← Rq.coeffHom_apply, map_sum]
  simp only [Rq.coeffHom_apply, mk_monomial_mul_Xpow, mk_monomial_coeff_full]
  by_cases hep : e ≤ p
  · rw [if_pos hep, Finset.sum_eq_single (p - e)]
    · have h1 : p - e + e = p := by omega
      rw [h1, Nat.mod_eq_of_lt hp, Nat.div_eq_of_lt hp, pow_zero, _root_.one_mul, if_pos rfl]
    · intro k hk hkne
      rw [Finset.mem_range] at hk
      rw [if_neg]
      intro hpk
      rcases lt_or_ge (k + e) (2 ^ α) with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at hpk; exact hkne (by omega)
      · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at hpk; omega
    · intro h; exact absurd (Finset.mem_range.mpr (by omega : p - e < 2 ^ α)) h
  · rw [if_neg hep, Finset.sum_eq_single (p + 2 ^ α - e)]
    · have h1 : p + 2 ^ α - e + e = p + 2 ^ α := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hp, Nat.add_div_right _ (by positivity),
        Nat.div_eq_of_lt hp, _root_.zero_add, pow_one, neg_one_mul, if_pos rfl]
    · intro k hk hkne
      rw [Finset.mem_range] at hk
      rw [if_neg]
      intro hpk
      rcases lt_or_ge (k + e) (2 ^ α) with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at hpk; omega
      · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at hpk; exact hkne (by omega)
    · intro h; exact absurd (Finset.mem_range.mpr (by omega : p + 2 ^ α - e < 2 ^ α)) h

end Support

/-- A `CPolynomial` coefficient past the stored `size` is `0` (`coeff` reads `Array.getD … 0`). -/
theorem coeff_eq_zero_of_size_le {S : Type*} [Zero S] (cp : CompPoly.CPolynomial S) {pos : ℕ}
    (h : cp.size ≤ pos) : cp.coeff pos = 0 := by
  change cp.val.getD pos 0 = 0
  unfold Array.getD
  split_ifs with hh
  · exact absurd hh (Nat.not_lt.mpr h)
  · rfl

/-- **Support of a fixed element (Eq. 7).** Every `x ∈ R_q^H` has its nonzero coefficients on
multiples of `d/2k = 2^{α-κ-1}`: for `p < d` with `2^{α-κ-1} ∤ p`, `x.1.coeff p = 0`. This comes
from the symmetric `vElt` basis (`fixedBasisMap` is surjective by `card_fixedSubring_eq`), each of
whose elements is supported — by `vElt_coeff_full` — on the two multiples `(d/2k)·s` and
`d − (d/2k)·s` of `2^{α-κ-1}`. -/
theorem fixedSubring_coeff_eq_zero (α κ : ℕ) (h2 : (2 : ZMod q) ≠ 0) (hk : 2 * 2 ^ κ ∣ 2 ^ α)
    (x : fixedSubring (R := ZMod q) α (2 ^ κ)) {p : ℕ} (hp : p < 2 ^ α)
    (hdvd : ¬ (2 ^ (α - κ - 1) ∣ p)) :
    (x : Rq (powTwoCyclotomic (R := ZMod q) α)).1.coeff p = 0 := by
  have hκ : κ + 1 ≤ α := succ_le_of_two_mul_two_pow_dvd hk
  have hbij : Function.Bijective (fixedBasisMap q α κ hκ) := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨fixedBasisMap_injective q α κ h2 hκ, by
      rw [Fintype.card_fun, Fintype.card_fin, card_fixedSubring_eq q α κ h2 hk]⟩
  obtain ⟨c, hc⟩ := hbij.surjective x
  set D : fixedSubring (R := ZMod q) α (2 ^ κ) →+ ZMod q :=
    (Rq.coeffHom (powTwoCyclotomic (R := ZMod q) α) p).comp
      (fixedSubring (R := ZMod q) α (2 ^ κ)).subtype.toAddMonoidHom with hD
  change D x = 0
  rw [← hc, fixedBasisMap, map_sum]
  refine Finset.sum_eq_zero (fun s _ => ?_)
  rw [map_nsmul]
  change (c s).val • (vElt α κ hκ s).val.1.coeff p = _
  rw [vElt_coeff_full α κ hκ s hp]
  have hdvd2 : 2 ^ (α - κ - 1) ∣ 2 ^ α := pow_dvd_pow 2 (by omega)
  have hz : (if (s : ℕ) = 0 then (if p = 0 then (2 : ZMod q) else 0)
      else if p = 2 ^ (α - κ - 1) * (s : ℕ) then 1
           else if p = 2 ^ α - 2 ^ (α - κ - 1) * (s : ℕ) then -1 else 0) = 0 := by
    split_ifs with h1 h2 h3 h4
    · exact absurd (h2 ▸ dvd_zero _) hdvd
    · rfl
    · exact absurd ⟨_, h3⟩ hdvd
    · exact absurd (h4 ▸ Nat.dvd_sub hdvd2 ⟨_, rfl⟩) hdvd
    · rfl
  rw [hz, smul_zero]

set_option maxHeartbeats 1000000 in
-- The final assembly chains many `omega`/`rw` steps over the double sum `ψ(a) = Σ_j a_j·X^{…}`,
-- exceeding the default heartbeat budget.
/-- **Hachi [NOZ26, §3, Lemma 6]: `‖ψ(a)‖∞ ≤ 2β`.** If every entry of the vector
`a : (R_q^H)^{d/k}` has centered coefficient `ℓ∞`-norm at most `β` (i.e. `‖a‖∞ ≤ β` in the
`mod± q` convention of [NOZ26, §2.1]), then the packed ring element `ψ(a) ∈ R_q` satisfies
`‖ψ(a)‖∞ ≤ 2β`.

The hypotheses are the standing assumptions of [NOZ26, §3]: `k = 2^κ` divides `d/2`
(`2·2^κ ∣ 2^α`) and `q` is odd (`(2 : ZMod q) ≠ 0`; the paper assumes `q ≡ 5 (mod 8)`, of
which only oddness is needed here).

The paper proves this "directly from the explicit formula in Equation (9)"; the formal proof
is index/sign bookkeeping over the monomial toolkit, in four steps whose supporting lemmas are
proved above this theorem:

1. *Support of a fixed element (Eq. 7).* `fixedBasisMap` is injective and, by
   `card_fixedSubring_eq`, surjective, so every `x ∈ R_q^H` is `Σ_s n_s • vElt s`;
   `vElt_coeff_full` pins each `vElt s` to the two positions `(d/2k)·s` and `d − (d/2k)·s`.
   Hence `fixedSubring_coeff_eq_zero`: `x.coeff p = 0` whenever `2^{α-κ-1} ∤ p`.

2. *Coefficient of a shifted entry.* `Xpow_mul_coeff`: for `e, p < d`, `(x · X^e).coeff p` is
   `± x.coeff ((p − e) mod d)` (sign from `X^d = -1`) — the only step using ring multiplication.

3. *At most two contributions per position.* `packExp j ≡ j (mod d/2k)` on both halves
   (`d/2 = k·(d/2k) ≡ 0`), so for each `p` exactly one first-half index `j₁` and one
   second-half index `j₂` contribute to `ψ(a).coeff p`; all other summands vanish by step 1.

4. *Conclude with the balanced-representative triangle inequality.*
   `ZMod.natAbs_valMinAbs_add_le` and `ZMod.natAbs_valMinAbs_neg` give
   `|±c₁ ± c₂|± ≤ |c₁|± + |c₂|± ≤ β + β`, using `ha` at the two contributing positions. -/
theorem cInfNorm_psi_le (α κ : ℕ) (h2 : (2 : ZMod q) ≠ 0) (hk : 2 * 2 ^ κ ∣ 2 ^ α) {β : ℕ}
    (a : Fin (2 ^ α / 2 ^ κ) → fixedSubring (R := ZMod q) α (2 ^ κ))
    (ha : (zmodCenteredView q).vecCInfNorm
      (fun i => ((a i : Rq (powTwoCyclotomic (R := ZMod q) α))).1) ≤ β) :
    (zmodCenteredView q).cInfNorm (psi α (2 ^ κ) a).1 ≤ 2 * β := by
  have hκ : κ + 1 ≤ α := succ_le_of_two_mul_two_pow_dvd hk
  have hM0 : 0 < 2 ^ (α - κ - 1) := by positivity
  have hMd : 2 ^ (α - κ - 1) ∣ 2 ^ α := pow_dvd_pow 2 (by omega)
  have hMle : 2 ^ (α - κ - 1) ≤ 2 ^ (α - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hH : (2 : ℕ) ^ (α - 1) = 2 ^ κ * 2 ^ (α - κ - 1) := by rw [← pow_add]; congr 1; omega
  have hd2 : (2 : ℕ) ^ α = 2 * 2 ^ (α - 1) := by rw [← pow_succ']; congr 1; omega
  have hN : 2 ^ α / 2 ^ κ = 2 * 2 ^ (α - κ - 1) := by
    have hfac : (2 : ℕ) ^ κ * (2 * 2 ^ (α - κ - 1)) = 2 ^ α := by
      rw [← Nat.mul_assoc, show (2 : ℕ) ^ κ * 2 = 2 ^ (κ + 1) from by rw [pow_succ], ← pow_add]
      congr 1; omega
    rw [← hfac, Nat.mul_div_cancel_left _ (by positivity : 0 < 2 ^ κ)]
  have hMM : 2 ^ α / (2 * 2 ^ κ) = 2 ^ (α - κ - 1) := by
    rw [show 2 * 2 ^ κ = 2 ^ (κ + 1) from by rw [pow_succ]; ring,
      Nat.pow_div (by omega) (by norm_num), show α - (κ + 1) = α - κ - 1 from by omega]
  have hpackExp_lt : ∀ j : Fin (2 ^ α / 2 ^ κ), packExp α (2 ^ κ) (j : ℕ) < 2 ^ α := by
    intro j
    have hj : (j : ℕ) < 2 * 2 ^ (α - κ - 1) := hN ▸ j.isLt
    unfold packExp; rw [hMM]; split_ifs with h <;> omega
  have hpackExp_mod : ∀ j : Fin (2 ^ α / 2 ^ κ),
      packExp α (2 ^ κ) (j : ℕ) % 2 ^ (α - κ - 1) = (j : ℕ) % 2 ^ (α - κ - 1) := by
    intro j
    have hj : (j : ℕ) < 2 * 2 ^ (α - κ - 1) := hN ▸ j.isLt
    unfold packExp; rw [hMM]
    split_ifs with h
    · rfl
    · rw [hH, Nat.add_comm (2 ^ κ * 2 ^ (α - κ - 1)) _, Nat.add_mul_mod_self_right,
        ← Nat.mod_eq_sub_mod (by omega : 2 ^ (α - κ - 1) ≤ (j : ℕ))]
  have hbound : ∀ (i : Fin (2 ^ α / 2 ^ κ)) (pos : ℕ),
      (ZMod.valMinAbs ((a i : Rq (powTwoCyclotomic (R := ZMod q) α)).1.coeff pos)).natAbs ≤ β := by
    intro i pos
    have hv := ha
    rw [CenteredCoeffView.vecCInfNorm] at hv
    have hi : (Finset.range ((a i : Rq (powTwoCyclotomic (R := ZMod q) α)).1).size).sup
        ((zmodCenteredView q).absCoeff (a i : Rq (powTwoCyclotomic (R := ZMod q) α)).1) ≤ β := by
      rw [← CenteredCoeffView.cInfNorm]
      exact le_trans (Finset.le_sup (f := fun i => (zmodCenteredView q).cInfNorm
        ((a i : Rq (powTwoCyclotomic (R := ZMod q) α)).1)) (Finset.mem_univ i)) hv
    by_cases hpos : pos < ((a i : Rq (powTwoCyclotomic (R := ZMod q) α)).1).size
    · exact le_trans (Finset.le_sup (f := (zmodCenteredView q).absCoeff
        (a i : Rq (powTwoCyclotomic (R := ZMod q) α)).1) (Finset.mem_range.mpr hpos)) hi
    · rw [coeff_eq_zero_of_size_le _ (by omega), ZMod.valMinAbs_zero]; exact Nat.zero_le _
  rw [CenteredCoeffView.cInfNorm]
  apply Finset.sup_le
  intro p _
  change (ZMod.valMinAbs ((psi α (2 ^ κ) a).1.coeff p)).natAbs ≤ 2 * β
  by_cases hp : p < 2 ^ α
  · have hr : p % 2 ^ (α - κ - 1) < 2 ^ (α - κ - 1) := Nat.mod_lt _ hM0
    set j₁ : Fin (2 ^ α / 2 ^ κ) := ⟨p % 2 ^ (α - κ - 1), by omega⟩ with hj1
    set j₂ : Fin (2 ^ α / 2 ^ κ) := ⟨2 ^ (α - κ - 1) + p % 2 ^ (α - κ - 1), by omega⟩ with hj2
    set t : Fin (2 ^ α / 2 ^ κ) → ZMod q := fun j =>
      ((a j : Rq (powTwoCyclotomic (R := ZMod q) α))
        * Xpow (powTwoCyclotomic α) (packExp α (2 ^ κ) (j : ℕ))).1.coeff p with ht_def
    have hsum : (psi α (2 ^ κ) a).1.coeff p = ∑ j, t j := by
      unfold psi; rw [← Rq.coeffHom_apply, map_sum]; simp only [ht_def, Rq.coeffHom_apply]
    have hjne : j₁ ≠ j₂ := by simp only [hj1, hj2, Ne, Fin.mk.injEq]; omega
    have hwit : ∀ j : Fin (2 ^ α / 2 ^ κ),
        p % 2 ^ (α - κ - 1) = (j : ℕ) % 2 ^ (α - κ - 1) → j = j₁ ∨ j = j₂ := by
      intro j heq
      have hjlt : (j : ℕ) < 2 * 2 ^ (α - κ - 1) := hN ▸ j.isLt
      have hv1 : (j₁ : ℕ) = p % 2 ^ (α - κ - 1) := rfl
      have hv2 : (j₂ : ℕ) = 2 ^ (α - κ - 1) + p % 2 ^ (α - κ - 1) := rfl
      rcases lt_or_ge (j : ℕ) (2 ^ (α - κ - 1)) with hjl | hjg
      · left; apply Fin.ext; rw [hv1]; rw [Nat.mod_eq_of_lt hjl] at heq; omega
      · right; apply Fin.ext; rw [hv2]
        have hjm : (j : ℕ) % 2 ^ (α - κ - 1) = (j : ℕ) - 2 ^ (α - κ - 1) := by
          rw [Nat.mod_eq_sub_mod hjg, Nat.mod_eq_of_lt (by omega)]
        rw [hjm] at heq; omega
    have hzero : ∀ j : Fin (2 ^ α / 2 ^ κ), j ∉ ({j₁, j₂} : Finset _) → t j = 0 := by
      intro j hj
      have hnotwit : p % 2 ^ (α - κ - 1) ≠ (j : ℕ) % 2 ^ (α - κ - 1) := by
        intro heq
        rcases hwit j heq with h | h <;> exact hj (by rw [h]; simp)
      simp only [ht_def]
      rw [Xpow_mul_coeff α (packExp α (2 ^ κ) (j : ℕ)) (hpackExp_lt j)
        (a j : Rq (powTwoCyclotomic (R := ZMod q) α)) hp]
      split_ifs with hle
      · apply fixedSubring_coeff_eq_zero q α κ h2 hk (a j) (by omega)
        intro hdvd
        apply hnotwit
        have hmeq : packExp α (2 ^ κ) (j : ℕ) % 2 ^ (α - κ - 1) = p % 2 ^ (α - κ - 1) :=
          (Nat.modEq_iff_dvd' hle).mpr hdvd
        rw [hpackExp_mod j] at hmeq; omega
      · rw [fixedSubring_coeff_eq_zero q α κ h2 hk (a j) (by omega) (by
          intro hdvd
          apply hnotwit
          have hle2 : packExp α (2 ^ κ) (j : ℕ) ≤ p + 2 ^ α := by have := hpackExp_lt j; omega
          have hmeq : packExp α (2 ^ κ) (j : ℕ) % 2 ^ (α - κ - 1)
              = (p + 2 ^ α) % 2 ^ (α - κ - 1) := (Nat.modEq_iff_dvd' hle2).mpr hdvd
          have h2z : (2 : ℕ) ^ α % 2 ^ (α - κ - 1) = 0 := by
            rw [show (2 : ℕ) ^ α = 2 ^ (α - κ - 1) * 2 ^ (κ + 1) from by
              rw [← pow_add]; congr 1; omega, Nat.mul_mod_right]
          rw [hpackExp_mod j, Nat.add_mod, h2z, Nat.add_zero, Nat.mod_mod] at hmeq; omega),
          neg_zero]
    have ht_bound : ∀ j, (ZMod.valMinAbs (t j)).natAbs ≤ β := by
      intro j
      simp only [ht_def]
      rw [Xpow_mul_coeff α (packExp α (2 ^ κ) (j : ℕ)) (hpackExp_lt j)
        (a j : Rq (powTwoCyclotomic (R := ZMod q) α)) hp]
      split_ifs
      · exact hbound j _
      · rw [ZMod.natAbs_valMinAbs_neg]; exact hbound j _
    have hpair : (psi α (2 ^ κ) a).1.coeff p = t j₁ + t j₂ := by
      rw [hsum, ← Finset.sum_subset (Finset.subset_univ {j₁, j₂}) (fun j _ hj => hzero j hj),
        Finset.sum_pair hjne]
    rw [hpair]
    calc (ZMod.valMinAbs (t j₁ + t j₂)).natAbs
        ≤ (ZMod.valMinAbs (t j₁) + ZMod.valMinAbs (t j₂)).natAbs :=
          ZMod.natAbs_valMinAbs_add_le _ _
      _ ≤ (ZMod.valMinAbs (t j₁)).natAbs + (ZMod.valMinAbs (t j₂)).natAbs := Int.natAbs_add_le _ _
      _ ≤ β + β := Nat.add_le_add (ht_bound j₁) (ht_bound j₂)
      _ = 2 * β := by ring
  · rw [coeff_eq_zero_of_le α (psi α (2 ^ κ) a) (by omega), ZMod.valMinAbs_zero]
    exact Nat.zero_le _

end ArkLib.Lattices.CyclotomicModulus
