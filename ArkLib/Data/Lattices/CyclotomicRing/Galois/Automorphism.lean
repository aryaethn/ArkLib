/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.PowTwo

/-!
# Galois Automorphisms `σ_i : X ↦ X^i` of the Cyclotomic Ring

For the power-of-two cyclotomic ring `R_q = Z_q[X] / (X^{2^α} + 1)`, the Galois automorphisms
are the ring automorphisms `σ_i` induced by `X ↦ X^i` for `i` a unit modulo the conductor
`2d = 2^{α+1}` (equivalently, `i` odd). These are the maps used throughout Hachi [NOZ26, §3]
to identify the finite-field extensions inside `R_q`.

Following the project's two-layer discipline (cf. `CyclotomicRing/Basic.lean`):

* **Computable layer** (`galoisAut`): on a reduced representative `a = Σ_{k<d} a_k X^k`, the
  automorphism remaps each monomial `X^k ↦ X^{ki}` and reduces modulo `X^d + 1`. Since
  `X^d = -1`, this is a *signed coefficient permutation*, here realised directly as
  `Rq.mk Φ (Σ_k monomial (k·i) a_k)` (reduction handles the `X^{ki}`-folding). Fully
  computable / `#eval`-able.
* **Semantic layer** (`galoisAutₛ`): the Mathlib `R`-algebra endomorphism `aeval (X^i)` of
  `Polynomial R`, descended to the quotient `Polynomial R ⧸ (X^d+1)` via
  `Ideal.Quotient.lift`. This is a genuine `RingHom` for free; well-definedness needs
  `aeval (X^i)` to fix the ideal, which holds for `i` odd because `X^d + 1 ∣ X^{di} + 1`.
* **Soundness bridge** (`galoisAut_toQuotient`): the computable map agrees with the semantic
  one under `Rq.toQuotient`. This is the load-bearing (and hardest) lemma; it transfers the
  `RingHom`/bijectivity structure from the semantic side back to the computable map.

## Main definitions

* `galoisAut Φ i` — the computable automorphism action `Rq Φ → Rq Φ`.
* `galoisAutₛ α i hi` — the semantic automorphism `RingHom` on the quotient (`i` odd).
* `galoisRingHom α i hi` — the computable action bundled as a `RingHom`.

## References

* [Lyubashevsky, V., Nguyen, N. K., and Plançon, M., *Lattice-Based Zero-Knowledge Proofs*][LNP22]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open Polynomial CompPoly CompPoly.CPolynomial Finset

namespace ArkLib.Lattices.CyclotomicModulus

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]

/-! ## `Rq.mk` is additive (helper for the computable layer) -/

variable (Φ : CyclotomicModulus R) [IsCyclotomic Φ]

omit [DecidableEq R] in
/-- `Rq.mk` commutes with addition: reduction is additive in the quotient. -/
theorem Rq.mk_add (p q : CPolynomial R) : Rq.mk Φ (p + q) = Rq.mk Φ p + Rq.mk Φ q := by
  apply Rq.toQuotient_injective Φ
  simp only [show ∀ x y : Rq Φ, Rq.toQuotient Φ (x + y) = Rq.toQuotient Φ x + Rq.toQuotient Φ y
        from fun x y => map_add (Rq.toQuotientHom Φ) x y,
      Rq.toQuotient_mk, map_add]

omit [DecidableEq R] in
/-- `Rq.mk` commutes with finite sums. -/
theorem Rq.mk_sum {ι : Type*} (s : Finset ι) (f : ι → CPolynomial R) :
    Rq.mk Φ (∑ k ∈ s, f k) = ∑ k ∈ s, Rq.mk Φ (f k) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]; rfl
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Rq.mk_add, ih]

/-! ## The computable automorphism `galoisAut` -/

/-- The **computable Galois automorphism action** `σ_i : Rq Φ → Rq Φ`, `X^k ↦ X^{ki}`.

On a reduced representative `a = Σ_{k<d} a_k X^k`, it forms `Σ_k a_k X^{ki}` and reduces modulo
the modulus; since `X^d = -1`, this is the signed coefficient permutation. It is a genuine ring
automorphism only when `i` is a unit modulo the conductor (`i` odd, for the power-of-two ring);
the bare action is defined for all `i`. -/
def galoisAut (i : ℕ) (a : Rq Φ) : Rq Φ :=
  Rq.mk Φ (∑ k ∈ range Φ.φ.natDegree, monomial (k * i) (a.1.coeff k))

/-- A monomial with zero coefficient is the zero polynomial. -/
private theorem monomial_eq_zero (n : ℕ) : (monomial n (0 : R) : CPolynomial R) = 0 :=
  CompPoly.CPolynomial.eq_zero_iff_coeff_zero.mpr
    (fun j => by rw [CompPoly.CPolynomial.coeff_monomial]; split_ifs <;> rfl)

@[simp] theorem galoisAut_zero (i : ℕ) : galoisAut Φ i 0 = 0 := by
  unfold galoisAut
  have : ∀ k ∈ range Φ.φ.natDegree,
      (monomial (k * i) ((0 : Rq Φ).1.coeff k) : CPolynomial R) = 0 := by
    intro k _
    rw [Rq.zero_val, CompPoly.CPolynomial.coeff_zero, monomial_eq_zero]
  rw [Finset.sum_congr rfl this, Finset.sum_const_zero]
  rfl

/-- `galoisAut` is additive. Follows from additivity of coefficient extraction, of `monomial`
in its coefficient, of finite sums, and of `Rq.mk`. -/
theorem galoisAut_add (i : ℕ) (a b : Rq Φ) :
    galoisAut Φ i (a + b) = galoisAut Φ i a + galoisAut Φ i b := by
  unfold galoisAut
  rw [← Rq.mk_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Rq.add_val, CompPoly.CPolynomial.coeff_add, CompPoly.CPolynomial.monomial_add]

omit [DecidableEq R] in
/-- The modulus polynomial of `powTwoCyclotomic α`, as a Mathlib polynomial. -/
theorem powTwoCyclotomic_toPoly (α : ℕ) :
    (powTwoCyclotomic (R := R) α).φ.toPoly = Polynomial.X ^ (2 ^ α) + 1 := by
  change (CompPoly.CPolynomial.X ^ (2 ^ α) + 1 : CPolynomial R).toPoly = _
  rw [toPoly_add, toPoly_pow, toPoly_X, toPoly_one]

omit [DecidableEq R] in
/-- **(S0)** The ring dimension: `natDegree` of the power-of-two modulus is `2^α`. -/
theorem powTwoCyclotomic_natDegree (α : ℕ) :
    (powTwoCyclotomic (R := R) α).φ.natDegree = 2 ^ α := by
  rw [CompPoly.CPolynomial.natDegree_toPoly, powTwoCyclotomic_toPoly,
    show (Polynomial.X ^ 2 ^ α + 1 : Polynomial R) = Polynomial.X ^ 2 ^ α + Polynomial.C 1 by
      rw [Polynomial.C_1], Polynomial.natDegree_X_pow_add_C]

omit [BEq R] [LawfulBEq R] [DecidableEq R] in
/-- **(S3)** Coefficient bridge: the Mathlib and `CPolynomial` coefficients agree. -/
theorem coeff_toPoly (p : CPolynomial R) (k : ℕ) : p.toPoly.coeff k = p.coeff k :=
  CompPoly.CPolynomial.Raw.coeff_toPoly

omit [DecidableEq R] in
/-- **(S4)** A reduced representative has `natDegree` below the ring dimension. -/
theorem natDegree_val_toPoly_lt (α : ℕ) (a : Rq (powTwoCyclotomic (R := R) α)) :
    a.1.toPoly.natDegree < (powTwoCyclotomic (R := R) α).φ.natDegree := by
  rcases eq_or_ne a.1.toPoly 0 with h0 | hne
  · rw [h0, Polynomial.natDegree_zero, powTwoCyclotomic_natDegree]
    exact pow_pos (by norm_num) α
  · rw [CompPoly.CPolynomial.natDegree_toPoly]
    exact Polynomial.natDegree_lt_natDegree hne
      ((powTwoCyclotomic (R := R) α).degree_toPoly_lt_of_reduced a.2)

/-- `σ_i` fixes `1`, since only the constant term contributes (so in particular `σ_1` fixes it). -/
theorem galoisAut_map_one (α i : ℕ) : galoisAut (powTwoCyclotomic (R := R) α) i 1 = 1 := by
  have h2 : (0 : ℕ) < 2 ^ α := pow_pos (by norm_num) α
  have hpos : 0 < (powTwoCyclotomic (R := R) α).φ.natDegree := by
    rw [powTwoCyclotomic_natDegree]; exact h2
  have hone : (1 : Rq (powTwoCyclotomic (R := R) α)).1 = (1 : CPolynomial R) := by
    change (powTwoCyclotomic (R := R) α).reduce 1 = 1
    refine CyclotomicModulus.reduce_eq_self_of_degree_lt _ ?_
    rw [CompPoly.CPolynomial.toPoly_one, Polynomial.degree_one, powTwoCyclotomic_toPoly,
      ← Polynomial.C_1, Polynomial.degree_X_pow_add_C h2 (1 : R)]
    exact_mod_cast h2
  have hcoeff : ∀ k,
      (1 : Rq (powTwoCyclotomic (R := R) α)).1.coeff k = if k = 0 then (1 : R) else 0 :=
    fun k => by rw [hone]; exact CompPoly.CPolynomial.coeff_one k
  have hm : (monomial 0 (1 : R) : CPolynomial R) = 1 :=
    CompPoly.CPolynomial.eq_iff_coeff.mpr fun j => by
      rw [CompPoly.CPolynomial.coeff_monomial, CompPoly.CPolynomial.coeff_one]
  unfold galoisAut
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hpos)
        (fun k _ hk => by rw [hcoeff, if_neg hk, monomial_eq_zero]),
      hcoeff, if_pos rfl, Nat.zero_mul, hm]
  rfl

/-! ## The semantic automorphism via Mathlib `aeval` -/

/-- The Mathlib `R`-algebra endomorphism of `Polynomial R` sending `X ↦ X^i` (i.e. `p ↦ p(X^i)`),
as a `RingHom`. -/
noncomputable def galoisAeval (i : ℕ) : Polynomial R →+* Polynomial R :=
  (Polynomial.aeval (Polynomial.X ^ i : Polynomial R)).toRingHom

omit [BEq R] [LawfulBEq R] [DecidableEq R] in
@[simp] theorem galoisAeval_apply (i : ℕ) (p : Polynomial R) :
    galoisAeval i p = Polynomial.aeval (Polynomial.X ^ i : Polynomial R) p := rfl

omit [BEq R] [LawfulBEq R] [DecidableEq R] in
/-- **(S2)** `aeval (X^i)` sends a monomial `X^k·c` to `X^{ki}·c`. -/
theorem aeval_X_pow_monomial (i k : ℕ) (c : R) :
    (Polynomial.aeval (Polynomial.X ^ i : Polynomial R)) (Polynomial.monomial k c)
      = Polynomial.monomial (k * i) c := by
  rw [Polynomial.aeval_monomial, Polynomial.algebraMap_eq, ← pow_mul,
    Polynomial.C_mul_X_pow_eq_monomial, Nat.mul_comm]

omit [DecidableEq R] in
/-- Well-definedness on the power-of-two ring: `aeval (X^i)` maps the modulus ideal into itself
for odd `i`, since `X^{2^α} + 1 ∣ (X^{2^α})^i + 1`. -/
theorem powTwo_galoisAeval_mem (α i : ℕ) (hi : Odd i) {p : Polynomial R}
    (hp : p ∈ (powTwoCyclotomic (R := R) α).modIdeal) :
    galoisAeval i p ∈ (powTwoCyclotomic (R := R) α).modIdeal := by
  -- `galoisAeval i X = X ^ i`
  have hX : galoisAeval i (Polynomial.X : Polynomial R) = Polynomial.X ^ i := by
    simp [galoisAeval]
  -- `aeval (X^i)` sends the modulus to `(X^{2^α})^i + 1`, divisible by `X^{2^α} + 1`.
  have hdvd : (powTwoCyclotomic (R := R) α).φ.toPoly ∣
      galoisAeval i (powTwoCyclotomic (R := R) α).φ.toPoly := by
    rw [powTwoCyclotomic_toPoly, map_add, map_pow, map_one, hX,
      show ((Polynomial.X : Polynomial R) ^ i) ^ 2 ^ α = (Polynomial.X ^ 2 ^ α) ^ i by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
    have hd := sub_dvd_pow_sub_pow (Polynomial.X ^ 2 ^ α : Polynomial R) (-1) i
    rwa [Odd.neg_one_pow hi, sub_neg_eq_add, sub_neg_eq_add] at hd
  simp only [modIdeal, Ideal.mem_span_singleton] at hp ⊢
  obtain ⟨c, rfl⟩ := hp
  rw [map_mul]
  exact hdvd.mul_right _

/-- The **semantic Galois automorphism** `σ_i` on the quotient ring, obtained by descending the
Mathlib endomorphism `aeval (X^i)` along `Ideal.Quotient.lift`. A genuine `RingHom`. -/
noncomputable def galoisAutₛ (α i : ℕ) (hi : Odd i) :
    (powTwoCyclotomic (R := R) α).CyclotomicRing →+* (powTwoCyclotomic (R := R) α).CyclotomicRing :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk (powTwoCyclotomic (R := R) α).modIdeal).comp (galoisAeval i))
    (fun p hp => by
      rw [RingHom.comp_apply]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr (powTwo_galoisAeval_mem α i hi hp))

omit [DecidableEq R] in
/-- **(S1)** The semantic automorphism on a lifted element: `galoisAutₛ` applied to
`a.toQuotient` is the class of `aeval (X^i)` applied to the underlying polynomial. -/
theorem galoisAutₛ_toQuotient (α i : ℕ) (hi : Odd i) (a : Rq (powTwoCyclotomic (R := R) α)) :
    galoisAutₛ α i hi a.toQuotient
      = Ideal.Quotient.mk _
          (Polynomial.aeval (Polynomial.X ^ i : Polynomial R) a.1.toPoly) := by
  rw [Rq.toQuotient, quotientHom_apply, galoisAutₛ, Ideal.Quotient.lift_mk,
    RingHom.comp_apply, galoisAeval_apply]

/-! ## Soundness bridge -/

/-- **(S5)** The core polynomial identity behind soundness: the monomial-remapped sum (before
reduction) equals `aeval (X^i)` of the underlying polynomial. Both sides are
`∑_{k<d} X^{ki}·a_k`. -/
theorem galoisAut_sum_toPoly_eq_aeval (α i : ℕ) (a : Rq (powTwoCyclotomic (R := R) α)) :
    (∑ k ∈ range (powTwoCyclotomic (R := R) α).φ.natDegree,
        CompPoly.CPolynomial.monomial (k * i) (a.1.coeff k)).toPoly
      = Polynomial.aeval (Polynomial.X ^ i : Polynomial R) a.1.toPoly := by
  rw [toPoly_sum,
    show a.1.toPoly = ∑ k ∈ range (powTwoCyclotomic (R := R) α).φ.natDegree,
        Polynomial.monomial k (a.1.toPoly.coeff k)
      from a.1.toPoly.as_sum_range' _ (natDegree_val_toPoly_lt α a),
    map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [toPoly_monomial, aeval_X_pow_monomial, coeff_toPoly]

/-- **(S6) Soundness**: the computable automorphism agrees with the semantic one under
`Rq.toQuotient`. This is the key bridge (Hachi [NOZ26, §3]); it lets all algebraic structure
(ring-hom laws, bijectivity) be proven on the Mathlib side and transported back. -/
theorem galoisAut_toQuotient (α i : ℕ) (hi : Odd i) (a : Rq (powTwoCyclotomic (R := R) α)) :
    (galoisAut (powTwoCyclotomic α) i a).toQuotient = galoisAutₛ α i hi a.toQuotient := by
  rw [galoisAut, Rq.toQuotient_mk, galoisAutₛ_toQuotient α i hi, quotientHom_apply]
  exact congrArg (Ideal.Quotient.mk _) (galoisAut_sum_toPoly_eq_aeval α i a)

/-- Multiplicativity of the computable automorphism, transported from `galoisAutₛ` (a `RingHom`)
through the soundness bridge. -/
theorem galoisAut_mul (α i : ℕ) (hi : Odd i) (a b : Rq (powTwoCyclotomic (R := R) α)) :
    galoisAut (powTwoCyclotomic α) i (a * b)
      = galoisAut (powTwoCyclotomic α) i a * galoisAut (powTwoCyclotomic α) i b := by
  apply Rq.toQuotient_injective (powTwoCyclotomic α)
  have hmul : ∀ x y : Rq (powTwoCyclotomic (R := R) α),
      (x * y).toQuotient = x.toQuotient * y.toQuotient :=
    fun x y => map_mul (Rq.toQuotientHom _) x y
  rw [galoisAut_toQuotient α i hi, hmul a b, map_mul,
    hmul (galoisAut (powTwoCyclotomic α) i a) (galoisAut (powTwoCyclotomic α) i b),
    galoisAut_toQuotient α i hi, galoisAut_toQuotient α i hi]

/-! ## The computable automorphism bundled as a `RingHom` -/

/-- The computable Galois automorphism action bundled as a `RingHom` on `Rq`. The additive
structure and unitality are proven directly; multiplicativity (`map_mul'`) is transported from
the semantic `galoisAutₛ` via the soundness bridge `galoisAut_toQuotient` (see `galoisAut_mul`). -/
noncomputable def galoisRingHom (α i : ℕ) (hi : Odd i) :
    Rq (powTwoCyclotomic (R := R) α) →+* Rq (powTwoCyclotomic (R := R) α) where
  toFun := galoisAut (powTwoCyclotomic α) i
  map_one' := galoisAut_map_one α i
  map_mul' := galoisAut_mul α i hi
  map_zero' := galoisAut_zero (powTwoCyclotomic α) i
  map_add' := galoisAut_add (powTwoCyclotomic α) i

@[simp] theorem galoisRingHom_apply (α i : ℕ) (hi : Odd i)
    (a : Rq (powTwoCyclotomic (R := R) α)) :
    galoisRingHom α i hi a = galoisAut (powTwoCyclotomic α) i a := rfl

end ArkLib.Lattices.CyclotomicModulus
