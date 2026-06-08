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

@[simp] theorem galoisAut_zero (i : ℕ) : galoisAut Φ i 0 = 0 := by
  unfold galoisAut
  have : ∀ k ∈ range Φ.φ.natDegree,
      (monomial (k * i) ((0 : Rq Φ).1.coeff k) : CPolynomial R) = 0 := by
    intro k _
    rw [Rq.zero_val, CompPoly.CPolynomial.coeff_zero]
    exact CompPoly.CPolynomial.eq_zero_iff_coeff_zero.mpr
      (fun j => by rw [CompPoly.CPolynomial.coeff_monomial]; split_ifs <;> rfl)
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

/-! ## The semantic automorphism via Mathlib `aeval` -/

/-- The Mathlib `R`-algebra endomorphism of `Polynomial R` sending `X ↦ X^i` (i.e. `p ↦ p(X^i)`),
as a `RingHom`. -/
noncomputable def galoisAeval (i : ℕ) : Polynomial R →+* Polynomial R :=
  (Polynomial.aeval (Polynomial.X ^ i : Polynomial R)).toRingHom

omit [DecidableEq R] in
/-- Well-definedness on the power-of-two ring: `aeval (X^i)` maps the modulus ideal into itself
for odd `i`, since `X^{2^α} + 1 ∣ (X^{2^α})^i + 1`.

(Medium difficulty: `a + 1 ∣ a^i + 1` for odd `i` via `sub_dvd_pow_sub_pow a (-1) i` and
`Odd.neg_one_pow`. Sorried for now.) -/
theorem powTwo_galoisAeval_mem (α i : ℕ) (hi : Odd i) {p : Polynomial R}
    (hp : p ∈ (powTwoCyclotomic (R := R) α).modIdeal) :
    galoisAeval i p ∈ (powTwoCyclotomic (R := R) α).modIdeal := by
  sorry

/-- The **semantic Galois automorphism** `σ_i` on the quotient ring, obtained by descending the
Mathlib endomorphism `aeval (X^i)` along `Ideal.Quotient.lift`. A genuine `RingHom`. -/
noncomputable def galoisAutₛ (α i : ℕ) (hi : Odd i) :
    (powTwoCyclotomic (R := R) α).CyclotomicRing →+* (powTwoCyclotomic (R := R) α).CyclotomicRing :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk (powTwoCyclotomic (R := R) α).modIdeal).comp (galoisAeval i))
    (fun p hp => by
      rw [RingHom.comp_apply]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr (powTwo_galoisAeval_mem α i hi hp))

/-! ## Soundness bridge -/

/-- **Soundness**: the computable automorphism agrees with the semantic one under
`Rq.toQuotient`. This is the key bridge (Hachi [NOZ26, §3]); it lets all algebraic structure
(ring-hom laws, bijectivity) be proven on the Mathlib side and transported back.

(Hard: requires matching the monomial-remap-then-reduce against `aeval (X^i)` coefficientwise.
Sorried for now.) -/
theorem galoisAut_toQuotient (α i : ℕ) (hi : Odd i) (a : Rq (powTwoCyclotomic (R := R) α)) :
    (galoisAut (powTwoCyclotomic α) i a).toQuotient = galoisAutₛ α i hi a.toQuotient := by
  sorry

/-! ## The computable automorphism bundled as a `RingHom` -/

/-- The computable Galois automorphism action bundled as a `RingHom` on `Rq`. The additive
structure is proven directly; multiplicativity and unitality are transported from the semantic
`galoisAutₛ` via `galoisAut_toQuotient` (currently sorried). -/
noncomputable def galoisRingHom (α i : ℕ) (hi : Odd i) :
    Rq (powTwoCyclotomic (R := R) α) →+* Rq (powTwoCyclotomic (R := R) α) where
  toFun := galoisAut (powTwoCyclotomic α) i
  map_one' := by sorry
  map_mul' := by sorry
  map_zero' := galoisAut_zero (powTwoCyclotomic α) i
  map_add' := galoisAut_add (powTwoCyclotomic α) i

@[simp] theorem galoisRingHom_apply (α i : ℕ) (hi : Odd i)
    (a : Rq (powTwoCyclotomic (R := R) α)) :
    galoisRingHom α i hi a = galoisAut (powTwoCyclotomic α) i a := rfl

end ArkLib.Lattices.CyclotomicModulus
