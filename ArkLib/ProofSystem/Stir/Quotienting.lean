/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter, Poulami Das (Least Authority)
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability
import CompPoly.Data.MvPolynomial.Notation
import CompPoly.Univariate.Lagrange
import CompPoly.Univariate.ToPoly.Impl

open Polynomial NNReal ReedSolomon ListDecodable

namespace Quotienting

variable {n : ℕ}
         {F : Type*} [Field F] [DecidableEq F]
         {ι : Finset F}

/-- Let `Ans : S → F`, `ansPoly(Ans, S)` is the unique interpolating polynomial of degree < |S|
    with `AnsPoly(s) = Ans(s)` for each s ∈ S.

    Note: For S=∅ we get Ans'(x) = 0 (the zero polynomial) -/
noncomputable def ansPoly (S : Finset F) (Ans : S → F) : Polynomial F :=
  Lagrange.interpolate S.attach (fun i => (i : F)) Ans

/-- VanishingPoly is the vanishing polynomial on S, i.e. the unique polynomial of degree |S|+1
    that is 0 at each s ∈ S and is not the zero polynomial. That is V(X) = ∏(s ∈ S) (X - s). -/
noncomputable def vanishingPoly (S : Finset F) : Polynomial F :=
  ∏ s ∈ S, (Polynomial.X - Polynomial.C s)

/-- Definition 4.2
  funcQuotient is the quotient function that outputs
  if x ∈ S,  Fill(x).
  else       (f(x) - Ans'(x)) / V(x).
  Note here that, V(x) = 0 ∀ x ∈ S, otherwise V(x) ≠ 0. -/
noncomputable def funcQuotient (f : ι → F) (S : Finset F) (Ans Fill : S → F) : ι → F :=
  fun x =>
    if hx : x.val ∈ S then Fill ⟨x.val, hx⟩ -- if x ∈ S,  Fill(x).
    else (f x - (ansPoly S Ans).eval x.val) / (vanishingPoly S).eval x.val

/-- Definition 4.3
  polyQuotient is the polynomial derived from the polynomials fPoly, Ans' and V, where
  Ans' is a polynomial s.t. Ans'(x) = fPoly(x) for x ∈ S, and
  V is the vanishing polynomial on S as before.
  Then, polyQuotient = (fPoly - Ans') / V, where
  polyQuotient.degree < (fPoly.degree - ι.card) -/
noncomputable def polyQuotient (S : Finset F) (fPoly : F[X]) : F[X] :=
    (fPoly - (ansPoly S (fun s => fPoly.eval s))) / (vanishingPoly S)

/-- We define the set disagreementSet(f,ι,S,Ans) as the set of all points x ∈ ι that lie in S
such that the Ans' disagrees with f, we have
disagreementSet := { x ∈ ι ∩ S ∧ AnsPoly x ≠ f x }. -/
noncomputable def disagreementSet (f : ι → F) (S : Finset F) (Ans : S → F) : Finset F :=
  Set.toFinset ({x : ι | x.val ∈ S ∧ (ansPoly S Ans).eval x.val ≠ f x}.image Subtype.val)

/-- Quotienting Lemma 4.4
  Let `f : ι → F` be a function, `degree` a degree parameter, `δ ∈ (0,1)` be a distance parameter
  `S` be a set with |S| < degree, `Ans, Fill : S → F`. Suppose for all `u ∈ Λ(code, f, δ)`,
  there exists `x : S`, such that `uPoly(x) ≠ Ans(x)` then
  `δᵣ(funcQuotient(f, S, Ans, Fill), code[ι, F, degree - |S|]) + |T|/|ι| > δ`,
  where T is the disagreementSet as defined above -/
lemma quotienting {degree : ℕ} {domain : ι ↪ F} [Nonempty ι]
  (S : Finset F) (hS_lt : S.card < degree) (r : F)
  (f : ι → F) (Ans Fill : S → F) (δ : ℝ≥0) (hδPos : δ > 0) (hδLt : δ < 1)
  (h : ∀ u : code domain degree, u.val ∈ (closeCodewordsRel ↑(code domain degree) f δ) →
    ∃ x : S, ((decodeLT u) : F[X]).eval x.val ≠ Ans x) :
    δᵣ((funcQuotient f S Ans Fill), (code domain (degree - S.card))) +
      ((disagreementSet f S Ans).card) / (ι.card) > δ := by
  sorry

/-- Computable version of `ansPoly`: the unique interpolating polynomial of degree `< |S|`
agreeing with `Ans` on `S`. Built on CompPoly's `CLagrange.interpolate`. -/
def cpolyAnsPoly (S : Finset F) (Ans : S → F) : CompPoly.CPolynomial F :=
  CompPoly.CPolynomial.CLagrange.interpolate S.attach (fun i => (i : F)) Ans

/-- Bridge lemma: `cpolyAnsPoly` and `ansPoly` agree under `toPoly`. -/
@[simp]
lemma cpolyAnsPoly_toPoly (S : Finset F) (Ans : S → F) :
    (cpolyAnsPoly S Ans).toPoly = ansPoly S Ans := by
  unfold cpolyAnsPoly ansPoly
  exact CompPoly.CPolynomial.CLagrange.cinterpolate_eq_interpolate

/-- Computable version of `vanishingPoly`: `∏ s ∈ S, (X - C s)`, built on CompPoly's
`CPolynomial`. -/
def cpolyVanishingPoly (S : Finset F) : CompPoly.CPolynomial F :=
  ∏ s ∈ S, (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C s)

/-- Bridge lemma: `cpolyVanishingPoly` and `vanishingPoly` agree under `toPoly`. -/
@[simp]
lemma cpolyVanishingPoly_toPoly (S : Finset F) :
    (cpolyVanishingPoly S).toPoly = vanishingPoly S := by
  unfold cpolyVanishingPoly vanishingPoly
  rw [CompPoly.CPolynomial.toPoly_prod]
  refine Finset.prod_congr rfl ?_
  intro s _
  rw [CompPoly.CPolynomial.toPoly_sub, CompPoly.CPolynomial.X_toPoly,
      CompPoly.CPolynomial.C_toPoly]

/-- Computable version of `funcQuotient`. Uses the cpoly versions of `ansPoly` and
`vanishingPoly` for the off-`S` branch; the on-`S` branch is identical to the Mathlib spec. -/
def cpolyFuncQuotient (f : ι → F) (S : Finset F) (Ans Fill : S → F) : ι → F :=
  fun x =>
    if hx : x.val ∈ S then Fill ⟨x.val, hx⟩
    else (f x - (cpolyAnsPoly S Ans).eval x.val) / (cpolyVanishingPoly S).eval x.val

/-- Function equality: `cpolyFuncQuotient` agrees with `funcQuotient`. -/
@[simp]
lemma cpolyFuncQuotient_eq_funcQuotient
    (f : ι → F) (S : Finset F) (Ans Fill : S → F) :
    cpolyFuncQuotient f S Ans Fill = funcQuotient f S Ans Fill := by
  funext x
  unfold cpolyFuncQuotient funcQuotient
  by_cases hx : x.val ∈ S
  · simp [hx]
  · simp only [hx, dif_neg, not_false_eq_true]
    rw [CompPoly.CPolynomial.eval_toPoly, cpolyAnsPoly_toPoly,
        CompPoly.CPolynomial.eval_toPoly, cpolyVanishingPoly_toPoly]

/-- Computable version of `disagreementSet`: the set of `x ∈ ι ∩ S` at which the answer
polynomial `cpolyAnsPoly` disagrees with `f`. Uses `Finset.filter` over the decidable predicate
in place of the noncomputable `Set.toFinset`. -/
def cpolyDisagreementSet (f : ι → F) (S : Finset F) (Ans : S → F) : Finset F :=
  (ι.attach.filter
    (fun x => x.val ∈ S ∧ (cpolyAnsPoly S Ans).eval x.val ≠ f x)).image Subtype.val

/-- Set equality: `cpolyDisagreementSet` and `disagreementSet` describe the same `Finset F`. -/
@[simp]
lemma cpolyDisagreementSet_eq_disagreementSet
    (f : ι → F) (S : Finset F) (Ans : S → F) :
    cpolyDisagreementSet f S Ans = disagreementSet f S Ans := by
  ext y
  simp only [cpolyDisagreementSet, disagreementSet,
    Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and,
    Set.mem_toFinset, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, ⟨hxS, hxDis⟩, hxy⟩
    refine ⟨x, ⟨hxS, ?_⟩, hxy⟩
    rwa [CompPoly.CPolynomial.eval_toPoly, cpolyAnsPoly_toPoly] at hxDis
  · rintro ⟨x, ⟨hxS, hxDis⟩, hxy⟩
    refine ⟨x, ⟨hxS, ?_⟩, hxy⟩
    rw [CompPoly.CPolynomial.eval_toPoly, cpolyAnsPoly_toPoly]
    exact hxDis

end Quotienting
