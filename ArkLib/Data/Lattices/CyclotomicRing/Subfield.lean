/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Basis
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Packing
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.TraceVanishing
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.TraceInnerProduct
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Cardinality
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Bijectivity

/-!
# The Subfield Packing Map `ψ` of Hachi §3 (Theorem 2)

Aggregator for the `R_q^H ↪ R_q` packing layer of Hachi [NOZ26, §3], establishing that the
packing map `ψ : (R_q^H)^{d/k} → R_q` is a bijection.

* `Subfield/Basis.lean` — monomials `X^i`, the `X^d = -1` folding toolkit, the `Fintype` instance
  and `|R_q| = q^{2^α}`, and the symmetric basis `vElt` with its triangular coefficient formula.
* `Subfield/Packing.lean` — the packing map `ψ` and its additivity.
* `Subfield/TraceVanishing.lean` — the trace-of-monomial vanishing identities (Claims 2, 3).
* `Subfield/TraceInnerProduct.lean` — the trace formula `Tr_H(ψ(a)·σ_{-1}(ψ(b))) = (d/k)·⟨a,b⟩`
  and the injectivity of `ψ`.
* `Subfield/Cardinality.lean` — `|R_q^H| = q^k` (Eq. 7) from the symmetric basis.
* `Subfield/Bijectivity.lean` — `ψ` is a bijection (Theorem 2).

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
