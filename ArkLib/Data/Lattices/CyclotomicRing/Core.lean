/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Core.Modulus
import ArkLib.Data.Lattices.CyclotomicRing.Core.Basic
import ArkLib.Data.Lattices.CyclotomicRing.Core.Rq
import ArkLib.Data.Lattices.CyclotomicRing.Core.PowTwo

/-!
# Construction of the Cyclotomic Ring `R_q = Z_q[X] / (φ)`

Aggregator for the *construction layer* of the cyclotomic ring — the four files that define what
`R_q` **is**, before any Galois / norm / subfield theory is built on top of it:

* `Core/Modulus.lean` — the `CyclotomicModulus` data (`φ`, conductor) and `powTwoCyclotomic α`.
* `Core/Basic.lean` — the semantic quotient `R[X]/(φ)`, the computable `reduce`/`mul`, and the
  soundness bridge `quotientHom`.
* `Core/Rq.lean` — the canonical reduced representatives `Rq Φ` as a `CommRing`.
* `Core/PowTwo.lean` — the prime power-of-two specialization `R = ZMod q`.

## References

* [Lyubashevsky, V., Nguyen, N. K., and Plançon, M., *Lattice-Based Zero-Knowledge Proofs*][LNP22]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
