/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Core.Rq

/-!
# `Rq` — forwarding module

The canonical reduced-representative ring `Rq Φ` now lives in
[`Core/Rq.lean`](Core/Rq.lean) (the cyclotomic-ring *construction* layer). This module forwards the
old `ArkLib.Data.Lattices.CyclotomicRing.Rq` import path to it so existing references keep
resolving after the relocation.
-/
