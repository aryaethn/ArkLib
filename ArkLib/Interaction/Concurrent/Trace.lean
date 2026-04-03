/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Concurrent.Frontier

/-!
# Finite concurrent traces

This file defines finite traces of concurrent interaction specs.

For sequential `Interaction.Spec`, a `Transcript` records one complete root-to-
leaf play through a tree whose next move family is always unique.

For concurrent `Interaction.Concurrent.Spec`, there may be multiple currently
enabled frontier events at once. A `Trace S` therefore records one **finite
scheduler linearization**:

* choose one frontier event of `S`;
* continue with the residual spec after that event;
* repeat until reaching `done`.

So `Trace` is the finite interleaving-level execution object associated to the
concurrent core. If a later true-concurrency layer adds independence or partial-
order semantics, those refinements should be layered over these linear traces
rather than replacing the basic execution story here.
-/

universe u

namespace Interaction
namespace Concurrent

/--
`Trace S` is a finite execution trace of the concurrent spec `S`.

It records one scheduler-chosen linearization of frontier events, ending when
the residual concurrent spec reaches `done`.

This should be read as the concurrent analogue of a sequential transcript, but
with one crucial difference:
the constructors record **frontier choices** rather than the moves of a
single always-current node.
-/
inductive Trace : Spec → Type (u + 1) where
  | /-- The unique finished trace of a terminated concurrent spec. -/
    done : Trace .done
  | /-- Extend a trace by one frontier event and a trace of the residual spec
    that remains after performing that event. -/
    step {S : Spec} (event : Front S) : Trace (residual event) → Trace S

namespace Trace

/-- The number of frontier events in a finite concurrent trace. -/
def length : {S : Spec} → Trace S → Nat
  | .done, .done => 0
  | _, .step _ tail => tail.length.succ

@[simp, grind =]
theorem length_done : length Trace.done = 0 := rfl

@[simp, grind =]
theorem length_step {S : Spec} (event : Front S) (tail : Trace (residual event)) :
    length (Trace.step event tail) = tail.length.succ := by
  simp [length]

/-- A `step` contributes exactly one additional frontier event to the trace
length. -/
theorem length_step_eq_add_one {S : Spec} (event : Front S)
    (tail : Trace (residual event)) :
    length (Trace.step event tail) = tail.length + 1 := by
  simp [length_step]

end Trace
end Concurrent
end Interaction
