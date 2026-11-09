import Lax330177.CostExamples

/-!
---
title: A detour with no waiting
type: lemma
---
On the three-vertex chain and its shortcut triangle, each traversal takes c units, where c is zero or one. In the triangle, the two-hop path departing at 0 and c minimizes waiting for either traversal cost and uses more hops than the shortcut. It is fastest exactly when c is zero.

[Read the proof.](Lax330177Proofs.CostExamples.no_wait_detour.html)
-/
namespace Lax330177.NoWaitDetour
open Lax330177.Representations Lax330177.Durations Lax330177.OptimalPaths
open Lax330177.CostExamples

axiom no_wait_detour (c : Fin 2) : MinimumWaiting (via true false c) ∧
    ¬ Shortest (via true false c) ∧ (Fastest (via true false c) ↔ c.val = 0)
end Lax330177.NoWaitDetour
