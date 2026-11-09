import Lax330177.CostExamples

/-!
---
title: A shortest path can wait longer
type: lemma
---
On the three-vertex chain and its shortcut triangle, each traversal takes c units, where c is zero or one. On the chain without the shortcut, departures at 0 and 3 give a shortest path for either traversal cost. Another feasible path arrives in less elapsed time and has less total waiting.

[Read the proof.](Lax330177Proofs.CostExamples.slow_shortest.html)
-/
namespace Lax330177.SlowShortest
open Lax330177.Representations Lax330177.Durations Lax330177.OptimalPaths
open Lax330177.CostExamples

axiom slow_shortest (c : Fin 2) : Shortest (via false true c) ∧
    ¬ Fastest (via false true c) ∧ ¬ MinimumWaiting (via false true c)
end Lax330177.SlowShortest
