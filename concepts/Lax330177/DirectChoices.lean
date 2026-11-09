import Lax330177.CostExamples

/-!
---
title: Early and late direct paths
type: lemma
---
On the three-vertex chain and its shortcut triangle, each traversal takes c units, where c is zero or one. In the triangle, direct departures at 0 and 3 both minimize hops, elapsed time and waiting for either traversal cost. Of these two paths, only the early one is foremost and only the late one is latest-departing.

[Read the proof.](Lax330177Proofs.CostExamples.direct_choices.html)
-/
namespace Lax330177.DirectChoices
open Lax330177.Representations Lax330177.Durations Lax330177.OptimalPaths
open Lax330177.CostExamples

axiom direct_choices (c : Fin 2) :
    Shortest (direct false c) ∧ Fastest (direct false c) ∧ MinimumWaiting (direct false c) ∧
    Foremost (direct false c) ∧ ¬ LatestDeparture (direct false c) ∧
    Shortest (direct true c) ∧ Fastest (direct true c) ∧ MinimumWaiting (direct true c) ∧
    LatestDeparture (direct true c) ∧ ¬ Foremost (direct true c)
end Lax330177.DirectChoices
