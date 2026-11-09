import Lax330177.OptimalPaths

/-!
---
title: Each objective attains its optimum
type: theorem
---
Fix the endpoints, traversal times, release time and arrival deadline. If at least one feasible path exists, then each of the five criteria has an optimal path. The optimizing path may depend on the criterion.

[Read the proof.](Lax330177Proofs.OptimalPaths.optima_exist.html)
-/
namespace Lax330177.OptimaExist
open Lax330177.Representations Lax330177.Durations
open Lax330177.OptimalPaths
variable {n : ℕ} {G : Graph n} {q : Query G}

axiom optima_exist (h : Nonempty (Candidate q)) :
    (∃ p : Candidate q, Shortest p) ∧ (∃ p : Candidate q, Fastest p) ∧
    (∃ p : Candidate q, Foremost p) ∧ (∃ p : Candidate q, LatestDeparture p) ∧
    (∃ p : Candidate q, MinimumWaiting p)
end Lax330177.OptimaExist
