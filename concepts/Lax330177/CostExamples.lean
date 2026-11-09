import Lax330177.UniformCosts

/-!
---
title: Three-vertex examples separating path objectives
type: definition
---
The chain 0 → 1 → 2 is available at times 0 through 3. An optional shortcut
0 → 2 makes a triangle. Every traversal takes c units, where c is zero or one.
In the triangle compare the direct departures at 0 and 3 with the two-hop
journey departing at 0 and c. In the chain compare departures (0,3) with (0,c).
These witnesses distinguish optimality predicates, allowing ties.

- [Early and late direct paths.](Lax330177Proofs.CostExamples.direct_choices.html) In the triangle, direct departures at 0 and 3 both minimize hops, elapsed time and waiting for either traversal cost. Of these two paths, only the early one is foremost and only the late one is latest-departing.
- [A shortest path can wait longer.](Lax330177Proofs.CostExamples.slow_shortest.html) On the chain without the shortcut, departures at 0 and 3 give a shortest path for either traversal cost. Another feasible path arrives in less elapsed time and has less total waiting.
- [A detour with no waiting.](Lax330177Proofs.CostExamples.no_wait_detour.html) In the triangle, the two-hop path departing at 0 and c minimizes waiting for either traversal cost and uses more hops than the shortcut. It is fastest exactly when c is zero.
-/
namespace Lax330177.CostExamples
open Lax330177.Representations Lax330177.Durations Lax330177.OptimalPaths

abbrev network (shortcut : Bool) : Graph 3 where
  lifetime := 4
  edge _ u v := u.val + 1 = v.val ∨ (shortcut = true ∧ u = 0 ∧ v = 2)
  loopless := by intro t u; fin_cases u <;> simp

def query (shortcut : Bool) (c : Fin 2) : Query (network shortcut) where
  source := 0
  target := 2
  release := 0
  deadline := 3+c.val
  transit _ _ _ := c.val

def direct (late : Bool) (c : Fin 2) : Candidate (query true c) where
  hops := 1
  vertex := ![0,2]
  time := fun _ => if late then 3 else 0
  departure := if late then 3 else 0
  arrival := (if late then 3 else 0) + c.val
  feasible := by cases late <;> fin_cases c <;> dsimp [DurationPath, Feasible, query, network] <;> decide
  starts := rfl
  ends := rfl
  released := by cases late <;> fin_cases c <;> dsimp [DurationPath, Feasible, query, network] <;> decide
  inOrder := by cases late <;> fin_cases c <;> dsimp [DurationPath, Feasible, query, network] <;> decide
  onTime := by cases late <;> fin_cases c <;> dsimp [DurationPath, Feasible, query, network] <;> decide
  first := by cases late <;> fin_cases c <;> dsimp [DurationPath, Feasible, query, network] <;> decide
  last := by cases late <;> fin_cases c <;> dsimp [DurationPath, Feasible, query, network] <;> decide
  instantaneous := by cases late <;> fin_cases c <;> dsimp [DurationPath, Feasible, query, network] <;> decide

def via (shortcut slow : Bool) (c : Fin 2) : Candidate (query shortcut c) where
  hops := 2
  vertex := id
  time := ![0, if slow then 3 else ⟨c.val, by change c.val < 4; omega⟩]
  departure := 0
  arrival := (if slow then 3 else c.val) + c.val
  feasible := by cases shortcut <;> cases slow <;> fin_cases c <;> dsimp [DurationPath, Feasible, query, network] <;> decide
  starts := rfl
  ends := rfl
  released := by cases shortcut <;> cases slow <;> fin_cases c <;> dsimp [DurationPath, Feasible, query, network] <;> decide
  inOrder := by cases shortcut <;> cases slow <;> fin_cases c <;> dsimp [DurationPath, Feasible, query, network] <;> decide
  onTime := by cases shortcut <;> cases slow <;> fin_cases c <;> dsimp [DurationPath, Feasible, query, network] <;> decide
  first := by cases shortcut <;> cases slow <;> fin_cases c <;> dsimp [DurationPath, Feasible, query, network] <;> decide
  last := by cases shortcut <;> cases slow <;> fin_cases c <;> dsimp [DurationPath, Feasible, query, network] <;> decide
  instantaneous := by cases shortcut <;> cases slow <;> fin_cases c <;> dsimp [DurationPath, Feasible, query, network] <;> decide



end Lax330177.CostExamples


