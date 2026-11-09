import Lax330177.UniformCosts

/-!
---
title: Three-vertex examples separating path objectives
type: theorem
---
The chain 0 → 1 → 2 is available at times 0 through 3. An optional shortcut
0 → 2 makes a triangle. Every traversal takes c units, where c is zero or one.
In the triangle compare the direct departures at 0 and 3 with the two-hop
journey departing at 0 and c. In the chain compare departures (0,3) with (0,c).
These witnesses distinguish optimality predicates, allowing ties.
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

axiom direct_choices (c : Fin 2) :
    Shortest (direct false c) ∧ Fastest (direct false c) ∧ MinimumWaiting (direct false c) ∧
    Foremost (direct false c) ∧ ¬ LatestDeparture (direct false c) ∧
    Shortest (direct true c) ∧ Fastest (direct true c) ∧ MinimumWaiting (direct true c) ∧
    LatestDeparture (direct true c) ∧ ¬ Foremost (direct true c)

axiom slow_shortest (c : Fin 2) : Shortest (via false true c) ∧
    ¬ Fastest (via false true c) ∧ ¬ MinimumWaiting (via false true c)

axiom no_wait_detour (c : Fin 2) : MinimumWaiting (via true false c) ∧
    ¬ Shortest (via true false c) ∧ (Fastest (via true false c) ↔ c.val = 0)
end Lax330177.CostExamples


