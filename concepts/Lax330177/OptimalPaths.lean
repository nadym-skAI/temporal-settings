import Lax330177.Durations
import Mathlib.Order.Filter.Extr
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
---
title: Optimal temporal paths
type: definition
---
Fix two vertices, traversal times, a release time and an inclusive arrival deadline.
A shortest path minimizes traversals. A fastest path minimizes elapsed time from
first departure to final arrival. Foremost paths minimize arrival, and latest
departure paths maximize departure. Minimum waiting paths minimize the sum of
idle gaps at internal vertices. Initial waiting and time after arrival do not
contribute. A zero-edge path occupies its vertex at any one instant in the window.
Every feasible query admits an optimizer for each of the five criteria.

- [Each objective attains its optimum.](Lax330177Proofs.OptimalPaths.optima_exist.html) Fix the endpoints, traversal times, release time and arrival deadline. If at least one feasible path exists, then each of the five criteria has an optimal path. The optimizing path may depend on the criterion.
-/
namespace Lax330177.OptimalPaths
open Lax330177.Representations Lax330177.Durations

structure Query {n : ℕ} (G : Graph n) where
  source : Fin n
  target : Fin n
  release : ℕ
  deadline : ℕ
  transit : Fin G.lifetime → Fin n → Fin n → ℕ

variable {n : ℕ} {G : Graph n} (q : Query G)

structure Candidate where
  hops : ℕ
  vertex : Fin (hops+1) → Fin n
  time : Fin hops → Fin G.lifetime
  feasible : DurationPath G q.transit vertex time
  starts : vertex 0 = q.source
  ends : vertex (Fin.last hops) = q.target
  departure : ℕ
  arrival : ℕ
  released : q.release ≤ departure
  inOrder : departure ≤ arrival
  onTime : arrival ≤ q.deadline
  first : ∀ h : 0 < hops, departure = (time ⟨0,h⟩).val
  last : ∀ h : 0 < hops,
    let i : Fin hops := ⟨hops-1, by omega⟩
    arrival = (time i).val + q.transit (time i) (vertex i.castSucc) (vertex i.succ)
  instantaneous : hops = 0 → departure = arrival

variable {q}
def Candidate.elapsed (p : Candidate q) := p.arrival - p.departure

def Candidate.waiting (p : Candidate q) : ℕ :=
  ∑ i : Fin p.hops, if h : i.val + 1 < p.hops then
    (p.time ⟨i.val+1,h⟩).val - ((p.time i).val + q.transit (p.time i) (p.vertex i.castSucc) (p.vertex i.succ))
  else 0

def Shortest (p : Candidate q) := IsMinOn Candidate.hops Set.univ p
def Fastest (p : Candidate q) := IsMinOn Candidate.elapsed Set.univ p
def Foremost (p : Candidate q) := IsMinOn Candidate.arrival Set.univ p
abbrev EarliestArrival (p : Candidate q) := Foremost p
def LatestDeparture (p : Candidate q) := IsMaxOn Candidate.departure Set.univ p
def MinimumWaiting (p : Candidate q) := IsMinOn Candidate.waiting Set.univ p

end Lax330177.OptimalPaths

