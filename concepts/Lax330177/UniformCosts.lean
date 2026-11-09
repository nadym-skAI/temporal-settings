import Lax330177.OptimalPaths

/-!
---
title: Optimality under uniform traversal times
type: theorem
---
With constant traversal time c, elapsed time equals total internal waiting plus
c times the number of hops. At c = 0, fastest and minimum-waiting paths coincide.
At c = 1 a hop contributes one unit even if the path never waits.
-/
namespace Lax330177.UniformCosts
open Lax330177.Representations Lax330177.OptimalPaths
variable {n : ℕ} {G : Graph n} {q : Query G}
def Uniform (q : Query G) (c : ℕ) := ∀ t u v, G.edge t u v → q.transit t u v = c

axiom elapsed_eq (p : Candidate q) (c : ℕ) (h : Uniform q c) :
    p.elapsed = p.waiting + p.hops * c
axiom zero_optima (p : Candidate q) (h : Uniform q 0) : Fastest p ↔ MinimumWaiting p
axiom unit_optima (p : Candidate q) (h : Uniform q 1) :
    Fastest p ↔ IsMinOn (fun x : Candidate q => x.waiting + x.hops) Set.univ p
end Lax330177.UniformCosts
