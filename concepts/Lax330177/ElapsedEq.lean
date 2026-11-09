import Lax330177.UniformCosts

/-!
---
title: Elapsed time splits into travel and waiting
type: theorem
---
If every available traversal takes c time units, every feasible path has elapsed time equal to its total internal waiting time plus c times its number of hops.

[Read the proof.](Lax330177Proofs.UniformCosts.elapsed_eq.html)
-/
namespace Lax330177.ElapsedEq
open Lax330177.Representations Lax330177.OptimalPaths
open Lax330177.UniformCosts
variable {n : ℕ} {G : Graph n} {q : Query G}

axiom elapsed_eq (p : Candidate q) (c : ℕ) (h : Uniform q c) :
    p.elapsed = p.waiting + p.hops * c
end Lax330177.ElapsedEq
