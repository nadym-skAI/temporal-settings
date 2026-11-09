import Lax330177.UniformCosts

/-!
---
title: Unit traversal time
type: lemma
---
With uniform traversal time one, a feasible path is fastest exactly when it minimizes the sum of its hop count and its total internal waiting time.

[Read the proof.](Lax330177Proofs.UniformCosts.unit_optima.html)
-/
namespace Lax330177.UnitOptima
open Lax330177.Representations Lax330177.OptimalPaths
open Lax330177.UniformCosts
variable {n : ℕ} {G : Graph n} {q : Query G}

axiom unit_optima (p : Candidate q) (h : Uniform q 1) :
    Fastest p ↔ IsMinOn (fun x : Candidate q => x.waiting + x.hops) Set.univ p
end Lax330177.UnitOptima
