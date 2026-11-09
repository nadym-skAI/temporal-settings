import Lax330177.UniformCosts

/-!
---
title: Zero traversal time
type: lemma
---
With uniform traversal time zero, a feasible path is fastest exactly when it minimizes total internal waiting time.

[Read the proof.](Lax330177Proofs.UniformCosts.zero_optima.html)
-/
namespace Lax330177.ZeroOptima
open Lax330177.Representations Lax330177.OptimalPaths
open Lax330177.UniformCosts
variable {n : ℕ} {G : Graph n} {q : Query G}

axiom zero_optima (p : Candidate q) (h : Uniform q 0) : Fastest p ↔ MinimumWaiting p
end Lax330177.ZeroOptima
