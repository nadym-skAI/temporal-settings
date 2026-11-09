import Lax330177.OptimalPaths

/-!
---
title: Optimality under uniform traversal times
type: definition
---
With constant traversal time c, elapsed time equals total internal waiting plus
c times the number of hops. At c = 0, fastest and minimum-waiting paths coincide.
At c = 1 a hop contributes one unit even if the path never waits.

- [Elapsed time splits into travel and waiting.](Lax330177Proofs.UniformCosts.elapsed_eq.html) If every available traversal takes c time units, every feasible path has elapsed time equal to its total internal waiting time plus c times its number of hops.
- [Zero traversal time.](Lax330177Proofs.UniformCosts.zero_optima.html) With uniform traversal time zero, a feasible path is fastest exactly when it minimizes total internal waiting time.
- [Unit traversal time.](Lax330177Proofs.UniformCosts.unit_optima.html) With uniform traversal time one, a feasible path is fastest exactly when it minimizes the sum of its hop count and its total internal waiting time.
-/
namespace Lax330177.UniformCosts
open Lax330177.Representations Lax330177.OptimalPaths
variable {n : ℕ} {G : Graph n} {q : Query G}
def Uniform (q : Query G) (c : ℕ) := ∀ t u v, G.edge t u v → q.transit t u v = c

end Lax330177.UniformCosts
