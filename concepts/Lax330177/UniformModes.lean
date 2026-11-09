import Lax330177.Durations

/-!
---
title: Feasible departure times
type: lemma
---
For integer timestamps, a departure sequence is feasible with traversal time zero exactly when it is weakly increasing. With traversal time one, it is feasible exactly when it is strictly increasing.

[Read the proof.](Lax330177Proofs.Basic.uniform_modes.html)
-/
namespace Lax330177.UniformModes
open Lax330177.Representations
open Lax330177.Paths
open Lax330177.Durations

axiom uniform_modes {k} (t : Fin k → ℕ) (m : TraversalMode) : Feasible t (fun _ => if m = .strict then 1 else 0) ↔ ∀ i j, i < j → TimeLE m (t i) (t j)
end Lax330177.UniformModes
