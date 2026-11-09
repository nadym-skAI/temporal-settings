import Mathlib
import Lax330177.Representations
import Lax330177.Paths

/-!
---
title: Traversal times
type: definition
---
Each occurrence has a natural traversal time. The next departure may occur at arrival. The lifetime bounds departure times and the final arrival may fall outside it.

- [Feasible departure times.](Lax330177Proofs.Basic.uniform_modes.html) For integer timestamps, a departure sequence is feasible with traversal time zero exactly when it is weakly increasing. With traversal time one, it is feasible exactly when it is strictly increasing.
- [The same timed paths.](Lax330177Proofs.Basic.uniform_paths.html) Fix the vertex sequence and every departure time. They form a path with uniform traversal time zero exactly when they form a nonstrict temporal path, and with uniform time one exactly when they form a strict temporal path.
- [The same reachable pairs.](Lax330177Proofs.Basic.uniform_reaches.html) For every pair of vertices, reachability with uniform traversal time zero is equivalent to nonstrict reachability, and reachability with uniform time one is equivalent to strict reachability.
-/
namespace Lax330177.Durations
open Lax330177.Representations
open Lax330177.Paths
noncomputable section
attribute [local instance] Classical.propDecidable

def Feasible {k : ℕ} (time duration : Fin k → ℕ) : Prop :=
  ∀ i j, i < j → time i + duration i ≤ time j

def DurationPath {n k} (G : Graph n) (δ : Fin G.lifetime → Fin n → Fin n → ℕ)
    (x : Fin (k+1) → Fin n) (t : Fin k → Fin G.lifetime) : Prop :=
  Function.Injective x ∧ (∀ i, G.edge (t i) (x i.castSucc) (x i.succ)) ∧
    Feasible (fun i => (t i).val) (fun i => δ (t i) (x i.castSucc) (x i.succ))


def DurationReaches {n} (G : Graph n) (δ : Fin G.lifetime → Fin n → Fin n → ℕ)
    (u v : Fin n) : Prop :=
  ∃ k, ∃ x : Fin (k+1) → Fin n, ∃ t : Fin k → Fin G.lifetime,
    DurationPath G δ x t ∧ x 0 = u ∧ x (Fin.last k) = v



end
end Lax330177.Durations
