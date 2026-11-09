import Mathlib
import Lax330177.Representations
import Lax330177.Paths

/-!
---
title: Traversal times
type: definition
---
Each occurrence has a natural traversal time. The next departure may occur at arrival. The horizon bounds departure times and the final arrival may fall outside it.
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

axiom uniform_modes {k} (t : Fin k → ℕ) (m : TraversalMode) : Feasible t (fun _ => if m = .strict then 1 else 0) ↔ ∀ i j, i < j → TimeLE m (t i) (t j)

def DurationReaches {n} (G : Graph n) (δ : Fin G.lifetime → Fin n → Fin n → ℕ)
    (u v : Fin n) : Prop :=
  ∃ k, ∃ x : Fin (k+1) → Fin n, ∃ t : Fin k → Fin G.lifetime,
    DurationPath G δ x t ∧ x 0 = u ∧ x (Fin.last k) = v

axiom uniform_reaches {n} (G : Graph n) (m : TraversalMode) (u v) : DurationReaches G (fun _ _ _ => if m = .strict then 1 else 0) u v ↔ Reaches G m u v

axiom uniform_paths {n k} (G : Graph n) (m : TraversalMode) (x : Fin (k+1) → Fin n) (t : Fin k → Fin G.lifetime) : DurationPath G (fun _ _ _ => if m = .strict then 1 else 0) x t ↔ ∃ w : TemporalPath G m k, w.val.vertex = x ∧ w.val.time = t

end
end Lax330177.Durations
