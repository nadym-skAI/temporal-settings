import Lax330177.Representations

/-!
---
title: Snapshot adjacency and edge labels
type: lemma
---
An arc is active at time t exactly when its label set contains t.

[Read the proof.](Lax330177Proofs.Observations.active_label.html)
-/
namespace Lax330177.ActiveLabel
open Lax330177.Representations
variable {n k : ℕ} {G : Graph n} {mode : TraversalMode}

axiom active_label (G : Graph n) (t : Fin G.lifetime) (u v : Fin n) : t ∈ (toLabels G).labels u v ↔ G.edge t u v
end Lax330177.ActiveLabel
