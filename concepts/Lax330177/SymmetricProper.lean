import Lax330177.Paths

/-!
---
title: Properness of symmetric snapshots
type: lemma
---
On symmetric snapshots, directed properness is equivalent to undirected properness.

[Read the proof.](Lax330177Proofs.Observations.symmetric_proper.html)
-/
namespace Lax330177.SymmetricProper
open Lax330177.Representations
open Lax330177.Settings Lax330177.Paths
variable {n k : ℕ} {G : Graph n} {mode : TraversalMode}

axiom symmetric_proper (G : Graph n) (h : IsUndirected G) : IsProper .directed G ↔ IsProper .undirected G
end Lax330177.SymmetricProper
