import Lax330177.Paths

/-!
---
title: Allowing all vertices
type: lemma
---
Restricting the path to the full vertex set recovers ordinary temporal reachability.

[Read the proof.](Lax330177Proofs.Observations.allow_all.html)
-/
namespace Lax330177.UnrestrictedVertices
open Lax330177.Representations
open Lax330177.Settings Lax330177.Paths
variable {n k : ℕ} {G : Graph n} {mode : TraversalMode}

axiom allow_all (G : Graph n) (mode : TraversalMode) (u v : Fin n) : ReachesIn G mode Finset.univ u v ↔ Reaches G mode u v
end Lax330177.UnrestrictedVertices
