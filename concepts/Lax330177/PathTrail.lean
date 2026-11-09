import Lax330177.Paths

/-!
---
title: Paths are static-edge trails
type: lemma
---
A vertex-simple path never uses a footprint edge twice, even counting reverse traversals as the same undirected edge.

[Read the proof.](Lax330177Proofs.Observations.path_trail.html)
-/
namespace Lax330177.PathTrail
open Lax330177.Representations
open Lax330177.Settings Lax330177.Paths
variable {n k : ℕ} {G : Graph n} {mode : TraversalMode}

axiom path_trail (d : Direction) (w : Walk G mode k) (h : w.IsPath) : w.IsStaticEdgeTrail d
end Lax330177.PathTrail
