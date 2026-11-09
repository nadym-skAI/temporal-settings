import Lax330177.Paths

/-!
---
title: Static-edge trails are temporal-edge trails
type: lemma
---
A walk that never repeats a static edge never repeats an edge-time occurrence.

[Read the proof.](Lax330177Proofs.Observations.trail_inclusion.html)
-/
namespace Lax330177.TrailInclusion
open Lax330177.Representations
open Lax330177.Settings Lax330177.Paths
variable {n k : ℕ} {G : Graph n} {mode : TraversalMode}

axiom trail_inclusion (d : Direction) (w : Walk G mode k) (h : w.IsStaticEdgeTrail d) : w.IsTemporalEdgeTrail d
end Lax330177.TrailInclusion
