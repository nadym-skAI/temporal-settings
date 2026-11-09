import Lax330177.Paths

/-!
---
title: Strict walks are temporal-edge trails
type: lemma
---
A strict walk never repeats an edge-time occurrence.

[Read the proof.](Lax330177Proofs.Observations.strict_trail.html)
-/
namespace Lax330177.StrictWalkTrail
open Lax330177.Representations
open Lax330177.Settings Lax330177.Paths
variable {n k : ℕ} {G : Graph n} {mode : TraversalMode}

axiom strict_trail (d : Direction) (w : Walk G .strict k) : w.IsTemporalEdgeTrail d
end Lax330177.StrictWalkTrail
