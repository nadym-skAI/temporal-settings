import Lax330177.Examples

/-!
---
title: A temporal-edge trail can repeat a static edge
type: lemma
---
Crossing one undirected edge at time 0 and returning at time 1 gives a temporal-edge trail that repeats its static edge.

[Read the proof.](Lax330177Proofs.Observations.trail_separation.html)
-/
namespace Lax330177.TrailSeparation
open Lax330177.Representations
open Lax330177.Settings Lax330177.Paths
open Lax330177.Examples
variable {n k : ℕ} {G : Graph n} {mode : TraversalMode}

axiom trail_separation : bounce.IsTemporalEdgeTrail .undirected ∧ ¬ bounce.IsStaticEdgeTrail .undirected
end Lax330177.TrailSeparation
