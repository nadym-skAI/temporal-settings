import Lax330177.ReachabilityGraph

/-!
---
title: Proper graphs have the same reachability graph in both modes
type: lemma
---
On a proper temporal graph, strict and nonstrict traversal yield the same static
reachability graph on the original vertices.

[Read the proof.](Lax330177Proofs.Observations.proper_graphs.html)
-/
namespace Lax330177.ProperReachGraphs
open Lax330177.Representations Lax330177.Settings Lax330177.ReachabilityGraph

axiom proper_graphs {n : ℕ} (G : Graph n) (d : Direction) (h : IsProper d G) :
    reachabilityGraph G .strict = reachabilityGraph G .nonstrict

end Lax330177.ProperReachGraphs
