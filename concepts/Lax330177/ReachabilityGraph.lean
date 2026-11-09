import Lax330177.Paths
import Mathlib.Combinatorics.Digraph.Basic

/-!
---
title: The temporal reachability graph
type: definition
---
Fix a traversal mode. The reachability graph is the static directed graph on the
original vertex set with an arc from u to v exactly when u and v are distinct
and a temporal path in that mode goes from u to v. Each arc records a whole
journey. Even undirected temporal graphs can have asymmetric reachability.
The zero-edge path witnesses reflexivity of the relation, while the graph omits
diagonal arcs.

[Strict and nonstrict reachability graphs on proper graphs.](Lax330177.ProperReachGraphs.html)
-/
namespace Lax330177.ReachabilityGraph
open Lax330177.Representations Lax330177.Paths Lax330177.Settings

def reachabilityGraph {n : ℕ} (G : Graph n) (mode : TraversalMode) : Digraph (Fin n) where
  Adj u v := u ≠ v ∧ Reaches G mode u v

def ofSetting {n : ℕ} {s : Setting} (G : InterpretedGraph n s) : Digraph (Fin n) :=
  reachabilityGraph G.graph s.mode

end Lax330177.ReachabilityGraph
