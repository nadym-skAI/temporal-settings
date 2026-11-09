import Lax330177.Examples

/-!
---
title: A proper graph can have a walk with equal departure times
type: lemma
---
On a proper undirected graph, a nonstrict walk can traverse one edge and immediately traverse it back at the same time.

[Read the proof.](Lax330177Proofs.Basic.bounce_same_time.html)
-/
namespace Lax330177.BounceSameTime
open Lax330177.Representations
open Lax330177.Settings
open Lax330177.Paths
open Lax330177.Examples

axiom bounce_same_time : IsProper .undirected repeatedEdge ∧ ¬ StrictMono simultaneousBounce.time
end Lax330177.BounceSameTime
