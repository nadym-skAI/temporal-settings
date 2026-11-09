import Lax330177.Durations

/-!
---
title: The same reachable pairs
type: lemma
---
For every pair of vertices, reachability with uniform traversal time zero is equivalent to nonstrict reachability, and reachability with uniform time one is equivalent to strict reachability.

[Read the proof.](Lax330177Proofs.Basic.uniform_reaches.html)
-/
namespace Lax330177.UniformReaches
open Lax330177.Representations
open Lax330177.Paths
open Lax330177.Durations

axiom uniform_reaches {n} (G : Graph n) (m : TraversalMode) (u v) : DurationReaches G (fun _ _ _ => if m = .strict then 1 else 0) u v ↔ Reaches G m u v
end Lax330177.UniformReaches
