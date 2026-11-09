import Lax330177.Paths

/-!
---
title: Replacing undirected edges by opposite arcs
type: lemma
---
Replacing each undirected edge occurrence by both directed orientations preserves exactly the same timed paths of every length in the chosen traversal mode.

[Read the proof.](Lax330177Proofs.Basic.bidirect_paths.html)
-/
namespace Lax330177.BidirectPaths
open Lax330177.Representations
open Lax330177.Settings
open Lax330177.Paths

axiom bidirect_paths {n s} (G : InterpretedGraph n s) (_ : s.direction = .undirected) (k : ℕ) : TemporalPath (bidirect G).graph s.mode k = TemporalPath G.graph s.mode k
end Lax330177.BidirectPaths
