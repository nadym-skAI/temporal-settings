import Lax330177.Durations

/-!
---
title: The same timed paths
type: lemma
---
Fix the vertex sequence and every departure time. They form a path with uniform traversal time zero exactly when they form a nonstrict temporal path, and with uniform time one exactly when they form a strict temporal path.

[Read the proof.](Lax330177Proofs.Basic.uniform_paths.html)
-/
namespace Lax330177.UniformPaths
open Lax330177.Representations
open Lax330177.Paths
open Lax330177.Durations

axiom uniform_paths {n k} (G : Graph n) (m : TraversalMode) (x : Fin (k+1) → Fin n) (t : Fin k → Fin G.lifetime) : DurationPath G (fun _ _ _ => if m = .strict then 1 else 0) x t ↔ ∃ w : TemporalPath G m k, w.val.vertex = x ∧ w.val.time = t
end Lax330177.UniformPaths
