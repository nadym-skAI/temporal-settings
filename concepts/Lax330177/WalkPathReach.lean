import Lax330177.Paths

/-!
---
title: Walks and paths have the same reachability
type: theorem
---
In either traversal mode, a temporal walk from u to v exists exactly when a temporal path from u to v exists.

[Read the proof.](Lax330177Proofs.Basic.walk_path_reach.html)
-/
namespace Lax330177.WalkPathReach
open Lax330177.Representations
open Lax330177.Settings
open Lax330177.Paths

axiom walk_path_reach {n} (G : Graph n) (m : TraversalMode) (u v) : WalkReaches G m u v ↔ Reaches G m u v
end Lax330177.WalkPathReach
