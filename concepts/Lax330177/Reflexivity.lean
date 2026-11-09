import Lax330177.Paths

/-!
---
title: Temporal reachability is reflexive
type: lemma
---
Every vertex reaches itself in both modes, including at lifetime zero.

[Read the proof.](Lax330177Proofs.Observations.reflexive.html)
-/
namespace Lax330177.Reflexivity
open Lax330177.Representations
open Lax330177.Settings Lax330177.Paths
variable {n k : ℕ} {G : Graph n} {mode : TraversalMode}

axiom reflexive (G : Graph n) (mode : TraversalMode) (u : Fin n) : Reaches G mode u u
end Lax330177.Reflexivity
