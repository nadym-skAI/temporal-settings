import Lax330177.Paths

/-!
---
title: Reachability on a proper graph
type: theorem
---
On a proper directed or undirected graph, u reaches v strictly exactly when u reaches v nonstrictly.

[Read the proof.](Lax330177Proofs.Basic.proper_modes.html)
-/
namespace Lax330177.ProperModes
open Lax330177.Representations
open Lax330177.Settings
open Lax330177.Paths

axiom proper_modes {n} (G : Graph n) (d : Direction) (h : IsProper d G) (u v) : Reaches G .strict u v ↔ Reaches G .nonstrict u v
end Lax330177.ProperModes
