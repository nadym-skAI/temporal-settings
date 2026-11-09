import Lax330177.Paths

/-!
---
title: Strict paths give nonstrict reachability
type: lemma
---
If u can reach v by a strict temporal path, then u can also reach v by a nonstrict temporal path in the same graph.

[Read the proof.](Lax330177Proofs.Basic.strict_inclusion.html)
-/
namespace Lax330177.StrictInclusion
open Lax330177.Representations
open Lax330177.Settings
open Lax330177.Paths

axiom strict_inclusion {n} {G : Graph n} {u v} : Reaches G .strict u v → Reaches G .nonstrict u v
end Lax330177.StrictInclusion
