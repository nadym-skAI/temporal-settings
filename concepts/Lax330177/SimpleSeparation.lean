import Lax330177.Examples

/-!
---
title: A simple graph can separate the traversal modes
type: lemma
---
The directed chain with both arcs available only at time 0 is simple and fails properness. Its first vertex reaches its last nonstrictly but cannot reach it strictly.

[Read the proof.](Lax330177Proofs.Basic.simple_separation.html)
-/
namespace Lax330177.SimpleSeparation
open Lax330177.Representations
open Lax330177.Settings
open Lax330177.Paths
open Lax330177.Examples

axiom simple_separation : IsSimple simultaneousChain ∧ ¬ IsProper .directed simultaneousChain ∧ Reaches simultaneousChain .nonstrict 0 2 ∧ ¬ Reaches simultaneousChain .strict 0 2
end Lax330177.SimpleSeparation
