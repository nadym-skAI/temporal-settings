import Lax330177.Examples

/-!
---
title: Properness does not imply simplicity
type: lemma
---
One undirected edge appearing twice gives a proper graph that fails simplicity. The two opposite directed arcs are proper as well, since every two-step traversal returns to its starting vertex.

[Read the proof.](Lax330177Proofs.Basic.proper_separation.html)
-/
namespace Lax330177.ProperSeparation
open Lax330177.Representations
open Lax330177.Settings
open Lax330177.Paths
open Lax330177.Examples

axiom proper_separation : IsProper .undirected repeatedEdge ∧ ¬ IsSimple repeatedEdge ∧ IsProper .directed repeatedEdge
end Lax330177.ProperSeparation
