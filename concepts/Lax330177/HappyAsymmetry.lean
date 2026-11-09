import Lax330177.Examples

/-!
---
title: Reachability can be asymmetric even on a happy graph
type: lemma
---
The undirected chain with edge 1–2 at time 0 and edge 0–1 at time 1 is simple and proper. In both modes, 2 reaches 0 while 0 cannot reach 2.

[Read the proof.](Lax330177Proofs.Basic.happy_asymmetry.html)
-/
namespace Lax330177.HappyAsymmetry
open Lax330177.Representations
open Lax330177.Settings
open Lax330177.Paths
open Lax330177.Examples

axiom happy_asymmetry (m : TraversalMode) : IsHappy .undirected backwardsChain ∧ Reaches backwardsChain m 2 0 ∧ ¬ Reaches backwardsChain m 0 2
end Lax330177.HappyAsymmetry
