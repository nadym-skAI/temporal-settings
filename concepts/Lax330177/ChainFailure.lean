import Lax330177.Examples

/-!
---
title: Reachability can fail transitivity
type: lemma
---
In both traversal modes, the same three-vertex chain has 0 reaching 1 and 1 reaching 2, although 0 cannot reach 2.

[Read the proof.](Lax330177Proofs.Basic.chain_failure.html)
-/
namespace Lax330177.ChainFailure
open Lax330177.Representations
open Lax330177.Settings
open Lax330177.Paths
open Lax330177.Examples

axiom chain_failure (m : TraversalMode) : ¬ (∀ u v z, Reaches backwardsChain m u v → Reaches backwardsChain m v z → Reaches backwardsChain m u z)
end Lax330177.ChainFailure
