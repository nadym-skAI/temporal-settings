import Lax330177.Paths

/-!
---
title: Path supports determine reachability
type: lemma
---
If two graphs on the same vertices realize exactly the same ordered vertex sequences as temporal paths in their respective modes, then they have the same reachability relation.

[Read the proof.](Lax330177Proofs.Basic.support_reach.html)
-/
namespace Lax330177.SupportReach
open Lax330177.Representations
open Lax330177.Settings
open Lax330177.Paths

axiom support_reach {n} (G H : Graph n) (m l : TraversalMode) (h : SupportEquivalent G H m l) (u v) : Reaches G m u v ↔ Reaches H l u v
end Lax330177.SupportReach
