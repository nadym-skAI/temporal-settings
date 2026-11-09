import Lax330177.Paths

/-!
---
title: Enlarging the allowed vertex set
type: lemma
---
A path restricted to C remains feasible in any vertex superset D.

[Read the proof.](Lax330177Proofs.Observations.allowed_mono.html)
-/
namespace Lax330177.RestrictedMonotonicity
open Lax330177.Representations
open Lax330177.Settings Lax330177.Paths
variable {n k : ℕ} {G : Graph n} {mode : TraversalMode}

axiom allowed_mono {C D : Finset (Fin n)} (h : C ⊆ D) {u v} : ReachesIn G mode C u v → ReachesIn G mode D u v
end Lax330177.RestrictedMonotonicity
