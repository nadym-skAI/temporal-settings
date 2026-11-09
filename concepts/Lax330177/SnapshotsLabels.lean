import Lax330177.Representations

/-!
---
title: Snapshots to labels and back
type: lemma
---
Starting from snapshots, collecting the appearance times of each arc and reconstructing the snapshots recovers the original graph, including its lifetime.

[Read the proof.](Lax330177Proofs.Basic.snapshots_labels.html)
-/
namespace Lax330177.SnapshotsLabels

open Lax330177.Representations

axiom snapshots_labels {n} (G : Graph n) : (toLabels G).toSnapshots = G
end Lax330177.SnapshotsLabels
