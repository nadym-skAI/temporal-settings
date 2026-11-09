import Lax330177.Representations

/-!
---
title: Labels to snapshots and back
type: lemma
---
Starting from a time-labelled footprint, taking its snapshots and collecting the labels again recovers the original footprint, label sets, and lifetime.

[Read the proof.](Lax330177Proofs.Basic.labels_snapshots.html)
-/
namespace Lax330177.LabelsSnapshots

open Lax330177.Representations

axiom labels_snapshots {n} (G : LabeledGraph n) : toLabels G.toSnapshots = G
end Lax330177.LabelsSnapshots
