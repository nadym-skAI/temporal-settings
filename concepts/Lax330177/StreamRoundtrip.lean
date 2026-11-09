import Lax330177.Representations

/-!
---
title: Recovering an event list
type: lemma
---
Converting a chronological event list to snapshots and back preserves every event with its multiplicity. Only the order of events at the same time can change.

[Read the proof.](Lax330177Proofs.Basic.stream_roundtrip.html)
-/
namespace Lax330177.StreamRoundtrip

open Lax330177.Representations

axiom stream_roundtrip {n h} (s : EventStream n h) : (streamOf s.snapshots).events.Perm s.events
end Lax330177.StreamRoundtrip
