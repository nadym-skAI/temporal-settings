import Lax330177.Representations

/-!
---
title: Events and adjacency
type: lemma
---
At every time t, the snapshot reconstructed from the chronological event list contains the arc from u to v exactly when the original snapshot at t contains that arc.

[Read the proof.](Lax330177Proofs.Basic.stream_edges.html)
-/
namespace Lax330177.StreamEdges

open Lax330177.Representations

axiom stream_edges {n} (G : Graph n) (t : Fin G.lifetime) (u v : Fin n) : (streamOf G).snapshots.edge t u v ↔ G.edge t u v
end Lax330177.StreamEdges
