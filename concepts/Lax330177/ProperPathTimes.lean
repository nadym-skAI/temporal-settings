import Lax330177.Paths

/-!
---
title: Departure times on a proper graph
type: lemma
---
On a proper directed or undirected graph, every nonstrict temporal path already has strictly increasing departure times.

[Read the proof.](Lax330177Proofs.Basic.proper_path_times.html)
-/
namespace Lax330177.ProperPathTimes
open Lax330177.Representations
open Lax330177.Settings
open Lax330177.Paths

axiom proper_path_times {n k} (G : Graph n) (d : Direction) (hg : IsProper d G) (w : TemporalPath G .nonstrict k) : StrictMono w.val.time
end Lax330177.ProperPathTimes
