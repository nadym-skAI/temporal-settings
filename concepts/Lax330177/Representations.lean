import Mathlib

/-!
---
title: Three representations of temporal graphs
type: definition
---
A finite lifetime includes empty snapshots. Chronological lists enumerate distinct arc occurrences. Ties can be permuted. Undirected edges have both orientations.

- [Snapshots to labels and back.](Lax330177Proofs.Basic.snapshots_labels.html) Starting from snapshots, collecting the appearance times of each arc and reconstructing the snapshots recovers the original graph, including its lifetime.
- [Labels to snapshots and back.](Lax330177Proofs.Basic.labels_snapshots.html) Starting from a time-labelled footprint, taking its snapshots and collecting the labels again recovers the original footprint, label sets, and lifetime.
- [Events and adjacency.](Lax330177Proofs.Basic.stream_edges.html) At every time t, the snapshot reconstructed from the chronological event list contains the arc from u to v exactly when the original snapshot at t contains that arc.
- [Recovering an event list.](Lax330177Proofs.Basic.stream_roundtrip.html) Converting a chronological event list to snapshots and back preserves every event with its multiplicity. Only the order of events at the same time can change.
- [Snapshot adjacency and edge labels.](Lax330177.ActiveLabel.html) An arc is active at time t exactly when its label set contains t.
-/
namespace Lax330177.Representations
noncomputable section
attribute [local instance] Classical.propDecidable
/-- A finite temporal graph with exactly `n` vertices. -/
structure Graph (n : ℕ) where
  lifetime : ℕ
  edge : Fin lifetime → Fin n → Fin n → Prop
  loopless : ∀ t u, ¬ edge t u u

/-- Symmetric snapshots represent undirected edges. -/
def IsUndirected {n : ℕ} (G : Graph n) : Prop :=
  ∀ t u v, G.edge t u v ↔ G.edge t v u


inductive Direction where
  | directed | undirected
  deriving DecidableEq

inductive TraversalMode where
  | strict | nonstrict
  deriving DecidableEq

def TimeLE (mode : TraversalMode) (a b : ℕ) : Prop :=
  match mode with
  | .strict => a < b
  | .nonstrict => a ≤ b

def ValidDirection {n : ℕ} (d : Direction) (G : Graph n) : Prop :=
  match d with
  | .directed => True
  | .undirected => IsUndirected G

def Footprint {n : ℕ} (G : Graph n) (u v : Fin n) : Prop := ∃ t, G.edge t u v

/-- Explicit footprint and finite labels, with no unused footprint edges. -/
structure LabeledGraph (n : ℕ) where
  lifetime : ℕ
  footprint : Fin n → Fin n → Prop
  labels : Fin n → Fin n → Finset (Fin lifetime)
  supported : ∀ u v, footprint u v ↔ (labels u v).Nonempty
  loopless : ∀ u, ¬ footprint u u

def toLabels {n : ℕ} (G : Graph n) : LabeledGraph n where
  lifetime := G.lifetime
  footprint := Footprint G
  labels u v := Finset.univ.filter (fun t => G.edge t u v)
  supported := by intro u v; simp [Footprint, Finset.Nonempty]
  loopless := by intro u ⟨t, h⟩; exact G.loopless t u h

def LabeledGraph.toSnapshots {n : ℕ} (G : LabeledGraph n) : Graph n where
  lifetime := G.lifetime
  edge t u v := t ∈ G.labels u v
  loopless := by
    intro t u h
    exact G.loopless u ((G.supported u u).mpr ⟨t, h⟩)




structure EventStream (n h : ℕ) where
  events : List (Fin h × Fin n × Fin n)
  chronological : events.Pairwise (fun a b => a.1 ≤ b.1)
  unique : events.Nodup
  loopless : ∀ e ∈ events, e.2.1 ≠ e.2.2

def EventStream.snapshots {n h} (s : EventStream n h) : Graph n where
  lifetime := h
  edge t u v := (t,u,v) ∈ s.events
  loopless := by intro t u he; exact s.loopless _ he rfl



def occurrences {n} (G : Graph n) :=
  Finset.univ.filter (fun e : Fin G.lifetime × Fin n × Fin n => G.edge e.1 e.2.1 e.2.2)

def streamOf {n} (G : Graph n) : EventStream n G.lifetime := by
  let xs := (occurrences G).toList
  let cmp (a b : Fin G.lifetime × Fin n × Fin n) := decide (a.1 ≤ b.1)
  refine ⟨xs.mergeSort cmp, ?_, ?_, ?_⟩
  · have h := List.pairwise_mergeSort (le := cmp)
        (by simpa [cmp] using (fun a b c => @le_trans _ _ a.1 b.1 c.1 : ∀ a b c : Fin G.lifetime × Fin n × Fin n, _))
        (by intro a b; simpa [cmp] using le_total a.1 b.1) xs
    simpa [cmp] using h
  · exact (List.mergeSort_perm xs cmp).nodup_iff.mpr (Finset.nodup_toList _)
  · rintro ⟨t,u,v⟩ he huv
    change u = v at huv
    subst v
    exact G.loopless t u (by simpa [xs, occurrences] using he)



end
end Lax330177.Representations

