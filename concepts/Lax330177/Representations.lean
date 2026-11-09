import Mathlib

/-!
---
title: Three representations of temporal graphs
type: definition
---
A finite horizon includes empty snapshots. Chronological lists enumerate distinct arc occurrences. Ties can be permuted. Undirected edges have both orientations.
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

@[simp] theorem snapshot_label_edge {n : ℕ} (G : Graph n)
    (t : Fin G.lifetime) (u v : Fin n) :
    (toLabels G).toSnapshots.edge t u v ↔ G.edge t u v := by
  simp [toLabels, LabeledGraph.toSnapshots]

@[simp] theorem snapshot_roundtrip {n : ℕ} (G : Graph n) :
    (toLabels G).toSnapshots = G := by
  cases G with
  | mk l e h =>
    simp only [toLabels, LabeledGraph.toSnapshots]
    congr 1
    funext t u v
    exact propext ⟨fun h => (Finset.mem_filter.mp h).2,
      fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

@[simp] theorem label_roundtrip {n : ℕ} (G : LabeledGraph n) :
    toLabels G.toSnapshots = G := by
  cases G with
  | mk l e labels supported loopless =>
    dsimp [toLabels, LabeledGraph.toSnapshots, Footprint]
    congr 1
    · funext u v
      exact propext (supported u v).symm
    · funext u v
      calc
        _ = Finset.univ.filter (fun t => t ∈ labels u v) :=
          Finset.filter_congr_decidable _ _ _
        _ = labels u v := by ext t; simp

structure EventStream (n h : ℕ) where
  events : List (Fin h × Fin n × Fin n)
  chronological : events.Pairwise (fun a b => a.1 ≤ b.1)
  unique : events.Nodup
  loopless : ∀ e ∈ events, e.2.1 ≠ e.2.2

def EventStream.snapshots {n h} (s : EventStream n h) : Graph n where
  lifetime := h
  edge t u v := (t,u,v) ∈ s.events
  loopless := by intro t u he; exact s.loopless _ he rfl

axiom snapshots_labels {n} (G : Graph n) : (toLabels G).toSnapshots = G

axiom labels_snapshots {n} (G : LabeledGraph n) : toLabels G.toSnapshots = G

end
end Lax330177.Representations
