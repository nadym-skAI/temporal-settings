import Mathlib
import Lax330177.Representations
import Lax330177.Settings

/-!
---
title: Paths, walks and reachability
type: definition
---
Walks may revisit vertices. Paths have injective vertex sequences. Departure times increase strictly or weakly according to the traversal mode.
-/
namespace Lax330177.Paths
open Lax330177.Representations
open Lax330177.Settings
noncomputable section
attribute [local instance] Classical.propDecidable
structure Walk {n : ℕ} (G : Graph n) (mode : TraversalMode) (k : ℕ) where
  vertex : Fin (k + 1) → Fin n
  time : Fin k → Fin G.lifetime
  available : ∀ i, G.edge (time i) (vertex i.castSucc) (vertex i.succ)
  ordered : ∀ i j, i < j → TimeLE mode (time i).val (time j).val

namespace Walk
variable {n k : ℕ} {G : Graph n} {mode : TraversalMode}

def start (w : Walk G mode k) := w.vertex 0
def finish (w : Walk G mode k) := w.vertex (Fin.last k)
def support (w : Walk G mode k) := List.ofFn w.vertex
def IsPath (w : Walk G mode k) : Prop := Function.Injective w.vertex
def IsStaticEdgeTrail (d : Direction) (w : Walk G mode k) : Prop :=
  ∀ i j : Fin k, SameStaticEdge d (w.vertex i.castSucc) (w.vertex i.succ)
    (w.vertex j.castSucc) (w.vertex j.succ) → i = j
def IsTemporalEdgeTrail (d : Direction) (w : Walk G mode k) : Prop :=
  ∀ i j : Fin k, SameStaticEdge d (w.vertex i.castSucc) (w.vertex i.succ)
    (w.vertex j.castSucc) (w.vertex j.succ) → w.time i = w.time j → i = j

def StaysIn (w : Walk G mode k) (C : Finset (Fin n)) : Prop := ∀ i, w.vertex i ∈ C
def InWindow (w : Walk G mode k) (a b : ℕ) : Prop :=
  ∀ i, a ≤ (w.time i).val ∧ (w.time i).val < b
def IsClosed (w : Walk G mode k) : Prop := w.start = w.finish
def IsCircuit (d : Direction) (w : Walk G mode k) : Prop :=
  0 < k ∧ w.IsClosed ∧ w.IsStaticEdgeTrail d
/-- Positive closed walk without repeated vertices except the final return.
Undirected cycles also have at least three edges, directed cycles at least two. -/
def IsCycle (d : Direction) (w : Walk G mode k) : Prop :=
  (match d with | .directed => 2 ≤ k | .undirected => 3 ≤ k) ∧
    w.IsClosed ∧ Function.Injective (fun i : Fin k => w.vertex i.castSucc)

def nil (G : Graph n) (mode : TraversalMode) (v : Fin n) : Walk G mode 0 where
  vertex _ := v
  time := Fin.elim0
  available := by intro i; exact Fin.elim0 i
  ordered := by intro i; exact Fin.elim0 i

@[simp] theorem nil_start (G : Graph n) (mode : TraversalMode) (v : Fin n) :
    (nil G mode v).start = v := rfl
@[simp] theorem nil_finish (G : Graph n) (mode : TraversalMode) (v : Fin n) :
    (nil G mode v).finish = v := rfl
theorem nil_isPath (G : Graph n) (mode : TraversalMode) (v : Fin n) :
    (nil G mode v).IsPath := by intro i j _; apply Fin.ext; omega

def forgetStrict (w : Walk G .strict k) : Walk G .nonstrict k where
  vertex := w.vertex
  time := w.time
  available := w.available
  ordered := by intro i j h; exact Nat.le_of_lt (w.ordered i j h)

theorem staticTrail_temporalTrail (d : Direction) (w : Walk G mode k)
    (h : w.IsStaticEdgeTrail d) : w.IsTemporalEdgeTrail d := by
  intro i j he _; exact h i j he

theorem path_staticTrail (d : Direction) (w : Walk G mode k) (hp : w.IsPath) :
    w.IsStaticEdgeTrail d := by
  intro i j he
  cases d with
  | directed =>
    have h := congrArg Fin.val (hp he.1)
    exact Fin.ext h
  | undirected =>
    rcases he with he | he
    · exact Fin.ext (congrArg (fun x : Fin (k + 1) => x.val) (hp he.1))
    · have h1 := congrArg Fin.val (hp he.1)
      have h2 := congrArg Fin.val (hp he.2)
      simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
      omega

theorem path_length_bound (w : Walk G mode k) (hp : w.IsPath) : k + 1 ≤ n := by
  have h := Fintype.card_le_of_injective w.vertex hp
  simpa using h

theorem proper_trail_strict (d : Direction) (w : Walk G .nonstrict k)
    (hg : IsProper d G) (hw : w.IsStaticEdgeTrail d) : StrictMono w.time := by
  intro i j hij
  have hle : (w.time i).val ≤ (w.time j).val := w.ordered i j hij
  by_contra hn
  have heq : (w.time i).val = (w.time j).val := by
    change ¬ (w.time i).val < (w.time j).val at hn
    omega
  let r : Fin k := ⟨i.val + 1, by have := j.isLt; change i.val < j.val at hij; omega⟩
  have hir : i < r := by change i.val < i.val + 1; omega
  have hrj : r ≤ j := by change i.val + 1 ≤ j.val; change i.val < j.val at hij; omega
  have ht1 : (w.time i).val ≤ (w.time r).val := w.ordered i r hir
  have ht2 : (w.time r).val ≤ (w.time j).val := by
    rcases lt_or_eq_of_le hrj with h | h
    · exact w.ordered r j h
    · rw [h]
  have ht : w.time r = w.time i := Fin.ext (by omega)
  have har := w.available r
  rw [ht] at har
  have shared : w.vertex i.succ = w.vertex r.castSucc := by
    apply congrArg w.vertex
    apply Fin.ext
    rfl
  have he := hg.2 (w.time i) _ _ _ _ (w.available i) har (Or.inr (Or.inr (Or.inl shared)))
  have hi := hw i r he
  exact (ne_of_lt hir) hi

def strictify (d : Direction) (w : Walk G .nonstrict k)
    (hg : IsProper d G) (hw : w.IsStaticEdgeTrail d) : Walk G .strict k where
  vertex := w.vertex
  time := w.time
  available := w.available
  ordered := proper_trail_strict d w hg hw

theorem strict_temporalTrail (d : Direction) (w : Walk G .strict k) :
    w.IsTemporalEdgeTrail d := by
  intro i j _ he
  by_contra hn
  rcases lt_or_gt_of_ne hn with h | h
  · have ht := w.ordered i j h
    simp only [TimeLE] at ht
    rw [he] at ht
    exact Nat.lt_irrefl _ ht
  · have ht := w.ordered j i h
    simp only [TimeLE] at ht
    rw [he] at ht
    exact Nat.lt_irrefl _ ht

/-- A contiguous segment, including its two endpoints. -/
def segment (w : Walk G mode k) (a len : ℕ) (h : a + len ≤ k) :
    Walk G mode len where
  vertex i := w.vertex ⟨a + i.val, by omega⟩
  time i := w.time ⟨a + i.val, by omega⟩
  available i := w.available ⟨a + i.val, by omega⟩
  ordered := by intro i j hij; apply w.ordered; change a + i.val < a + j.val; omega

def take (w : Walk G mode k) (len : ℕ) (h : len ≤ k) := w.segment 0 len (by omega)
def suffix (w : Walk G mode k) (a : ℕ) (h : a ≤ k) :=
  w.segment a (k - a) (by omega)

/-- Boundary condition for concatenation; empty operands impose no time constraint. -/
def CanAppend {l : ℕ} (w : Walk G mode k) (z : Walk G mode l) : Prop :=
  w.finish = z.start ∧ ∀ i j, TimeLE mode (w.time i).val (z.time j).val

end Walk

def Reaches {n : ℕ} (G : Graph n) (mode : TraversalMode) (u v : Fin n) : Prop :=
  ∃ k, ∃ w : Walk G mode k, w.IsPath ∧ w.start = u ∧ w.finish = v
def WalkReaches {n : ℕ} (G : Graph n) (mode : TraversalMode) (u v : Fin n) : Prop :=
  ∃ k, ∃ w : Walk G mode k, w.start = u ∧ w.finish = v
def ReachesIn {n : ℕ} (G : Graph n) (mode : TraversalMode)
    (C : Finset (Fin n)) (u v : Fin n) : Prop :=
  ∃ k, ∃ w : Walk G mode k, w.IsPath ∧ w.StaysIn C ∧ w.start = u ∧ w.finish = v
def ReachesDuring {n : ℕ} (G : Graph n) (mode : TraversalMode)
    (a b : ℕ) (u v : Fin n) : Prop :=
  ∃ k, ∃ w : Walk G mode k, w.IsPath ∧ w.InWindow a b ∧ w.start = u ∧ w.finish = v

theorem reaches_refl {n : ℕ} (G : Graph n) (mode : TraversalMode) (u : Fin n) :
    Reaches G mode u u := ⟨0, Walk.nil G mode u, Walk.nil_isPath G mode u, rfl, rfl⟩

theorem reachesIn_reaches {n : ℕ} {G : Graph n} {mode : TraversalMode}
    {C : Finset (Fin n)} {u v : Fin n} (h : ReachesIn G mode C u v) :
    Reaches G mode u v := by
  obtain ⟨k, w, hp, _, hs, ht⟩ := h
  exact ⟨k, w, hp, hs, ht⟩

theorem reachesIn_mono {n : ℕ} {G : Graph n} {mode : TraversalMode}
    {C D : Finset (Fin n)} (hCD : C ⊆ D) {u v : Fin n}
    (h : ReachesIn G mode C u v) : ReachesIn G mode D u v := by
  obtain ⟨k, w, hp, hC, hs, ht⟩ := h
  exact ⟨k, w, hp, fun i => hCD (hC i), hs, ht⟩

theorem reachesIn_univ {n : ℕ} (G : Graph n) (mode : TraversalMode) (u v : Fin n) :
    ReachesIn G mode Finset.univ u v ↔ Reaches G mode u v := by
  constructor
  · exact reachesIn_reaches
  · rintro ⟨k, w, hp, hs, ht⟩
    exact ⟨k, w, hp, fun _ => Finset.mem_univ _, hs, ht⟩

theorem strict_reaches_nonstrict {n : ℕ} {G : Graph n} {u v : Fin n}
    (h : Reaches G .strict u v) : Reaches G .nonstrict u v := by
  obtain ⟨k, w, hp, hs, ht⟩ := h
  exact ⟨k, w.forgetStrict, hp, hs, ht⟩

theorem proper_reaches_iff {n : ℕ} {G : Graph n} (d : Direction) (hg : IsProper d G)
    (u v : Fin n) : Reaches G .strict u v ↔ Reaches G .nonstrict u v := by
  constructor
  · exact strict_reaches_nonstrict
  · rintro ⟨k, w, hp, hs, ht⟩
    exact ⟨k, w.strictify d hg (w.path_staticTrail d hp), hp, hs, ht⟩

abbrev TemporalPath {n} (G : Graph n) (m : TraversalMode) (k : ℕ) := {w : Walk G m k // w.IsPath}
def graphReaches {n s} (G : InterpretedGraph n s) := Reaches G.graph s.mode

axiom strict_inclusion {n} {G : Graph n} {u v} : Reaches G .strict u v → Reaches G .nonstrict u v

axiom proper_modes {n} (G : Graph n) (d : Direction) (h : IsProper d G) (u v) : Reaches G .strict u v ↔ Reaches G .nonstrict u v

end
end Lax330177.Paths
