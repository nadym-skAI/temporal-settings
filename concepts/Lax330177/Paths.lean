import Mathlib
import Lax330177.Representations
import Lax330177.Settings

/-!
---
title: Paths, walks and reachability
type: definition
---
Walks may revisit vertices. Paths have injective vertex sequences. Departure times increase strictly or weakly according to the traversal mode.

- [Walks and paths have the same reachability.](Lax330177Proofs.Basic.walk_path_reach.html) In either traversal mode, a temporal walk from u to v exists exactly when a temporal path from u to v exists.
- [Strict paths give nonstrict reachability.](Lax330177Proofs.Basic.strict_inclusion.html) If u can reach v by a strict temporal path, then u can also reach v by a nonstrict temporal path in the same graph.
- [Departure times on a proper graph.](Lax330177Proofs.Basic.proper_path_times.html) On a proper directed or undirected graph, every nonstrict temporal path already has strictly increasing departure times.
- [Reachability on a proper graph.](Lax330177Proofs.Basic.proper_modes.html) On a proper directed or undirected graph, u reaches v strictly exactly when u reaches v nonstrictly.
- [Replacing undirected edges by opposite arcs.](Lax330177Proofs.Basic.bidirect_paths.html) Replacing each undirected edge occurrence by both directed orientations preserves exactly the same timed paths of every length in the chosen traversal mode.
- [Path supports determine reachability.](Lax330177Proofs.Basic.support_reach.html) If two graphs on the same vertices realize exactly the same ordered vertex sequences as temporal paths in their respective modes, then they have the same reachability relation.
- [Temporal reachability is reflexive.](Lax330177.Reflexivity.html) Every vertex reaches itself in both modes, including at lifetime zero.
- [Enlarging the allowed vertex set.](Lax330177.RestrictedMonotonicity.html) A path restricted to C remains feasible in any vertex superset D.
- [Allowing all vertices.](Lax330177.UnrestrictedVertices.html) Restricting the path to the full vertex set recovers ordinary temporal reachability.
- [Paths are static-edge trails.](Lax330177.PathTrail.html) A vertex-simple path never uses a footprint edge twice, even counting reverse traversals as the same undirected edge.
- [Static-edge trails are temporal-edge trails.](Lax330177.TrailInclusion.html) A walk that never repeats a static edge never repeats an edge-time occurrence.
- [Strict walks are temporal-edge trails.](Lax330177.StrictWalkTrail.html) A strict walk never repeats an edge-time occurrence.
- [Properness of symmetric snapshots.](Lax330177.SymmetricProper.html) On symmetric snapshots, directed properness is equivalent to undirected properness.
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


def forgetStrict (w : Walk G .strict k) : Walk G .nonstrict k where
  vertex := w.vertex
  time := w.time
  available := w.available
  ordered := by intro i j h; exact Nat.le_of_lt (w.ordered i j h)







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







abbrev TemporalPath {n} (G : Graph n) (m : TraversalMode) (k : ℕ) := {w : Walk G m k // w.IsPath}
abbrev StrictPath {n} (G : Graph n) := TemporalPath G .strict
abbrev NonstrictPath {n} (G : Graph n) := TemporalPath G .nonstrict
abbrev StrictReachability {n} (G : Graph n) := Reaches G .strict
abbrev NonstrictReachability {n} (G : Graph n) := Reaches G .nonstrict

def graphReaches {n s} (G : InterpretedGraph n s) := Reaches G.graph s.mode



def bidirect {n} {s : Setting} (G : InterpretedGraph n s) :
    InterpretedGraph n { s with direction := .directed } where
  graph := G.graph
  admitted := ⟨trivial, G.admitted.2.1, fun h => ⟨trivial, (G.admitted.2.2 h).2⟩⟩




def Realizes {n k} (G : Graph n) (m : TraversalMode) (x : Fin (k+1) → Fin n) :=
  ∃ w : TemporalPath G m k, w.val.vertex = x

def SupportEquivalent {n} (G H : Graph n) (m l : TraversalMode) :=
  ∀ k (x : Fin (k+1) → Fin n), Realizes G m x ↔ Realizes H l x


end
end Lax330177.Paths
