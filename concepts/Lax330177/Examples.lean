import Mathlib
import Lax330177.Representations
import Lax330177.Settings
import Lax330177.Paths

/-!
---
title: Counterexamples
type: definition
---
A single repeated edge admits a simultaneous return walk under properness. A chain in reverse chronological order witnesses failure of transitivity.
-/
namespace Lax330177.Examples
open Lax330177.Representations
open Lax330177.Settings
open Lax330177.Paths
noncomputable section
attribute [local instance] Classical.propDecidable
abbrev repeatedEdge : Graph 2 where
  lifetime := 2
  edge _ u v := u ≠ v
  loopless := by intro _ _ h; exact h rfl

def bounce : Walk repeatedEdge .strict 2 where
  vertex := ![0, 1, 0]
  time := id
  available := by intro i; fin_cases i <;> decide
  ordered := by intro i j h; exact h

theorem bounce_temporalTrail : bounce.IsTemporalEdgeTrail .undirected :=
  bounce.strict_temporalTrail .undirected

theorem bounce_not_staticTrail : ¬ bounce.IsStaticEdgeTrail .undirected := by
  intro h
  have he : SameStaticEdge .undirected
      (bounce.vertex (0 : Fin 2).castSucc) (bounce.vertex (0 : Fin 2).succ)
      (bounce.vertex (1 : Fin 2).castSucc) (bounce.vertex (1 : Fin 2).succ) := by
    exact Or.inr ⟨rfl, rfl⟩
  have hi := h 0 1 he
  exact (by decide : (0 : Fin 2) ≠ 1) hi

theorem repeatedEdge_proper : IsProper .undirected repeatedEdge := by
  constructor
  · intro t u v; exact ne_comm
  · intro t u v x y h1 h2 _
    fin_cases u <;> fin_cases v <;> fin_cases x <;> fin_cases y <;>
      simp_all [SameStaticEdge]

def simultaneousBounce : Walk repeatedEdge .nonstrict 2 where
  vertex := ![0, 1, 0]
  time _ := (0 : Fin 2)
  available := by intro i; fin_cases i <;> decide
  ordered := by intro i j _; exact le_refl _

theorem proper_walk_need_not_be_strict : ¬ StrictMono simultaneousBounce.time := by
  intro h
  have he := h (show (0 : Fin 2) < 1 by decide)
  exact (lt_irrefl (0 : Fin 2)) he

abbrev backwardsChain : Graph 3 where
  lifetime := 2
  edge t u v :=
    (t = 1 ∧ ((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0))) ∨
    (t = 0 ∧ ((u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1)))
  loopless := by intro t u; fin_cases t <;> fin_cases u <;> decide

def firstLeg : Walk backwardsChain .strict 1 where
  vertex := ![0, 1]
  time _ := (1 : Fin 2)
  available := by intro i; fin_cases i; decide
  ordered := by intro i j h; have := i.isLt; have := j.isLt; change i.val < j.val at h; omega

def secondLeg : Walk backwardsChain .strict 1 where
  vertex := ![1, 2]
  time _ := (0 : Fin 2)
  available := by intro i; fin_cases i; decide
  ordered := by intro i j h; have := i.isLt; have := j.isLt; change i.val < j.val at h; omega

theorem reaches_first : Reaches backwardsChain .strict 0 1 := by
  refine ⟨1, firstLeg, ?_, rfl, rfl⟩
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [firstLeg]

theorem reaches_second : Reaches backwardsChain .strict 1 2 := by
  refine ⟨1, secondLeg, ?_, rfl, rfl⟩
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [secondLeg]

theorem not_reaches_endpoints (mode : TraversalMode) : ¬ Reaches backwardsChain mode 0 2 := by
  rintro ⟨k, w, hp, hs, ht⟩
  have hb := w.path_length_bound hp
  have hk : k ≤ 2 := by omega
  interval_cases k
  · have he : (0 : Fin 3) = 2 := hs.symm.trans ht
    exact (by decide : (0 : Fin 3) ≠ 2) he
  · have he := w.available 0
    change backwardsChain.edge (w.time 0) w.start w.finish at he
    rw [hs, ht] at he
    simp [backwardsChain] at he
  · have h0 := w.available (0 : Fin 2)
    have h1 := w.available (1 : Fin 2)
    change backwardsChain.edge (w.time 0) w.start (w.vertex 1) at h0
    change backwardsChain.edge (w.time 1) (w.vertex 1) w.finish at h1
    rw [hs] at h0
    rw [ht] at h1
    have ho := w.ordered (0 : Fin 2) 1 (by decide)
    simp [backwardsChain] at h0 h1
    cases mode <;> simp_all [TimeLE]

theorem strict_reachability_not_transitive :
    ¬ (∀ u v z, Reaches backwardsChain .strict u v → Reaches backwardsChain .strict v z →
      Reaches backwardsChain .strict u z) := by
  intro h
  exact not_reaches_endpoints .strict (h 0 1 2 reaches_first reaches_second)
theorem nonstrict_reachability_not_transitive :
    ¬ (∀ u v z, Reaches backwardsChain .nonstrict u v → Reaches backwardsChain .nonstrict v z →
      Reaches backwardsChain .nonstrict u z) := by
  intro h
  exact not_reaches_endpoints .nonstrict
    (h 0 1 2 (strict_reaches_nonstrict reaches_first) (strict_reaches_nonstrict reaches_second))

axiom bounce_same_time : IsProper .undirected repeatedEdge ∧ ¬ StrictMono simultaneousBounce.time

axiom chain_failure (m : TraversalMode) : ¬ (∀ u v z, Reaches backwardsChain m u v → Reaches backwardsChain m v z → Reaches backwardsChain m u z)

abbrev simultaneousChain : Graph 3 where
  lifetime := 1
  edge _ u v := (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2)
  loopless := by intro t u; fin_cases u <;> decide

def chainPath : Walk simultaneousChain .nonstrict 2 where
  vertex := id
  time _ := 0
  available := by intro i; fin_cases i <;> decide
  ordered := by intro i j h; exact le_rfl

axiom simple_separation : IsSimple simultaneousChain ∧ ¬ IsProper .directed simultaneousChain ∧ Reaches simultaneousChain .nonstrict 0 2 ∧ ¬ Reaches simultaneousChain .strict 0 2

axiom proper_separation : IsProper .undirected repeatedEdge ∧ ¬ IsSimple repeatedEdge ∧ ¬ IsProper .directed repeatedEdge

end
end Lax330177.Examples
