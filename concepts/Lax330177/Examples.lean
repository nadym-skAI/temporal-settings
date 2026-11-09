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

- [A simple graph can separate the traversal modes.](Lax330177Proofs.Basic.simple_separation.html) The directed chain with both arcs available only at time 0 is simple and fails properness. Its first vertex reaches its last nonstrictly but cannot reach it strictly.
- [Properness does not imply simplicity.](Lax330177Proofs.Basic.proper_separation.html) One undirected edge appearing twice gives a proper graph that fails simplicity. The two opposite directed arcs are proper as well, since every two-step traversal returns to its starting vertex.
- [A proper graph can have a walk with equal departure times.](Lax330177Proofs.Basic.bounce_same_time.html) On a proper undirected graph, a nonstrict walk can traverse one edge and immediately traverse it back at the same time.
- [Reachability can fail transitivity.](Lax330177Proofs.Basic.chain_failure.html) In both traversal modes, the same three-vertex chain has 0 reaching 1 and 1 reaching 2, although 0 cannot reach 2.
- [Reachability can be asymmetric even on a happy graph.](Lax330177Proofs.Basic.happy_asymmetry.html) The undirected chain with edge 1–2 at time 0 and edge 0–1 at time 1 is simple and proper. In both modes, 2 reaches 0 while 0 cannot reach 2.
- [A temporal-edge trail can repeat a static edge.](Lax330177.TrailSeparation.html) Crossing one undirected edge at time 0 and returning at time 1 gives a temporal-edge trail that repeats its static edge.
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




def simultaneousBounce : Walk repeatedEdge .nonstrict 2 where
  vertex := ![0, 1, 0]
  time _ := (0 : Fin 2)
  available := by intro i; fin_cases i <;> decide
  ordered := by intro i j _; exact le_refl _


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







abbrev simultaneousChain : Graph 3 where
  lifetime := 1
  edge _ u v := (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2)
  loopless := by intro t u; fin_cases u <;> decide

def chainPath : Walk simultaneousChain .nonstrict 2 where
  vertex := id
  time _ := 0
  available := by intro i; fin_cases i <;> decide
  ordered := by intro i j h; exact le_rfl



def reverseChainPath : Walk backwardsChain .strict 2 where
  vertex := ![2,1,0]
  time := id
  available := by intro i; fin_cases i <;> decide
  ordered := by intro i j h; exact h


end
end Lax330177.Examples
