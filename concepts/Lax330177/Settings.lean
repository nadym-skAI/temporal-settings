import Mathlib
import Lax330177.Representations

/-!
---
title: Temporal graph settings
type: definition
---
A setting selects direction, traversal mode and restrictions on the labelling. Happy graphs are both simple and proper.
-/
namespace Lax330177.Settings
open Lax330177.Representations
noncomputable section
attribute [local instance] Classical.propDecidable
/-- Identity of the static edge, respecting the selected direction convention. -/
def SameStaticEdge (d : Direction) {n : ℕ} (u v x y : Fin n) : Prop :=
  match d with
  | .directed => u = x ∧ v = y
  | .undirected => (u = x ∧ v = y) ∨ (u = y ∧ v = x)
def IsSimple {n : ℕ} (G : Graph n) : Prop :=
  ∀ u v t s, G.edge t u v → G.edge s u v → t = s

def IsProper {n : ℕ} (d : Direction) (G : Graph n) : Prop :=
  ValidDirection d G ∧ ∀ t u v x y, G.edge t u v → G.edge t x y →
    (u = x ∨ u = y ∨ v = x ∨ v = y) → SameStaticEdge d u v x y

def IsHappy {n : ℕ} (d : Direction) (G : Graph n) : Prop :=
  IsSimple G ∧ IsProper d G

def LabelMultiplicityBound {n : ℕ} (G : Graph n) (b : ℕ) : Prop :=
  ∀ u v, ((toLabels G).labels u v).card ≤ b

structure Setting where
  direction : Direction
  mode : TraversalMode
  requireSimple : Bool := false
  requireProper : Bool := false

def Setting.Admits {n : ℕ} (s : Setting) (G : Graph n) : Prop :=
  ValidDirection s.direction G ∧ (s.requireSimple = true → IsSimple G) ∧
    (s.requireProper = true → IsProper s.direction G)

structure InterpretedGraph (n : ℕ) (s : Setting) where
  graph : Graph n
  admitted : s.Admits graph

abbrev StrictTemporalGraph (n : ℕ) (d : Direction) (simple proper : Bool) :=
  InterpretedGraph n ⟨d, .strict, simple, proper⟩
abbrev NonstrictTemporalGraph (n : ℕ) (d : Direction) (simple proper : Bool) :=
  InterpretedGraph n ⟨d, .nonstrict, simple, proper⟩

end
end Lax330177.Settings
