import Lax330177.OptimalPaths

namespace Lax330177Proofs.OptimalPaths
open Lax330177.Representations Lax330177.OptimalPaths

private theorem minimum {α : Type} (h : Nonempty α) (cost : α → ℕ) :
    ∃ p, IsMinOn cost Set.univ p := by
  classical
  obtain ⟨w⟩ := h
  have hex : ∃ a, ∃ p, cost p = a := ⟨_,w,rfl⟩
  obtain ⟨p,hp⟩ := Nat.find_spec hex
  exact ⟨p,isMinOn_univ_iff.mpr (fun x => hp ▸ Nat.find_min' hex ⟨x,rfl⟩)⟩

/--
---
conclusion: Lax330177.OptimalPaths.optima_exist
---
Natural-valued costs attain a minimum on a nonempty set. Maximizing departure
is equivalent to minimizing its distance below the common deadline.
-/
theorem optima_exist {n : ℕ} {G : Graph n} {q : Query G} (h : Nonempty (Candidate q)) :
    (∃ p : Candidate q, Shortest p) ∧ (∃ p : Candidate q, Fastest p) ∧
    (∃ p : Candidate q, Foremost p) ∧ (∃ p : Candidate q, LatestDeparture p) ∧
    (∃ p : Candidate q, MinimumWaiting p) := by
  refine ⟨minimum h _,minimum h _,minimum h _,?_,minimum h _⟩
  obtain ⟨p,hp⟩ := minimum h (fun x => q.deadline - x.departure)
  refine ⟨p,isMaxOn_univ_iff.mpr ?_⟩
  intro x
  have hx := isMinOn_univ_iff.mp hp x
  have h₁ := p.inOrder.trans p.onTime
  have h₂ := x.inOrder.trans x.onTime
  change q.deadline - p.departure ≤ q.deadline - x.departure at hx
  change x.departure ≤ p.departure
  omega
end Lax330177Proofs.OptimalPaths
