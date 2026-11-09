import Lax330177.CostExamples
import Lax330177Proofs.UniformCosts
namespace Lax330177Proofs.CostExamples
open Lax330177.OptimalPaths Lax330177.CostExamples
open Lax330177Proofs.UniformCosts

private theorem positive {b c} (p : Candidate (query b c)) : 1 ≤ p.hops := by
  by_contra! h
  have eq : (0 : Fin (p.hops+1)) = Fin.last p.hops := Fin.ext (by simp; omega)
  have hv := p.starts.symm.trans ((congrArg p.vertex eq).trans p.ends)
  exact (by decide : (0 : Fin 3) ≠ 2) hv

private theorem lower {b c} (p : Candidate (query b c)) : c.val ≤ p.elapsed := by
  rw [elapsed_eq p c.val (by intro; intros; rfl)]
  have hp := positive p
  exact le_trans (by simpa using Nat.mul_le_mul_right c.val hp) (Nat.le_add_left ..)

private theorem direct_best (late : Bool) (c : Fin 2) :
    Shortest (direct late c) ∧ Fastest (direct late c) ∧ MinimumWaiting (direct late c) := by
  have he : (direct late c).elapsed = c.val := by cases late <;> fin_cases c <;> decide
  have hw : (direct late c).waiting = 0 := by cases late <;> fin_cases c <;> decide
  exact ⟨isMinOn_univ_iff.mpr positive,isMinOn_univ_iff.mpr (fun p => he ▸ lower p),
    isMinOn_univ_iff.mpr (fun _ => hw ▸ Nat.zero_le _)⟩

/--
---
conclusion: Lax330177.CostExamples.direct_choices
---
Moving the direct departure from zero to three preserves hop count, elapsed time
and waiting, but exchanges earliest arrival for latest departure.
-/
theorem direct_choices (c : Fin 2) :
    Shortest (direct false c) ∧ Fastest (direct false c) ∧ MinimumWaiting (direct false c) ∧
    Foremost (direct false c) ∧ ¬ LatestDeparture (direct false c) ∧
    Shortest (direct true c) ∧ Fastest (direct true c) ∧ MinimumWaiting (direct true c) ∧
    LatestDeparture (direct true c) ∧ ¬ Foremost (direct true c) := by
  obtain ⟨s,f,w⟩ := direct_best false c
  obtain ⟨s',f',w'⟩ := direct_best true c
  refine ⟨s,f,w,isMinOn_univ_iff.mpr ?_,?_,s',f',w',isMaxOn_univ_iff.mpr ?_,?_⟩
  · intro p
    have h := lower p
    change c.val ≤ p.arrival - p.departure at h
    change 0 + c.val ≤ p.arrival
    omega
  · intro h
    exact (by decide : ¬ 3 ≤ 0) (isMaxOn_univ_iff.mp h (direct true c))
  · intro p
    have hd := p.first (by have := positive p; omega)
    change p.departure ≤ 3
    rw [hd]; exact Nat.le_of_lt_succ (p.time _).isLt
  · intro h
    have he := isMinOn_univ_iff.mp h (direct false c)
    change 3+c.val ≤ 0+c.val at he
    omega

/--
---
conclusion: Lax330177.CostExamples.slow_shortest
---
Without the shortcut both arcs are necessary. Waiting at vertex one gives a
shortest path which loses on both elapsed time and total waiting.
-/
theorem slow_shortest (c : Fin 2) : Shortest (via false true c) ∧
    ¬ Fastest (via false true c) ∧ ¬ MinimumWaiting (via false true c) := by
  refine ⟨isMinOn_univ_iff.mpr ?_,?_,?_⟩
  · intro p
    have pos := positive p
    change 2 ≤ p.hops
    by_contra! h
    have hk : p.hops = 1 := by omega
    let i : Fin p.hops := ⟨0,by omega⟩
    have hs : i.castSucc = 0 := rfl
    have hf : i.succ = Fin.last p.hops := Fin.ext (by simpa [i] using hk.symm)
    have he := p.feasible.2.1 i
    rw [hs,hf,p.starts,p.ends] at he
    exact (by decide : ¬ ((0:ℕ)+1=2 ∨ (false=true ∧ (0:Fin 3)=0 ∧ (2:Fin 3)=2))) he
  · intro h
    have he := isMinOn_univ_iff.mp h (via false false c)
    fin_cases c <;> revert he <;> decide
  · intro h
    have he := isMinOn_univ_iff.mp h (via false false c)
    fin_cases c <;> revert he <;> decide

/--
---
conclusion: Lax330177.CostExamples.no_wait_detour
---
The two-hop detour incurs no internal waiting. Against a direct edge it ties
on elapsed time at zero transit cost and loses at unit cost.
-/
theorem no_wait_detour (c : Fin 2) : MinimumWaiting (via true false c) ∧
    ¬ Shortest (via true false c) ∧ (Fastest (via true false c) ↔ c.val = 0) := by
  have hw : (via true false c).waiting = 0 := by fin_cases c <;> decide
  refine ⟨isMinOn_univ_iff.mpr (fun _ => hw ▸ Nat.zero_le _),?_,?_⟩
  · intro h
    exact (by decide : ¬ 2 ≤ 1) (isMinOn_univ_iff.mp h (direct false c))
  · constructor
    · intro h
      have he := isMinOn_univ_iff.mp h (direct false c)
      fin_cases c <;> revert he <;> decide
    · intro hz
      apply isMinOn_univ_iff.mpr
      intro p
      have he : (via true false c).elapsed = 0 := by fin_cases c <;> first | rfl | contradiction
      rw [he]; exact Nat.zero_le _
end Lax330177Proofs.CostExamples
