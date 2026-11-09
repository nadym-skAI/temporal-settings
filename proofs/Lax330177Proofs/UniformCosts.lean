import Lax330177.UniformCosts
namespace Lax330177Proofs.UniformCosts
open Lax330177.Representations Lax330177.OptimalPaths Lax330177.UniformCosts
variable {n : ℕ} {G : Graph n} {q : Query G}

private theorem telescope {k : ℕ} (t : Fin (k+1) → ℕ) (c : ℕ)
    (h : ∀ i : Fin k, t i.castSucc + c ≤ t i.succ) :
    t 0 + k*c + (∑ i : Fin k, (t i.succ - (t i.castSucc + c))) = t (Fin.last k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ht := ih (fun i => t i.castSucc) (fun i => h i.castSucc)
    rw [Fin.sum_univ_castSucc, Nat.succ_mul]
    have hl := h (Fin.last k)
    change t (Fin.last k).castSucc + c ≤ t (Fin.last (k+1)) at hl
    change t 0 + k*c + (∑ i : Fin k, (t i.castSucc.succ - (t i.castSucc.castSucc + c))) = t (Fin.last k).castSucc at ht
    change t 0 + (k*c+c) + ((∑ i : Fin k, (t i.castSucc.succ - (t i.castSucc.castSucc+c))) + (t (Fin.last (k+1)) - (t (Fin.last k).castSucc+c))) = _
    omega

/--
---
conclusion: Lax330177.UniformCosts.elapsed_eq
---
Summing the gaps between successive traversals cancels the internal timestamps.
-/
theorem elapsed_eq (p : Candidate q) (c : ℕ) (h : Uniform q c) :
    p.elapsed = p.waiting + p.hops * c := by
  have hu (i : Fin p.hops) := h _ _ _ (p.feasible.2.1 i)
  cases hk : p.hops with
  | zero =>
    simp [Candidate.elapsed,Candidate.waiting,p.instantaneous hk,hk]
  | succ k =>
    let e (i : Fin (k+1)) : Fin p.hops := ⟨i.val,by omega⟩
    let t (i : Fin (k+1)) := (p.time (e i)).val
    have mono (i : Fin k) : t i.castSucc + c ≤ t i.succ := by
      have h₀ := p.feasible.2.2 (e i.castSucc) (e i.succ) (by exact Nat.lt_succ_self i.val)
      simpa only [hu] using h₀
    have ht := telescope t c mono
    have hd : p.departure = t 0 := p.first (by omega)
    have ha : p.arrival = t (Fin.last k) + c := by
      rw [p.last (by omega), hu]
      congr 2
      apply congrArg p.time
      apply Fin.ext
      simp [e,hk]
    have hw : p.waiting = ∑ i : Fin k, (t i.succ - (t i.castSucc + c)) := by
      unfold Candidate.waiting
      rw [← Equiv.sum_comp (finCongr hk.symm)]
      rw [Fin.sum_univ_castSucc]
      simp [hk,hu,t,e] <;> rfl
    rw [Candidate.elapsed,hd,ha,hw,Nat.succ_mul]
    omega

/--
---
conclusion: Lax330177.UniformCosts.zero_optima
---
At zero cost per traversal the two objective values agree path by path.
-/
theorem zero_optima (p : Candidate q) (h : Uniform q 0) : Fastest p ↔ MinimumWaiting p := by
  simp only [Fastest,MinimumWaiting,isMinOn_univ_iff,elapsed_eq _ 0 h,Nat.mul_zero,Nat.add_zero]

/--
---
conclusion: Lax330177.UniformCosts.unit_optima
---
At unit cost every traversal contributes one to elapsed time.
-/
theorem unit_optima (p : Candidate q) (h : Uniform q 1) :
    Fastest p ↔ IsMinOn (fun x : Candidate q => x.waiting + x.hops) Set.univ p := by
  simp only [Fastest,isMinOn_univ_iff,elapsed_eq _ 1 h,Nat.mul_one]
end Lax330177Proofs.UniformCosts


