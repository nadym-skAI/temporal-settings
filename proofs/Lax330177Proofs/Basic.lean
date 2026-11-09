import Lax330177
namespace Lax330177Proofs.Basic
open Lax330177.Representations
open Lax330177.Settings
open Lax330177.Paths
open Lax330177.Durations
open Lax330177.Examples
/--
---
conclusion: Lax330177.Representations.snapshots_labels
---
A finite horizon includes empty snapshots.
-/
theorem snapshots_labels {n} (G : Graph n) : (toLabels G).toSnapshots = G := snapshot_roundtrip G

/--
---
conclusion: Lax330177.Representations.labels_snapshots
---
A finite horizon includes empty snapshots.
-/
theorem labels_snapshots {n} (G : LabeledGraph n) : toLabels G.toSnapshots = G := label_roundtrip G

/--
---
conclusion: Lax330177.Paths.strict_inclusion
---
Walks may revisit vertices.
-/
theorem strict_inclusion {n} {G : Graph n} {u v} : Reaches G .strict u v → Reaches G .nonstrict u v := strict_reaches_nonstrict

/--
---
conclusion: Lax330177.Paths.proper_modes
---
Walks may revisit vertices.
-/
theorem proper_modes {n} (G : Graph n) (d : Direction) (h : IsProper d G) (u v) : Reaches G .strict u v ↔ Reaches G .nonstrict u v := proper_reaches_iff d h u v

/--
---
conclusion: Lax330177.Durations.uniform_modes
---
Each occurrence has a natural traversal time.
-/
theorem uniform_modes {k} (t : Fin k → ℕ) (m : TraversalMode) : Feasible t (fun _ => if m = .strict then 1 else 0) ↔ ∀ i j, i < j → TimeLE m (t i) (t j) := by cases m <;> simp [Feasible, TimeLE]

/--
---
conclusion: Lax330177.Examples.bounce_same_time
---
A single repeated edge admits a simultaneous return walk under properness.
-/
theorem bounce_same_time : IsProper .undirected repeatedEdge ∧ ¬ StrictMono simultaneousBounce.time := ⟨repeatedEdge_proper, proper_walk_need_not_be_strict⟩

/--
---
conclusion: Lax330177.Examples.chain_failure
---
A single repeated edge admits a simultaneous return walk under properness.
-/
theorem chain_failure (m : TraversalMode) : ¬ (∀ u v z, Reaches backwardsChain m u v → Reaches backwardsChain m v z → Reaches backwardsChain m u z) := by cases m <;> first | exact strict_reachability_not_transitive | exact nonstrict_reachability_not_transitive
/--
---
conclusion: Lax330177.Representations.stream_edges
---
Sorting occurrences by departure time preserves precisely the active arcs.
-/
theorem stream_edges {n} (G : Graph n) (t : Fin G.lifetime) (u v : Fin n) : (streamOf G).snapshots.edge t u v ↔ G.edge t u v := by simp [streamOf, EventStream.snapshots, occurrences]
/--
---
conclusion: Lax330177.Durations.uniform_reaches
---
The same vertex and departure sequences witness reachability in both models.
-/
theorem uniform_reaches {n} (G : Graph n) (m : TraversalMode) (u v) : DurationReaches G (fun _ _ _ => if m = .strict then 1 else 0) u v ↔ Reaches G m u v := by
  constructor
  · rintro ⟨k,x,t,⟨hp,ha,ho⟩,hs,hf⟩
    exact ⟨k, ⟨x,t,ha,(uniform_modes (fun i => (t i).val) m).mp ho⟩, hp,hs,hf⟩
  · rintro ⟨k,w,hp,hs,hf⟩
    exact ⟨k,w.vertex,w.time,⟨hp,w.available,(uniform_modes _ m).mpr w.ordered⟩,hs,hf⟩
/--
---
conclusion: Lax330177.Paths.bidirect_paths
---
Reading each symmetric adjacency as a directed arc preserves the timed paths verbatim.
-/
theorem bidirect_paths {n s} (G : InterpretedGraph n s) (_ : s.direction = .undirected) (k : ℕ) : TemporalPath (bidirect G).graph s.mode k = TemporalPath G.graph s.mode k := rfl
/--
---
conclusion: Lax330177.Examples.simple_separation
---
Two arcs with the same unique label form a nonstrict path. A strict path cannot use both.
-/
theorem simple_separation : IsSimple simultaneousChain ∧ ¬ IsProper .directed simultaneousChain ∧ Reaches simultaneousChain .nonstrict 0 2 ∧ ¬ Reaches simultaneousChain .strict 0 2 := by
  refine ⟨fun _ _ _ _ _ _ => Subsingleton.elim .., ?_, ⟨2,chainPath,Function.injective_id,rfl,rfl⟩, ?_⟩
  · intro h
    have he := h.2 0 0 1 1 2 (by decide) (by decide) (by decide)
    exact (by unfold SameStaticEdge; decide : ¬ SameStaticEdge .directed (0 : Fin 3) 1 1 2) he
  · rintro ⟨k,w,hp,hs,hf⟩
    have hb := w.path_length_bound hp
    have hk : k ≤ 2 := by omega
    interval_cases k
    · exact (by decide : (0 : Fin 3) ≠ 2) (hs.symm.trans hf)
    · have he := w.available 0
      change simultaneousChain.edge _ w.start w.finish at he
      rw [hs,hf] at he
      simpa [simultaneousChain] using he
    · have h := w.ordered 0 1 (by decide)
      have e : w.time 0 = w.time 1 := Subsingleton.elim .. 
      rw [e] at h
      exact (lt_irrefl _) h
/--
---
conclusion: Lax330177.Examples.proper_separation
---
One repeated undirected edge is proper. Its two opposite arcs violate directed properness.
-/
theorem proper_separation : IsProper .undirected repeatedEdge ∧ ¬ IsSimple repeatedEdge ∧ ¬ IsProper .directed repeatedEdge := by
  refine ⟨repeatedEdge_proper, ?_, ?_⟩
  · intro h
    exact (by decide : (0 : Fin 2) ≠ 1) (h 0 1 0 1 (by decide) (by decide))
  · intro h
    exact (by unfold SameStaticEdge; decide : ¬ SameStaticEdge .directed (0 : Fin 2) 1 1 0)
      (h.2 0 0 1 1 0 (by decide) (by decide) (by decide))
/--
---
conclusion: Lax330177.Paths.walk_path_reach
---
Delete the segment between two appearances of the same vertex and induct on the walk length.
-/
theorem walk_path_reach {n} (G : Graph n) (m : TraversalMode) (u v) : WalkReaches G m u v ↔ Reaches G m u v := by
  classical
  constructor
  · rintro ⟨k,w,hs,hf⟩
    induction k using Nat.strong_induction_on with
    | h k ih =>
      by_cases hp : w.IsPath
      · exact ⟨k,w,hp,hs,hf⟩
      change ¬ Function.Injective w.vertex at hp
      simp only [Function.Injective, not_forall] at hp
      obtain ⟨a,b,hab⟩ := hp
      obtain ⟨he,hne⟩ := hab
      obtain ⟨a,b,hab,he⟩ : ∃ a b : Fin (k+1), a < b ∧ w.vertex a = w.vertex b := by
        rcases lt_or_gt_of_ne hne with h | h
        · exact ⟨a,b,h,he⟩
        · exact ⟨b,a,h,he.symm⟩
      let d := b.val - a.val
      have ha := a.isLt
      have hb := b.isLt
      change a.val < b.val at hab
      let idx (i : Fin (k-d)) : Fin k :=
        ⟨if i.val < a.val then i.val else i.val+d, by split <;> dsimp [d] at * <;> omega⟩
      let vx (i : Fin (k-d+1)) : Fin (k+1) :=
        ⟨if i.val ≤ a.val then i.val else i.val+d, by split <;> dsimp [d] at * <;> omega⟩
      let z : Walk G m (k-d) := {
        vertex := fun i => w.vertex (vx i)
        time := fun i => w.time (idx i)
        available := by
          intro i
          have h₁ : w.vertex (vx i.castSucc) = w.vertex (idx i).castSucc := by
            by_cases eq : i.val = a.val
            · convert he using 2 <;> apply Fin.ext <;> simp [vx,idx,eq,d] <;> omega
            · congr 1; apply Fin.ext; simp [vx,idx]; split <;> (try split) <;> omega
          have h₂ : vx i.succ = (idx i).succ := by
            apply Fin.ext; simp [vx,idx]; split <;> (try split) <;> omega
          rw [h₁,h₂]; exact w.available _
        ordered := by
          intro i j hij
          apply w.ordered
          change i.val < j.val at hij
          change (if i.val < a.val then i.val else i.val+d) < (if j.val < a.val then j.val else j.val+d)
          split <;> (try split) <;> omega }
      apply ih (k-d) (by dsimp [d]; omega) z
      · change w.vertex (vx 0) = u
        rw [show vx 0 = 0 by apply Fin.ext; simp [vx]]; exact hs
      · change w.vertex (vx (Fin.last (k-d))) = v
        by_cases h : k-d ≤ a.val
        · have h₁ : vx (Fin.last (k-d)) = a := by apply Fin.ext; simp [vx,h]; dsimp [d] at *; omega
          have h₂ : b = Fin.last k := by apply Fin.ext; simp; dsimp [d] at *; omega
          rw [h₁,he,h₂]; exact hf
        · have h₁ : vx (Fin.last (k-d)) = Fin.last k := by apply Fin.ext; simp [vx,h]; dsimp [d] at *; omega
          rw [h₁]; exact hf
  · rintro ⟨k,w,_,hs,hf⟩
    exact ⟨k,w,hs,hf⟩
/--
---
conclusion: Lax330177.Durations.uniform_paths
---
The correspondence fixes every vertex and every departure time.
-/
theorem uniform_paths {n k} (G : Graph n) (m : TraversalMode) (x : Fin (k+1) → Fin n) (t : Fin k → Fin G.lifetime) : DurationPath G (fun _ _ _ => if m = .strict then 1 else 0) x t ↔ ∃ w : TemporalPath G m k, w.val.vertex = x ∧ w.val.time = t := by
  constructor
  · rintro ⟨hp,ha,ho⟩
    exact ⟨⟨⟨x,t,ha,(uniform_modes _ m).mp ho⟩,hp⟩,rfl,rfl⟩
  · rintro ⟨⟨w,hp⟩,rfl,rfl⟩
    exact ⟨hp,w.available,(uniform_modes _ m).mpr w.ordered⟩
/--
---
conclusion: Lax330177.Paths.proper_path_times
---
Consecutive edges of a path are distinct incident edges, so properness excludes equal times.
-/
theorem proper_path_times {n k} (G : Graph n) (d : Direction) (hg : IsProper d G) (w : TemporalPath G .nonstrict k) : StrictMono w.val.time := w.val.proper_trail_strict d hg (w.val.path_staticTrail d w.property)
/--
---
conclusion: Lax330177.Representations.stream_roundtrip
---
The recovered stream has exactly the original occurrences and can differ only within tied timestamps.
-/
theorem stream_roundtrip {n h} (s : EventStream n h) : (streamOf s.snapshots).events.Perm s.events := by
  apply (List.perm_ext_iff_of_nodup (streamOf s.snapshots).unique s.unique).mpr
  rintro ⟨t,u,v⟩
  exact stream_edges s.snapshots t u v
/--
---
conclusion: Lax330177.Paths.support_reach
---
A realization of the same ordered vertex sequence preserves both endpoints.
-/
theorem support_reach {n} (G H : Graph n) (m l : TraversalMode) (h : SupportEquivalent G H m l) (u v) : Reaches G m u v ↔ Reaches H l u v := by
  constructor <;> rintro ⟨k,w,hp,hs,hf⟩
  · obtain ⟨z,hz⟩ := (h k w.vertex).mp ⟨⟨w,hp⟩,rfl⟩
    exact ⟨k,z.val,z.property,(congrFun hz 0).trans hs,(congrFun hz _).trans hf⟩
  · obtain ⟨z,hz⟩ := (h k w.vertex).mpr ⟨⟨w,hp⟩,rfl⟩
    exact ⟨k,z.val,z.property,(congrFun hz 0).trans hs,(congrFun hz _).trans hf⟩
end Lax330177Proofs.Basic




