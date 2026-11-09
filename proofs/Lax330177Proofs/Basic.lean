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
Fix a time and an ordered pair of vertices. The label set of that pair contains the time exactly when the original snapshot contains the arc. Reconstructing the snapshot tests this same membership, so it recovers every arc at every time. The lifetime is copied as well, even when the final snapshot is empty.
-/
theorem snapshots_labels {n} (G : Graph n) : (toLabels G).toSnapshots = G := snapshot_roundtrip G

/--
---
conclusion: Lax330177.Representations.labels_snapshots
---
An arc appears in the reconstructed snapshot at time t exactly when t belongs to its original label set. Collecting its appearance times therefore recovers that set. The footprint is recovered too, since its edges are precisely the pairs with nonempty label sets, and both conversions preserve the lifetime.
-/
theorem labels_snapshots {n} (G : LabeledGraph n) : toLabels G.toSnapshots = G := label_roundtrip G

/--
---
conclusion: Lax330177.Paths.strict_inclusion
---
Take a strict path between the two vertices and keep its vertices and departure times. Every strict increase is also a weak increase, so the same path witnesses nonstrict reachability.
-/
theorem strict_inclusion {n} {G : Graph n} {u v} : Reaches G .strict u v → Reaches G .nonstrict u v := strict_reaches_nonstrict

/--
---
conclusion: Lax330177.Paths.proper_modes
---
A strict path also satisfies the nonstrict timing rule. For the converse, take a nonstrict path. Consecutive edges meet at a vertex and are distinct because a path never repeats a vertex. Properness prevents them from appearing at the same time. Their weakly increasing times must therefore increase strictly, giving a strict path with the same endpoints.
-/
theorem proper_modes {n} (G : Graph n) (d : Direction) (h : IsProper d G) (u v) : Reaches G .strict u v ↔ Reaches G .nonstrict u v := proper_reaches_iff d h u v

/--
---
conclusion: Lax330177.Durations.uniform_modes
---
Suppose one traversal departs at time a and a later traversal departs at b. With traversal time zero the first arrival is a, so feasibility requires a ≤ b. With traversal time one the arrival is a + 1. Since timestamps are integers, a + 1 ≤ b holds exactly when a < b. Applying this to every pair of steps gives both equivalences.
-/
theorem uniform_modes {k} (t : Fin k → ℕ) (m : TraversalMode) : Feasible t (fun _ => if m = .strict then 1 else 0) ↔ ∀ i j, i < j → TimeLE m (t i) (t j) := by cases m <;> simp [Feasible, TimeLE]

/--
---
conclusion: Lax330177.Examples.bounce_same_time
---
Use a graph on two vertices with one undirected edge. It is proper because there is no second edge incident to either endpoint. A walk can cross that edge and immediately cross it back at the same timestamp. Its two equal departure times satisfy the nonstrict rule and violate the strict rule.
-/
theorem bounce_same_time : IsProper .undirected repeatedEdge ∧ ¬ StrictMono simultaneousBounce.time := ⟨repeatedEdge_proper, proper_walk_need_not_be_strict⟩

/--
---
conclusion: Lax330177.Examples.chain_failure
---
On the undirected chain 0–1–2, edge 0–1 appears at time 1 and edge 1–2 at time 0. Each edge alone gives reachability between its endpoints in either mode. But the only path from 0 to 2 would have to use time 1 before time 0. Thus 0 reaches 1 and 1 reaches 2, while 0 cannot reach 2.
-/
theorem chain_failure (m : TraversalMode) : ¬ (∀ u v z, Reaches backwardsChain m u v → Reaches backwardsChain m v z → Reaches backwardsChain m u z) := by cases m <;> first | exact strict_reachability_not_transitive | exact nonstrict_reachability_not_transitive
/--
---
conclusion: Lax330177.Representations.stream_edges
---
List one event for every arc in every snapshot, then sort the list by time. Sorting preserves membership. Looking for the event with time t and endpoints u and v therefore succeeds exactly when the original snapshot at t contains the arc from u to v.
-/
theorem stream_edges {n} (G : Graph n) (t : Fin G.lifetime) (u v : Fin n) : (streamOf G).snapshots.edge t u v ↔ G.edge t u v := by simp [streamOf, EventStream.snapshots, occurrences]
/--
---
conclusion: Lax330177.Durations.uniform_reaches
---
Choose a path witnessing reachability. With uniform traversal time one, feasibility requires strictly increasing integer departures. With time zero, it requires weakly increasing departures. In either case the same timed path witnesses reachability in the corresponding mode. Reading the timing equivalence in reverse gives the converse.
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
An undirected snapshot allows each active edge to be traversed in either direction. Replacing it by its two directed arcs permits exactly the same ordered steps at exactly the same times. The conditions on repeated vertices and on departure order are unchanged, so every timed path is preserved in both directions.
-/
theorem bidirect_paths {n s} (G : InterpretedGraph n s) (_ : s.direction = .undirected) (k : ℕ) : TemporalPath (bidirect G).graph s.mode k = TemporalPath G.graph s.mode k := rfl
/--
---
conclusion: Lax330177.Examples.simple_separation
---
Let the only arcs be 0 → 1 and 1 → 2, both at time 0. Each has one label, so the graph is simple. They meet at vertex 1 at the same time, so it fails properness. Taking both arcs at time 0 reaches vertex 2 nonstrictly from 0. A strict path would need two distinct times, since there is no direct arc.
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
Let the single undirected edge between 0 and 1 appear at times 0 and 1. Each snapshot contains just that edge, so the graph is proper. Its two labels violate simplicity. If we read the same snapshots as directed, the two opposite arcs are distinct and simultaneous and share endpoints, violating directed properness.
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
If a walk visits a vertex twice, delete the steps between those visits. The remaining prefix and suffix join at the same vertex. Their departure times form a subsequence of the original times, so they still satisfy the chosen timing rule. Each deletion shortens the walk and preserves its endpoints. Eventually no vertex repeats, giving a path. Conversely, every path is already a walk.
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
Fix the vertex sequence and its departure times. Both path definitions require distinct vertices and an available edge at every departure. For uniform time zero, arrival before or at the next departure means that departure times are weakly increasing. For uniform time one, it means that the integer times are strictly increasing. Thus the same sequences satisfy either description exactly in the stated mode.
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
Two consecutive edges of a path share their middle vertex. They must be distinct, since traversing the same edge twice would repeat a vertex. Properness therefore forbids equal departure times on consecutive edges. Since the times are already weakly increasing, each is strictly smaller than its successor.
-/
theorem proper_path_times {n k} (G : Graph n) (d : Direction) (hg : IsProper d G) (w : TemporalPath G .nonstrict k) : StrictMono w.val.time := w.val.proper_trail_strict d hg (w.val.path_staticTrail d w.property)
/--
---
conclusion: Lax330177.Representations.stream_roundtrip
---
Forming snapshots from the stream records exactly which triples of time and endpoints occur. Converting back lists each recorded triple once. The original stream also lists each triple once, so the two lists are permutations of each other. Both are chronological, hence their orders can differ only among events at the same time.
-/
theorem stream_roundtrip {n h} (s : EventStream n h) : (streamOf s.snapshots).events.Perm s.events := by
  apply (List.perm_ext_iff_of_nodup (streamOf s.snapshots).unique s.unique).mpr
  rintro ⟨t,u,v⟩
  exact stream_edges s.snapshots t u v
/--
---
conclusion: Lax330177.Paths.support_reach
---
Take the ordered vertex sequence of a path witnessing reachability in the first graph. Support equivalence supplies a path with that same sequence in the second graph, so its first and last vertices are the required endpoints. Exchanging the graphs proves the reverse implication.
-/
theorem support_reach {n} (G H : Graph n) (m l : TraversalMode) (h : SupportEquivalent G H m l) (u v) : Reaches G m u v ↔ Reaches H l u v := by
  constructor <;> rintro ⟨k,w,hp,hs,hf⟩
  · obtain ⟨z,hz⟩ := (h k w.vertex).mp ⟨⟨w,hp⟩,rfl⟩
    exact ⟨k,z.val,z.property,(congrFun hz 0).trans hs,(congrFun hz _).trans hf⟩
  · obtain ⟨z,hz⟩ := (h k w.vertex).mpr ⟨⟨w,hp⟩,rfl⟩
    exact ⟨k,z.val,z.property,(congrFun hz 0).trans hs,(congrFun hz _).trans hf⟩
/--
---
conclusion: Lax330177.Examples.happy_asymmetry
---
Give the undirected edge 1–2 time 0 and the edge 0–1 time 1. Each edge has one label and each snapshot contains just one edge, so the graph is happy. From 2 to 0 the chain uses times 0 then 1, valid in both modes. From 0 to 2 the only possible path requires those times in decreasing order.
-/
theorem happy_asymmetry (m : TraversalMode) : IsHappy .undirected backwardsChain ∧ Reaches backwardsChain m 2 0 ∧ ¬ Reaches backwardsChain m 0 2 := by
  have happy : IsHappy .undirected backwardsChain := by
    dsimp [IsHappy, IsSimple, IsProper, ValidDirection, IsUndirected, SameStaticEdge, backwardsChain]
    constructor
    · intro u v t s ht hs; grind
    · constructor
      · intro t u v; grind
      · intro t u v x y huv hxy hshare; grind
  have hr : Reaches backwardsChain .strict 2 0 :=
    ⟨2,reverseChainPath,by change Function.Injective ![(2 : Fin 3),1,0]; decide,rfl,rfl⟩
  exact ⟨happy,by cases m <;> first | exact hr | exact strict_reaches_nonstrict hr,not_reaches_endpoints m⟩
end Lax330177Proofs.Basic







