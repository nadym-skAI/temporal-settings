import Lax330177.Examples

namespace Lax330177Proofs.Foundations
open Lax330177.Representations Lax330177.Paths Lax330177.Paths.Walk Lax330177.Settings Lax330177.Examples
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n k : ℕ} {G : Graph n} {mode : TraversalMode}

@[simp] theorem snapshot_label_edge {n : ℕ} (G : Graph n)
    (t : Fin G.lifetime) (u v : Fin n) :
    (toLabels G).toSnapshots.edge t u v ↔ G.edge t u v := by
  simp [toLabels, LabeledGraph.toSnapshots]

@[simp] theorem snapshot_roundtrip {n : ℕ} (G : Graph n) :
    (toLabels G).toSnapshots = G := by
  cases G with
  | mk l e h =>
    simp only [toLabels, LabeledGraph.toSnapshots]
    congr 1
    funext t u v
    exact propext ⟨fun h => (Finset.mem_filter.mp h).2,
      fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

@[simp] theorem label_roundtrip {n : ℕ} (G : LabeledGraph n) :
    toLabels G.toSnapshots = G := by
  cases G with
  | mk l e labels supported loopless =>
    dsimp [toLabels, LabeledGraph.toSnapshots, Footprint]
    congr 1
    · funext u v
      exact propext (supported u v).symm
    · funext u v
      calc
        _ = Finset.univ.filter (fun t => t ∈ labels u v) :=
          Finset.filter_congr_decidable _ _ _
        _ = labels u v := by ext t; simp

theorem nil_isPath (G : Graph n) (mode : TraversalMode) (v : Fin n) :
    (nil G mode v).IsPath := by intro i j _; apply Fin.ext; omega

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

theorem proper_path_strict (d : Direction) (w : Walk G .nonstrict k)
    (hg : IsProper d G) (hp : w.IsPath) : StrictMono w.time := by
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
  rw [← shared] at har
  have eq := hp (hg.2 _ _ _ _ (w.available i) har)
  have impossible := congrArg Fin.val eq
  change i.val = i.val + 1 + 1 at impossible
  omega

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

theorem reaches_refl {n : ℕ} (G : Graph n) (mode : TraversalMode) (u : Fin n) :
    Reaches G mode u u := ⟨0, Walk.nil G mode u, nil_isPath G mode u, rfl, rfl⟩

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

theorem bounce_temporalTrail : bounce.IsTemporalEdgeTrail .undirected :=
  strict_temporalTrail .undirected bounce

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
  · intro t u v z huv hvz
    fin_cases u <;> fin_cases v <;> fin_cases z <;> simp_all [repeatedEdge]

theorem proper_walk_need_not_be_strict : ¬ StrictMono simultaneousBounce.time := by
  intro h
  have he := h (show (0 : Fin 2) < 1 by decide)
  exact (lt_irrefl (0 : Fin 2)) he

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
  have hb := path_length_bound w hp
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
end
end Lax330177Proofs.Foundations
