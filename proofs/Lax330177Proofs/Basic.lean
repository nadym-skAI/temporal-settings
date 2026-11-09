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
theorem uniform_modes {k} (t : Fin k → ℕ) (m : TraversalMode) : Feasible t (fun _ => if m = .strict then 1 else 0) ↔ ∀ i j, i < j → TimeLE m (t i) (t j) := by cases m <;> simp [Feasible, TimeLE, Nat.succ_le_iff]

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
end Lax330177Proofs.Basic
