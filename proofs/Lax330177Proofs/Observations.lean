import Lax330177
import Lax330177Proofs.Foundations

namespace Lax330177Proofs.Observations
open Lax330177.Representations Lax330177.Settings Lax330177.Paths Lax330177.Examples Lax330177Proofs.Foundations
variable {n k : ℕ} {G : Graph n} {mode : TraversalMode}

/--
---
conclusion: Lax330177.ActiveLabel.active_label
---
The label set collects exactly the appearance times of the ordered pair.
-/
theorem active_label (G : Graph n) (t : Fin G.lifetime) (u v : Fin n) : t ∈ (toLabels G).labels u v ↔ G.edge t u v := snapshot_label_edge G t u v

/--
---
conclusion: Lax330177.Reflexivity.reflexive
---
The zero-edge path at the vertex has no timing constraints.
-/
theorem reflexive (G : Graph n) (mode : TraversalMode) (u : Fin n) : Reaches G mode u u := reaches_refl G mode u

/--
---
conclusion: Lax330177.RestrictedMonotonicity.allowed_mono
---
Keep the path and use containment for each visited vertex.
-/
theorem allowed_mono {C D : Finset (Fin n)} (h : C ⊆ D) {u v} : ReachesIn G mode C u v → ReachesIn G mode D u v := reachesIn_mono h

/--
---
conclusion: Lax330177.UnrestrictedVertices.allow_all
---
Forget the restriction in one direction. Conversely, every vertex on the witnessing path belongs to the full set.
-/
theorem allow_all (G : Graph n) (mode : TraversalMode) (u v : Fin n) : ReachesIn G mode Finset.univ u v ↔ Reaches G mode u v := reachesIn_univ G mode u v

/--
---
conclusion: Lax330177.PathTrail.path_trail
---
Repeating a static edge forces an endpoint to occur at two different positions.
-/
theorem path_trail (d : Direction) (w : Walk G mode k) (h : w.IsPath) : w.IsStaticEdgeTrail d := path_staticTrail d w h

/--
---
conclusion: Lax330177.TrailInclusion.trail_inclusion
---
A repeated edge-time occurrence would use the same static edge twice.
-/
theorem trail_inclusion (d : Direction) (w : Walk G mode k) (h : w.IsStaticEdgeTrail d) : w.IsTemporalEdgeTrail d := staticTrail_temporalTrail d w h

/--
---
conclusion: Lax330177.StrictWalkTrail.strict_trail
---
Different traversals have different times.
-/
theorem strict_trail (d : Direction) (w : Walk G .strict k) : w.IsTemporalEdgeTrail d := strict_temporalTrail d w

/--
---
conclusion: Lax330177.TrailSeparation.trail_separation
---
The two occurrences have different times but use the same undirected edge.
-/
theorem trail_separation : bounce.IsTemporalEdgeTrail .undirected ∧ ¬ bounce.IsStaticEdgeTrail .undirected := ⟨bounce_temporalTrail,bounce_not_staticTrail⟩

/--
---
conclusion: Lax330177.SymmetricProper.symmetric_proper
---
Both conditions exclude exactly the same simultaneous two-step traversals with distinct outer vertices. Symmetry supplies the undirected graph condition.
-/
theorem symmetric_proper (G : Graph n) (h : IsUndirected G) : IsProper .directed G ↔ IsProper .undirected G := ⟨fun p => ⟨h,p.2⟩,fun p => ⟨trivial,p.2⟩⟩
open Lax330177.ReachabilityGraph

/--
---
conclusion: Lax330177.ProperReachGraphs.proper_graphs
---
Both graphs omit diagonal arcs. For distinct vertices, their adjacency agrees
because strict and nonstrict paths give the same reachability on a proper graph.
-/
theorem proper_graphs (G : Graph n) (d : Direction) (h : IsProper d G) :
    reachabilityGraph G .strict = reachabilityGraph G .nonstrict := by
  ext u v
  exact and_congr_right (fun _ => Lax330177.ProperModes.proper_modes G d h u v)

end Lax330177Proofs.Observations
