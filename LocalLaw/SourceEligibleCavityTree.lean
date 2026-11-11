import LocalLaw.SourceCavityTreeIdentity
import LocalLaw.AdmissibleEndpointPatches
import LocalLaw.SourceSingletonObservation
import LocalLaw.CavityDeletionAverage

/-!
# Every eligible sampled cavity has the exact finite tree iterate

The I-test supplies an actual outside tree patch and the I/J tests supply
the literal far-boundary mask. No additional F1 tree-center event is needed
for the eligible edge's old singleton-deleted cavity model.
-/

noncomputable section
namespace LocalLaw
local instance sourceEligibleCavityDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}

theorem source_cavity_tree_identity_of_outside_tree (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (b c : (Tᶜ : Set (Fin N)))
    (hbc : (outsideGraph g.graph T).Adj b c) (r : ℕ)
    (hTree : (graphBall (outsideGraph g.graph T) c (r + 1)).IsTree)
    (hfar : ∀ α : BoundaryOrientedEdge g.graph T,
      ((r + 2 : ℕ) : ℕ∞) < (outsideGraph g.graph T).edist b (boundaryOuterEndpoint g.graph T α))
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    ((g.deficient.delete T).deleteVertex b).P r z q
      ⟨c, hbc.ne.symm⟩ ⟨c, hbc.ne.symm⟩ = cavityIterate z q (r + 1) := by
  let D := g.deficient.delete T
  let cc : {v : (Tᶜ : Set (Fin N)) // v ≠ b} := ⟨c, hbc.ne.symm⟩
  have hzero : ∀ v ∈ graphBallVertices D.graph c (r + 1), D.deficit v = 0 :=
    fun v hv => g.singleton_common_ball_zero_deficit T b c hbc r hfar v hv
  have hlocal : (graphBall (D.deleteVertex b).graph cc r).IsTree := deleted_ball_isTree D.graph b cc r hTree
  have hdef : ∀ v ∈ graphBallVertices (D.deleteVertex b).graph cc r,
      (D.deleteVertex b).deficit v = if v = cc then 1 else 0 :=
    fun v hv => D.deleted_tree_ball_one_root_deficit b cc hbc r hTree hzero ⟨v, hv⟩
  have hsat : ∀ v ∈ graphBallVertices (D.deleteVertex b).graph cc r,
      (D.deleteVertex b).graph.degree v + (D.deleteVertex b).deficit v = d :=
    fun v _ => (D.deleteVertex_degree_deficit_sum b v).trans (g.deleted_degree_deficit_saturated T v.val)
  exact (D.deleteVertex b).homogeneous_cavity_P_diagonal hd cc r hlocal hdef hsat q z hz hq

end RegularGraph

namespace LabelledResamplingState
variable {N d : ℕ} {T : Set (Fin N)} {ι : Type*}

/-- The actual old finite cavity model at every eligible sampled edge is
Y_(r+1), for all physical boundary parameters. -/
theorem eligible_cavity_tree_identity (s : LabelledResamplingState (Fin N) T ι)
    (hregular : s.graph.IsRegularOfDegree d) (hd : 3 ≤ d) (selector r : ℕ) (hr : r + 2 ≤ selector)
    (i : s.AdmissibleSampleIndex selector) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let g : RegularGraph N d := ⟨s.graph, hregular⟩
    let b := s.admissibleSampleVertex selector i
    let c := s.admissibleSecondVertex selector i
    let cc : {v : (Tᶜ : Set (Fin N)) // v ≠ b} :=
      ⟨c, fun h => (s.samples (s.boundary i.val)).property.1.ne' (congrArg Subtype.val h)⟩
    ((g.deficient.delete T).deleteVertex b).P r z q cc cc = cavityIterate z q (r + 1) := by
  dsimp only
  let g : RegularGraph N d := ⟨s.graph, hregular⟩
  let H := outsideGraph s.graph T
  let b := s.admissibleSampleVertex selector i
  let c := s.admissibleSecondVertex selector i
  have hbc : H.Adj b c := (s.samples (s.boundary i.val)).property.1
  have hpatch := s.sampledEndpointPatch_isTree selector (r + 1) (by omega) i
  have hsub : graphBallVertices H c (r + 1) ⊆ s.sampledEndpointPatch selector (r + 1) i := by
    intro v hv
    exact ⟨c, Or.inr rfl, hv⟩
  have htree : (graphBall H c (r + 1)).IsTree := by
    refine ⟨graphBall_connected _ _ _, ?_⟩
    intro v p hp
    let f := H.induceHomOfLE hsub
    exact hpatch.IsAcyclic (p.map f.toHom) (hp.map f.injective)
  have hfar : ∀ α : BoundaryOrientedEdge s.graph T,
      ((r + 2 : ℕ) : ℕ∞) < H.edist b (boundaryOuterEndpoint s.graph T α) := by
    intro α
    exact lt_of_le_of_lt (ENat.coe_le_coe.mpr hr) ((s.admissibleSampleVertex_far_boundary selector i) α)
  exact g.source_cavity_tree_identity_of_outside_tree hd T b c hbc r htree hfar q z hz hq

/-- For every eligible edge the source mask is automatically true and its
actual finite cavity model is Y. No exceptional-tree event is required. -/
theorem eligible_sourceSingletonObservation_eq (s : LabelledResamplingState (Fin N) T ι)
    (hregular : s.graph.IsRegularOfDegree d) (hd : 3 ≤ d) (selector r : ℕ) (hr : r + 2 ≤ selector)
    (i : s.AdmissibleSampleIndex selector) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    RegularGraph.sourceSingletonObservation (⟨s.graph, hregular⟩ : RegularGraph N d) T r selector z q
      (s.samples (s.boundary i.val)) =
        outsideOrientedCavityValue s.graph d T z (s.samples (s.boundary i.val)) - cavityIterate z q (r + 1) := by
  let g : RegularGraph N d := ⟨s.graph, hregular⟩
  let D := g.deficient.delete T
  let b := s.admissibleSampleVertex selector i
  let c := s.admissibleSecondVertex selector i
  let hbc : (outsideGraph s.graph T).Adj b c := (s.samples (s.boundary i.val)).property.1
  let cc : {v : (Tᶜ : Set (Fin N)) // v ≠ b} := ⟨c, hbc.ne.symm⟩
  have hmodel := s.eligible_cavity_tree_identity hregular hd selector r hr i q z hz hq
  have hfar := s.admissibleSampleVertex_far_boundary selector i
  change (D.deleteVertex b).P r z q cc cc = cavityIterate z q (r + 1) at hmodel
  change ∀ α : BoundaryOrientedEdge s.graph T,
    (selector : ℕ∞) < (outsideGraph s.graph T).edist b (boundaryOuterEndpoint s.graph T α) at hfar
  have hphysical : (D.deleteVertex b).G z cc cc =
      outsideOrientedCavityValue s.graph d T z (s.samples (s.boundary i.val)) := by
    rw [D.deleteVertex_G, outsideOrientedCavityValue_eq_deleted s.graph d T z hz (s.samples (s.boundary i.val))]
    rfl
  change (if (∀ α : BoundaryOrientedEdge s.graph T,
      (selector : ℕ∞) < (outsideGraph s.graph T).edist b (boundaryOuterEndpoint s.graph T α)) then
      (D.deleteVertex b).G z cc cc - (D.deleteVertex b).P r z q cc cc else 0) = _
  rw [if_pos hfar, hmodel, hphysical]

end LabelledResamplingState
end LocalLaw
