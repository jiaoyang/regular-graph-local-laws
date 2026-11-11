import LocalLaw.EndpointInternalGraphs
import LocalLaw.TreePairCutRadius

/-! # Genuine post-switch branch trees and the detached cavity vertex set -/

noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance endpointBranchTreesDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*}

def inducePreimageIso (G : SimpleGraph V) (K S : Set V) (hSK : S ⊆ K) :
    ((G.induce K).induce {x | x.val ∈ S}) ≃g G.induce S where
  toEquiv :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      invFun := fun x => ⟨⟨x.val, hSK x.property⟩, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := Iff.rfl

theorem induce_preimage_isTree (G : SimpleGraph V) (K S : Set V) (hSK : S ⊆ K)
    (hS : (G.induce S).IsTree) : ((G.induce K).induce {x | x.val ∈ S}).IsTree := by
  let e := inducePreimageIso G K S hSK
  constructor
  · exact e.connected_iff.mpr hS.isConnected
  · intro v p hp
    exact hS.IsAcyclic (p.map e.toHom) (hp.map e.injective)

theorem inducedTreeBranch_set_congr (G : SimpleGraph V) (W W' : Set V) (h : W = W')
    (a b root : W) :
    inducedTreeBranch G W a b root = inducedTreeBranch G W'
      ⟨a.val, h ▸ a.property⟩ ⟨b.val, h ▸ b.property⟩ ⟨root.val, h ▸ root.property⟩ := by
  subst W'
  rfl

namespace LabelledResamplingState
variable {T : Set V} {ι : Type*} [Fintype ι]

theorem endpoint_B_isTree (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2 * r + 2 ≤ selector) (i : s.AdmissibleSampleIndex selector) :
    let D := s.endpointBranchAttachmentData selector r hsep
    ((s.endpointPostGraph selector r).induce (D.B i)).IsTree := by
  dsimp only
  rw [s.endpoint_B_graph_eq selector r hsep i]
  exact induce_preimage_isTree (outsideGraph s.graph T) _ _
    ((s.sampledFirstBranch_subset selector r i).trans (s.sampledEndpointPatch_subset_model selector r i))
    (s.sampledFirstBranch_isTree selector r (by omega) i)

theorem endpoint_C_isTree (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2 * r + 2 ≤ selector) (i : s.AdmissibleSampleIndex selector) :
    let D := s.endpointBranchAttachmentData selector r hsep
    ((s.endpointPostGraph selector r).induce (D.C i)).IsTree := by
  dsimp only
  rw [s.endpoint_C_graph_eq selector r hsep i]
  exact induce_preimage_isTree (outsideGraph s.graph T) _ _
    ((s.sampledSecondBranch_subset selector r i).trans (s.sampledEndpointPatch_subset_model selector r i))
    (s.sampledSecondBranch_isTree selector r (by omega) i)

omit [Fintype ι] in
theorem sampledSecondBranch_eq_deleted_ball (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hr : r ≤ selector) (i : s.AdmissibleSampleIndex selector) :
    s.sampledSecondBranch selector r i =
      vertexDeletedBallAmbient (outsideGraph s.graph T) (s.admissibleSampleVertex selector i)
        ⟨s.admissibleSecondVertex selector i,
          (show (outsideGraph s.graph T).Adj (s.admissibleSampleVertex selector i)
            (s.admissibleSecondVertex selector i) from (s.samples (s.boundary i.val)).property.1).ne.symm⟩ r := by
  let H := outsideGraph s.graph T
  let b := s.admissibleSampleVertex selector i
  let c := s.admissibleSecondVertex selector i
  have hset := s.sampledEndpointPatch_eq_pairBall selector r i
  have htree : (pairBallGraph H b c r).IsTree := by
    change ((outsideGraph s.graph T).induce
      (pairBallVertices (outsideGraph s.graph T) (s.admissibleSampleVertex selector i)
        (s.admissibleSecondVertex selector i) r)).IsTree
    rw [← hset]
    exact s.sampledEndpointPatch_isTree selector r hr i
  have hmain := tree_pair_second_branch_eq_deleted_ball H b c r
    (s.samples (s.boundary i.val)).property.1 htree
  exact (inducedTreeBranch_set_congr H _ _ hset
    (s.sampledPatchFirst selector r i) (s.sampledPatchSecond selector r i)
    (s.sampledPatchSecond selector r i)).trans hmain

end LabelledResamplingState
end LocalLaw
