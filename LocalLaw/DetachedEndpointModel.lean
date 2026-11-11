import LocalLaw.EndpointBranchDeficits
import LocalLaw.SourceEligibleCavityTree
import LocalLaw.PostBranchComponents

/-! # The actual detached endpoint block is the genuine cavity model

An accepted c-branch is isolated in the switched common model, with exactly
the one-root inherited deficit. Its finite graph is the literal old cavity
ball, so its diagonal is the scalar tree iterate.
-/

noncomputable section
set_option maxHeartbeats 2600000
namespace LocalLaw
local instance detachedEndpointModelDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*}

def induceSetIso (G : SimpleGraph V) (S S' : Set V) (h : S = S') : G.induce S ≃g G.induce S' where
  toEquiv :=
    { toFun := fun x => ⟨x.val, h ▸ x.property⟩
      invFun := fun x => ⟨x.val, h.symm ▸ x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := Iff.rfl

def sameVertexGraphIso (G H : SimpleGraph V) (h : G = H) : G ≃g H where
  toEquiv := Equiv.refl V
  map_rel_iff' := by subst H; exact Iff.rfl

def deletedBallAmbientIso (G : SimpleGraph V) (b : V) (c : {v : V // v ≠ b}) (r : ℕ) :
    graphBall (G.induce {v | v ≠ b}) c r ≃g G.induce (vertexDeletedBallAmbient G b c r) where
  toEquiv := Equiv.ofInjective (fun x : graphBallVertices (G.induce {v | v ≠ b}) c r => x.val.val)
    (fun _ _ h => Subtype.ext (Subtype.ext h))
  map_rel_iff' := Iff.rfl

namespace BranchAttachmentData
variable {I : Type*} {old post : SimpleGraph V}

theorem C_edge_closed (D : BranchAttachmentData V I old post) (i : I)
    {u v : V} (hu : u ∈ D.C i) (h : post.Adj u v) : v ∈ D.C i := by
  by_cases hv : v ∈ D.core
  · exact False.elim (D.core_C_no_cut i hv hu h.symm)
  · exact D.C_closed_outside_core i hu hv h

theorem C_cut (D : BranchAttachmentData V I old post) (i : I) :
    ∀ u ∈ D.C i, ∀ v ∉ D.C i, ¬post.Adj u v := by
  intro u hu v hv h
  exact hv (D.C_edge_closed i hu h)

end BranchAttachmentData

namespace LabelledResamplingState
variable {T : Set V} {ι : Type*} [Fintype ι]

theorem sampledSecondBranch_post_graph_eq (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2 * r + 2 ≤ selector) (i : s.AdmissibleSampleIndex selector) :
    (outsideGraph (s.fullResample selector).graph T).induce (s.sampledSecondBranch selector r i) =
      (outsideGraph s.graph T).induce (s.sampledSecondBranch selector r i) := by
  let D := s.endpointBranchAttachmentData selector r hsep
  have h := s.endpoint_C_graph_eq selector r hsep i
  ext x y
  let xx : D.C i := ⟨⟨x.val, s.sampledEndpointPatch_subset_model selector r i
    (s.sampledSecondBranch_subset selector r i x.property)⟩, x.property⟩
  let yy : D.C i := ⟨⟨y.val, s.sampledEndpointPatch_subset_model selector r i
    (s.sampledSecondBranch_subset selector r i y.property)⟩, y.property⟩
  exact Iff.of_eq (congrArg (fun G => G.Adj xx yy) h)

def detachedBranchBallIso (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2 * r + 2 ≤ selector) (i : s.AdmissibleSampleIndex selector) :
    graphBall ((outsideGraph s.graph T).induce {v | v ≠ s.admissibleSampleVertex selector i})
      (⟨s.admissibleSecondVertex selector i,
        (show (outsideGraph s.graph T).Adj (s.admissibleSampleVertex selector i)
          (s.admissibleSecondVertex selector i) from (s.samples (s.boundary i.val)).property.1).ne.symm⟩ :
          {v : (Tᶜ : Set V) // v ≠ s.admissibleSampleVertex selector i}) r ≃g
      (s.endpointPostGraph selector r).induce ((s.endpointBranchAttachmentData selector r hsep).C i) :=
  (deletedBallAmbientIso _ _ _ r).trans
    ((induceSetIso _ _ _ (s.sampledSecondBranch_eq_deleted_ball selector r (by omega) i).symm).trans
      ((sameVertexGraphIso _ _ (s.sampledSecondBranch_post_graph_eq selector r hsep i).symm).trans
        (inducePreimageIso (outsideGraph (s.fullResample selector).graph T)
          (s.endpointModelVertices selector r) (s.sampledSecondBranch selector r i)
          ((s.sampledSecondBranch_subset selector r i).trans
            (s.sampledEndpointPatch_subset_model selector r i))).symm))

end LabelledResamplingState

namespace DeficientGraph
variable {A : Type} [Fintype A] [DecidableEq A] {d : ℕ}

theorem P_diagonal_eq_ball (g : DeficientGraph A d) (root : A) (r : ℕ) (q z : ℂ) :
    g.P r z q root root = (g.restrict (graphBallVertices g.graph root r)).extensionGreen q z
      (cavityBallRoot g.graph root r) (cavityBallRoot g.graph root r) := by
  let e : pairBallGraph g.graph root root r ≃g graphBall g.graph root r :=
    { toFun := fun x => ⟨x.val, x.property.elim id id⟩
      invFun := fun x => ⟨x.val, Or.inl x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  have h := (g.restrict (graphBallVertices g.graph root r)).extensionGreen_iso
    (g.restrict (pairBallVertices g.graph root root r)) e (fun _ => rfl) q z
  exact (congrFun (congrFun h (pairBallLeft g.graph root root r)) (pairBallRight g.graph root root r)).symm

end DeficientGraph

namespace RegularGraph
variable {N d : ℕ} {ι : Type*} [Fintype ι]

def switchedEndpointModel (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) : DeficientGraph
      ((g.admissibleState T boundary S).endpointModelVertices selector r) d :=
  ((g.labelledResampledGraph T boundary S selector).deficient.delete T).restrict
    ((g.admissibleState T boundary S).endpointModelVertices selector r)

theorem detachedBranchBall_deficit_match (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector)
    (i : (g.admissibleState T boundary S).AdmissibleSampleIndex selector) :
    let s := g.admissibleState T boundary S
    let b := s.admissibleSampleVertex selector i
    let c := s.admissibleSecondVertex selector i
    let cc : {v : (Tᶜ : Set (Fin N)) // v ≠ b} :=
      ⟨c, (show (outsideGraph g.graph T).Adj b c from (S (boundary i.val)).property.1).ne.symm⟩
    let old := ((g.deficient.delete T).deleteVertex b).restrict
      (graphBallVertices ((g.deficient.delete T).deleteVertex b).graph cc r)
    let post := (g.switchedEndpointModel T boundary S selector r).restrict
      ((s.endpointBranchAttachmentData selector r hsep).C i)
    ∀ x, old.deficit x = post.deficit (s.detachedBranchBallIso selector r hsep i x) := by
  dsimp only
  let s := g.admissibleState T boundary S
  let H := outsideGraph g.graph T
  let b := s.admissibleSampleVertex selector i
  let c := s.admissibleSecondVertex selector i
  let e := s.detachedBranchBallIso selector r hsep i
  intro x
  have hxc : x.val.val ∈ s.sampledSecondBranch selector r i := (e x).property
  have hzero := g.sampledEndpointPatch_zero_deficit T boundary S selector r (by omega) i x.val.val
    (s.sampledSecondBranch_subset selector r i hxc)
  have hpost := g.endpoint_C_one_root_deficit T boundary S selector r hsep i x.val.val hxc
  have hiff : H.Adj b x.val.val ↔ x.val.val = c := by
    constructor
    · intro ha
      have hc := (s.sampledBranch_old_cross_iff selector r (by omega) i
        (s.admissibleSampleVertex_mem_firstBranch selector r i) hxc).mp ha
      rcases (SimpleGraph.edge_adj _ _ _ _).mp hc with ⟨he, _⟩
      rcases he with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact False.elim ((S (boundary i.val)).property.1.ne (congrArg Subtype.val h))
    · intro he
      simpa only [he] using (show H.Adj b c from (S (boundary i.val)).property.1)
  change ((g.deficient.delete T).deleteVertex b).deficit x.val =
    ((g.labelledResampledGraph T boundary S selector).deficient.delete T).deficit x.val.val
  rw [(g.deficient.delete T).deleteVertex_deficit_eq_adj, hzero, zero_add, hpost]
  by_cases hv : x.val.val = c
  · have ha : (g.deficient.delete T).graph.Adj b x.val.val := hiff.mpr hv
    rw [if_pos hv, if_pos ha]
  · have ha : ¬(g.deficient.delete T).graph.Adj b x.val.val := fun h => hv (hiff.mp h)
    rw [if_neg hv, if_neg ha]

theorem switchedEndpointModel_tip_diagonal (g : RegularGraph N d) (hd : 3 ≤ d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector) (hr : r + 2 ≤ selector)
    (i : (g.admissibleState T boundary S).AdmissibleSampleIndex selector)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let s := g.admissibleState T boundary S
    (g.switchedEndpointModel T boundary S selector r).extensionGreen q z
      (s.endpointTipVertex selector r i) (s.endpointTipVertex selector r i) = cavityIterate z q (r + 1) := by
  dsimp only
  let s := g.admissibleState T boundary S
  let b := s.admissibleSampleVertex selector i
  let c := s.admissibleSecondVertex selector i
  let cc : {v : (Tᶜ : Set (Fin N)) // v ≠ b} :=
    ⟨c, (show (outsideGraph g.graph T).Adj b c from (S (boundary i.val)).property.1).ne.symm⟩
  let old := ((g.deficient.delete T).deleteVertex b).restrict
    (graphBallVertices ((g.deficient.delete T).deleteVertex b).graph cc r)
  let M := g.switchedEndpointModel T boundary S selector r
  let D := s.endpointBranchAttachmentData selector r hsep
  let post := M.restrict (D.C i)
  let e := s.detachedBranchBallIso selector r hsep i
  let root := cavityBallRoot ((g.deficient.delete T).deleteVertex b).graph cc r
  have hdef : ∀ x, old.deficit x = post.deficit (e x) :=
    g.detachedBranchBall_deficit_match T boundary S selector r hsep i
  have hiso := post.extensionGreen_iso old e hdef q z
  have hentry : post.extensionGreen q z (e root) (e root) = old.extensionGreen q z root root :=
    congrFun (congrFun hiso root) root
  have hblock := M.restrict_extensionGreen_of_isolated hd (D.C i) (D.C_cut i) q z hz hq
  have hfull : post.extensionGreen q z (e root) (e root) = M.extensionGreen q z
      (s.endpointTipVertex selector r i) (s.endpointTipVertex selector r i) :=
    congrFun (congrFun hblock (e root)) (e root)
  have hold := ((g.deficient.delete T).deleteVertex b).P_diagonal_eq_ball cc r q z
  have hY := s.eligible_cavity_tree_identity g.regular hd selector r hr i q z hz hq
  change ((g.deficient.delete T).deleteVertex b).P r z q cc cc = cavityIterate z q (r + 1) at hY
  exact hfull.symm.trans (hentry.trans (hold.symm.trans hY))

theorem switchedEndpointModel_tip_zero_across_branch (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector)
    (i : (g.admissibleState T boundary S).AdmissibleSampleIndex selector)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (x : (g.admissibleState T boundary S).endpointModelVertices selector r)
    (hx : x.val ∉ (g.admissibleState T boundary S).sampledSecondBranch selector r i) :
    let s := g.admissibleState T boundary S
    (g.switchedEndpointModel T boundary S selector r).extensionGreen q z
      (s.endpointTipVertex selector r i) x = 0 := by
  dsimp only
  let s := g.admissibleState T boundary S
  let D := s.endpointBranchAttachmentData selector r hsep
  exact (g.switchedEndpointModel T boundary S selector r).extensionGreen_zero_across_cut hd
    (D.C i) (D.C_cut i) q z hz hq (s.endpointTipVertex selector r i)
    (D.tip_mem i) x hx

end RegularGraph
end LocalLaw
