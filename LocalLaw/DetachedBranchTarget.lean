import LocalLaw.DetachedEndpointModel
import LocalLaw.IsolatedBranchAugmentation
import LocalLaw.SingleTargetOutsideLocality

/-! # Actual accepted c-branches stay isolated from distant outside targets -/

noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance detachedBranchTargetDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} [Fintype V] {T : Set V} {ι : Type*} [Fintype ι]

omit [Fintype V] in
theorem sampledSecondBranch_post_radial (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2*r+2≤selector) (i : s.AdmissibleSampleIndex selector)
    (v : (Tᶜ:Set V)) (hv : v∈s.sampledSecondBranch selector r i) :
    (outsideGraph (s.fullResample selector).graph T).edist (s.admissibleSecondVertex selector i) v≤(r:ℕ∞) := by
  let b := s.admissibleSampleVertex selector i
  let c := s.admissibleSecondVertex selector i
  let cc : {v : (Tᶜ:Set V) // v≠b} :=
    ⟨c,(show (outsideGraph s.graph T).Adj b c from (s.samples (s.boundary i.val)).property.1).ne.symm⟩
  let H := (outsideGraph s.graph T).induce {v | v≠b}
  let e := s.detachedBranchBallIso selector r hsep i
  let D := s.endpointBranchAttachmentData selector r hsep
  let vc : D.C i :=
    ⟨⟨v,s.sampledEndpointPatch_subset_model selector r i (s.sampledSecondBranch_subset selector r i hv)⟩,hv⟩
  let vb := e.symm vc
  obtain ⟨p,hp⟩ := graphBall_walk_from_center H cc r vb
  let f : graphBall H cc r →g outsideGraph (s.fullResample selector).graph T :=
    { toFun := fun x => (e x).val.val
      map_rel' := fun h => e.toHom.map_rel h }
  have hroot : f (cavityBallRoot H cc r)=c := rfl
  have htarget : f vb=v := by
    change (e (e.symm vc)).val.val=v
    rw [e.apply_symm_apply]
  have hh := (outsideGraph (s.fullResample selector).graph T).edist_le (p.map f)
  have hh' := hh.trans (by simpa only [SimpleGraph.Walk.length_map] using ENat.coe_le_coe.mpr hp)
  change (outsideGraph (s.fullResample selector).graph T).edist (f (cavityBallRoot H cc r)) (f vb)≤(r:ℕ∞) at hh'
  simpa only [hroot,htarget] using hh' 

end LabelledResamplingState

namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem singleTargetOutside_tip_zero (g : RegularGraph N d) (hd : 3≤d)
    (T : Set (Fin N)) (labels : ι≃BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T) (selector r : ℕ) (hsep : 2*r+2≤selector)
    (i : (g.admissibleState T labels samples).AdmissibleSampleIndex selector)
    (j : Fin N) (hj : j∉T)
    (hfar : ((2*r+1:ℕ):ℕ∞)<(outsideGraph (g.labelledResampledGraph T labels samples selector).graph T).edist
      ((g.admissibleState T labels samples).admissibleSecondVertex selector i) ⟨j,hj⟩)
    (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im)
    (x : g.singleTargetOutsideVertices T labels samples selector r j)
    (hx : x.val=(g.admissibleState T labels samples).admissibleSecondVertex selector i) :
    (((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict
      (g.singleTargetOutsideVertices T labels samples selector r j)).extensionGreen q z x
        (g.singleTargetOutsideTargetVertex T labels samples selector r j hj)=0 := by
  let s := g.admissibleState T labels samples
  let gnew := g.labelledResampledGraph T labels samples selector
  let K := s.endpointModelVertices selector r
  let C := s.sampledSecondBranch selector r i
  let A := g.singleTargetOutsideVertices T labels samples selector r j
  let M := (gnew.deficient.delete T).restrict A
  let H := outsideGraph gnew.graph T
  let c := s.admissibleSecondVertex selector i
  let jj : (Tᶜ:Set (Fin N)) := ⟨j,hj⟩
  let D := s.endpointBranchAttachmentData selector r hsep
  let C' : Set A := {v | v.val∈C}
  have hC : C⊆K := (s.sampledSecondBranch_subset selector r i).trans
    (s.sampledEndpointPatch_subset_model selector r i)
  have hcut : ∀ u∈C,∀ v∈K,v∉C → ¬H.Adj u v := by
    intro u hu v hv hvC huv
    exact D.C_cut i ⟨u,hC hu⟩ hu ⟨v,hv⟩ hvC huv
  have hradial : ∀ v∈C,H.edist c v≤(r:ℕ∞) := fun v hv =>
    s.sampledSecondBranch_post_radial selector r hsep i v hv
  have hunion : A=K∪graphBallVertices H jj r :=
    g.singleTargetOutsideVertices_eq_union T labels samples selector r j hj
  have hcut' : ∀ u∈C',∀ v∉C',¬M.graph.Adj u v := by
    intro u hu v hv huv
    have hvA : v.val∈K∪graphBallVertices H jj r := hunion ▸ v.property
    exact isolated_branch_augmented_cut H K C c jj r hcut hradial hfar u.val hu v.val hvA hv huv
  have hxc : x∈C' := by
    change x.val∈C
    rw [hx]
    exact s.admissibleSecondVertex_mem_secondBranch selector r i
  have hjC : g.singleTargetOutsideTargetVertex T labels samples selector r j hj∉C' :=
    isolated_branch_target_not_mem H C c jj r hradial hfar
  exact M.extensionGreen_zero_across_cut hd C' hcut' q z hz hq x hxc
    (g.singleTargetOutsideTargetVertex T labels samples selector r j hj) hjC

end RegularGraph
end LocalLaw
