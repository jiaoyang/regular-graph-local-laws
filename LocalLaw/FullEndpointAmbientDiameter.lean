import LocalLaw.FullEndpointBranches
import LocalLaw.OldEndpointAmbientDiameter
import LocalLaw.EndpointRootInvariance

/-! # Ambient diameter of full-filled components, independent of excess

Before switching the filled central cell is an ordinary expanded root ball;
every sampled pair cell is isolated. Applying the same fact to the actual
inverse state gives a uniform ambient cap for the switched components.
-/

noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance fullEndpointAmbientDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type} [Fintype ι]

def fullSampledPatch (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (i : s.AdmissibleSampleIndex selector) : Set V := Subtype.val '' s.sampledEndpointPatch selector r i

omit [Fintype ι] in
theorem fullEndpoint_old_core_closed (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2*r+2≤selector) :
    ∀ u∈filledExteriorVertices T (s.endpointModelVertices selector r),
      u∈filledExteriorVertices T (s.centralEndpointPatch r) →
      ∀ v∈filledExteriorVertices T (s.endpointModelVertices selector r),
        v∉filledExteriorVertices T (s.centralEndpointPatch r) → ¬s.graph.Adj u v := by
  intro u hu huC v hv hvC huv
  have hvT : v∉T := fun h => hvC (Or.inl h)
  let vv : (Tᶜ : Set V) := ⟨v,hvT⟩
  have hvK := (filledExterior_outside_mem T (s.endpointModelVertices selector r) vv).mp hv
  have hvnC : vv∉s.centralEndpointPatch r := fun h => hvC (Or.inr ⟨vv,h,rfl⟩)
  by_cases huT : u∈T
  · let α : BoundaryOrientedEdge s.graph T := ⟨(u,v),huv,huT,hvT⟩
    exact hvnC ⟨vv,⟨α,rfl⟩,center_mem_graphBall _ _ r⟩
  · let uu : (Tᶜ : Set V) := ⟨u,huT⟩
    have huK := (filledExterior_outside_mem T (s.endpointModelVertices selector r) uu).mp hu
    have huC' := (filledExterior_outside_mem T (s.centralEndpointPatch r) uu).mp huC
    exact s.endpointModel_central_closed selector r hsep uu huK huC' vv hvK hvnC huv

omit [Fintype ι] in
theorem fullEndpoint_old_sampled_closed (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2*r+2≤selector) (i : s.AdmissibleSampleIndex selector) :
    ∀ u∈filledExteriorVertices T (s.endpointModelVertices selector r),u∈s.fullSampledPatch selector r i →
      ∀ v∈filledExteriorVertices T (s.endpointModelVertices selector r),
        v∉s.fullSampledPatch selector r i → ¬s.graph.Adj u v := by
  intro u hu huI v hv hvI huv
  obtain ⟨uu,huu,rfl⟩ := huI
  have huK := (filledExterior_outside_mem T (s.endpointModelVertices selector r) uu).mp hu
  by_cases hvT : v∈T
  · let α : BoundaryOrientedEdge s.graph T := ⟨(v,uu.val),huv.symm,hvT,uu.property⟩
    have hc : uu∈s.centralEndpointPatch r := ⟨uu,⟨α,rfl⟩,center_mem_graphBall _ _ r⟩
    exact Set.disjoint_left.mp (s.central_sampledEndpointPatch_disjoint_no_edge selector r hsep i).1 hc huu
  · let vv : (Tᶜ : Set V) := ⟨v,hvT⟩
    have hvK := (filledExterior_outside_mem T (s.endpointModelVertices selector r) vv).mp hv
    have hvnI : vv∉s.sampledEndpointPatch selector r i := fun h => hvI ⟨vv,h,rfl⟩
    exact s.endpointModel_sampled_closed selector r hsep i uu huK huu vv hvK hvnI huv

omit [Fintype ι] in
theorem fullEndpoint_old_component_ambient (s : LabelledResamplingState V T ι)
    (o : V) (ell selector r : ℕ) (hT : T=graphBallVertices s.graph o ell)
    (hsep : 2*r+2≤selector)
    (C : (s.graph.induce (filledExteriorVertices T (s.endpointModelVertices selector r))).ConnectedComponent)
    (u v : C.supp) : s.graph.edist u.val.val v.val.val≤((2*r+2*ell+2:ℕ):ℕ∞) := by
  let H := s.graph
  let K := filledExteriorVertices T (s.endpointModelVertices selector r)
  let L := filledExteriorVertices T (s.centralEndpointPatch r)
  have hL : L=graphBallVertices H o (ell+r+1) := by
    change filledExteriorVertices T (centralBoundaryVertices H T r)=_
    rw [hT]
    exact filled_centralBoundary_eq_ball H o ell r
  by_cases huL : u.val.val∈L
  · have hsub := induced_component_subset_of_closed H K L (s.fullEndpoint_old_core_closed selector r hsep) C u huL
    have huB : H.edist o u.val.val≤((ell+r+1:ℕ):ℕ∞) := by
      change u.val.val∈graphBallVertices H o (ell+r+1)
      rw [←hL]
      exact huL
    have hvB : H.edist o v.val.val≤((ell+r+1:ℕ):ℕ∞) := by
      change v.val.val∈graphBallVertices H o (ell+r+1)
      rw [←hL]
      exact hsub v
    exact ((SimpleGraph.edist_triangle (G:=H) (u:=u.val.val) (v:=o) (w:=v.val.val)).trans
      (add_le_add (by simpa only [SimpleGraph.edist_comm] using huB) hvB)).trans_eq (by push_cast; ring)
  · have huT : u.val.val∉T := fun h => huL (Or.inl h)
    let uu : (Tᶜ : Set V) := ⟨u.val.val,huT⟩
    have huK := (filledExterior_outside_mem T (s.endpointModelVertices selector r) uu).mp u.val.property
    rcases s.endpointModelVertices_cell_cover selector r uu huK with huC | ⟨i,huI⟩
    · exact False.elim (huL (Or.inr ⟨uu,huC,rfl⟩))
    · have hsub := induced_component_subset_of_closed H K (s.fullSampledPatch selector r i)
        (s.fullEndpoint_old_sampled_closed selector r hsep i) C u ⟨uu,huI,rfl⟩
      obtain ⟨vv,hvI,hvv⟩ := hsub v
      rw [s.sampledEndpointPatch_eq_pairBall selector r i] at huI hvI
      have hh := pair_roots_ambient_edist_bound (outsideGraph H T) (s.admissibleSampleVertex selector i)
        (s.admissibleSecondVertex selector i) (s.samples (s.boundary i.val)).property.1 r uu vv huI hvI
      have hamb := (graphHom_edist_le (SimpleGraph.Embedding.induce (G:=H) Tᶜ).toHom uu vv).trans hh
      change H.edist u.val.val vv.val≤((2*r+1:ℕ):ℕ∞) at hamb
      rw [hvv] at hamb
      exact hamb.trans (ENat.coe_le_coe.mpr (by omega : 2*r+1≤2*r+2*ell+2))


theorem fullEndpoint_new_component_ambient (s : LabelledResamplingState V T ι)
    (o : V) (ell selector r : ℕ) (hT : T=graphBallVertices s.graph o ell)
    (hsep : 2*r+2≤selector)
    (C : ((s.fullResample selector).graph.induce (filledExteriorVertices T (s.endpointModelVertices selector r))).ConnectedComponent)
    (u v : C.supp) : (s.fullResample selector).graph.edist u.val.val v.val.val≤((2*r+2*ell+2:ℕ):ℕ∞) := by
  have hTnew : T=graphBallVertices (s.fullResample selector).graph o ell := by
    symm
    simpa only [graphSetBall_singleton] using s.fullResample_ball selector {o} ell
      (by simpa only [graphSetBall_singleton] using hT)
  have hh := (s.fullResample selector).fullEndpoint_old_component_ambient o ell selector r hTnew hsep
  rw [s.endpointModelVertices_resample] at hh
  exact hh C u v

end LabelledResamplingState
end LocalLaw
