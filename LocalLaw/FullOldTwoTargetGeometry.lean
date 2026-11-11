import LocalLaw.FullOldComponentAmbient
import LocalLaw.OldTwoTargetAugmentation

/-! # Old full two-target augmentation: class, diameter and exact capture

The source strong-radius event controls each old component individually.
The new pair is used only as a subset of this old model; no new class is assumed.
-/

noncomputable section
namespace LocalLaw
set_option maxHeartbeats 2500000
local instance fullOldTwoTargetDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) fullOldTwoTargetComponentDecidable
    {A : Type} (G : SimpleGraph A) (c : G.ConnectedComponent) : DecidablePred (fun x => x ∈ c.supp) :=
  fun _ => Classical.propDecidable _
namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type}

def fullTwoTargetVertices (s : LabelledResamplingState V T ι) (selector r : ℕ) (x y : V) : Set V :=
  twoBallAugment s.graph (filledExteriorVertices T (s.endpointModelVertices selector r)) x y r

theorem fullEndpointVertices_eq_setBall (s : LabelledResamplingState V T ι) (selector r : ℕ) :
    filledExteriorVertices T (s.endpointModelVertices selector r) = graphSetBall s.graph (s.fullEndpointRoots selector) r := by
  ext v
  constructor
  · rintro (hv | ⟨w,⟨a,ha,haw⟩,rfl⟩)
    · exact ⟨v,Or.inl hv,by simp⟩
    · refine ⟨a.val,Or.inr ⟨a,ha,rfl⟩,?_⟩
      exact (graphHom_edist_le (SimpleGraph.Embedding.induce (G := s.graph) Tᶜ).toHom a w).trans haw
  · rintro ⟨a,ha,hav⟩
    exact s.fullEndpoint_old_root_ball_capture selector r ⟨a,ha⟩ hav

theorem fullTwoTarget_eq_setBall (s : LabelledResamplingState V T ι) (selector r : ℕ) (x y : V) :
    s.fullTwoTargetVertices selector r x y = graphSetBall s.graph (s.fullEndpointRoots selector ∪ {x,y}) r := by
  rw [fullTwoTargetVertices,s.fullEndpointVertices_eq_setBall]
  ext v
  constructor
  · rintro (⟨a,ha,hav⟩ | hx | hy)
    · exact ⟨a,Or.inl ha,hav⟩
    · exact ⟨x,Or.inr (Or.inl rfl),hx⟩
    · exact ⟨y,Or.inr (Or.inr rfl),hy⟩
  · rintro ⟨a,ha,hav⟩
    rcases ha with ha | ha | ha
    · exact Or.inl ⟨a,ha,hav⟩
    · exact Or.inr (Or.inl (ha ▸ hav))
    · exact Or.inr (Or.inr (ha ▸ hav))

variable [Fintype ι]
theorem fullTwoTarget_new_setBall (s : LabelledResamplingState V T ι) (selector r : ℕ) (x y : V) :
    s.fullTwoTargetVertices selector r x y =
      graphSetBall (s.fullResample selector).graph (s.fullEndpointRoots selector ∪ {x,y}) r := by
  rw [s.fullTwoTarget_eq_setBall selector r x y]
  apply graphSetBall_eq_of_internal_changes
  intro u v huv
  exact s.fullResample_adj_agrees_off_endpoints selector u v
    (huv.imp (fun hu hm => hu (Or.inl (s.fullResampleEndpoints_subset_fullEndpointRoots selector hm)))
      (fun hv hm => hv (Or.inl (s.fullResampleEndpoints_subset_fullEndpointRoots selector hm))))

theorem switched_full_pair_subset_old_augmentation (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (x y : V) :
    pairBallVertices (s.fullResample selector).graph x y r ⊆ s.fullTwoTargetVertices selector r x y := by
  rw [s.fullTwoTarget_new_setBall selector r x y]
  intro v hv
  rcases hv with hx | hy
  · exact ⟨x,Or.inr (Or.inl rfl),hx⟩
  · exact ⟨y,Or.inr (Or.inr rfl),hy⟩

end LabelledResamplingState
namespace RegularGraph
variable {N d : ℕ} {ι : Type}

theorem old_fullTwoTarget_component_budget (g : RegularGraph N d) (o : Fin N)
    (ell selector r R : ℕ) (hmargin : 7*r+4*ell+7 ≤ R) (hsep : 2*r+2 ≤ selector)
    (hballs : ∀ v,graphBallExcess g.graph v R≤finiteOmega d)
    (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) (x y : Fin N) :
    let T := graphBallVertices g.graph o ell
    let s := g.admissibleState T labels samples
    (g.deficient.restrict (s.fullTwoTargetVertices selector r x y)).ComponentReferenceBudget := by
  dsimp only
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T labels samples
  let K := filledExteriorVertices T (s.endpointModelVertices selector r)
  let S := s.fullTwoTargetVertices selector r x y
  let f : (g.graph.induce S) →g g.graph := SimpleGraph.Embedding.induce (G := g.graph) S |>.toHom
  have hK : ∀ c : (g.graph.induce K).ConnectedComponent,∀ u v : S,
      u.val∈liftedComponent g.graph K c → v.val∈liftedComponent g.graph K c →
      g.graph.edist (f u) (f v)≤((2*r+2*ell+2:ℕ):ℕ∞) := by
    intro c u v hu hv
    exact g.fullEndpoint_old_component_ambient_diameter o ell selector r hsep labels samples c u.val v.val hu hv
  intro c
  obtain ⟨a,ha,hnear⟩ := twoHub_component_enclosure g.graph K (graphBallVertices g.graph x r)
    (graphBallVertices g.graph y r) g.graph f (twoBallLeft g.graph K x y r) (twoBallRight g.graph K x y r)
    (center_mem_graphBall g.graph x r) (center_mem_graphBall g.graph y r) (2*r+2*ell+2) r hK
    (twoBall_left_radial g.graph K x y r g.graph f) (twoBall_right_radial g.graph K x y r g.graph f) c
  let e : ((g.deficient.restrict S).graph.induce c.supp) →g graphBall g.graph a.val R :=
    { toFun := fun v => ⟨v.val.val,(hnear v.val v.property).trans
        (ENat.coe_le_coe.mpr (by omega : 3*r+2*(2*r+2*ell+2)+3≤R))⟩
      map_rel' := fun h => h }
  have he : Function.Injective e := by
    intro u v h
    exact Subtype.ext (Subtype.ext (congrArg (fun v : graphBallVertices g.graph a.val R => v.val) h))
  have hh := connected_embedding_graphExcess_le _ _ c.connected_induce_supp
    (graphBall_connected g.graph a.val R) e he
  have hz : (∑ v,((g.deficient.restrict S).restrict c.supp).deficit v)=0 := by
    apply Finset.sum_eq_zero
    intro v _
    rfl
  rw [hz,Nat.zero_add]
  exact hh.trans (hballs a.val)

theorem old_fullTwoTarget_distance_bound (g : RegularGraph N d) (o : Fin N)
    (ell selector r R : ℕ) (hmargin : ell+r+1≤R) (hsep : 2*r+2≤selector)
    (hball : graphBallExcess g.graph o R≤finiteOmega d)
    (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) (x y : Fin N) :
    let T := graphBallVertices g.graph o ell
    let s := g.admissibleState T labels samples
    ∀ u v : s.fullTwoTargetVertices selector r x y,
      (g.graph.induce (s.fullTwoTargetVertices selector r x y)).dist u v≤
        3*filledEndpointDiameter d ell r+4*r+4 := by
  dsimp only
  apply twoBallAugment_distance_bound
  exact g.old_filledEndpoint_distance_bound o ell selector r R hsep hmargin hball labels samples

end RegularGraph
end LocalLaw
