import LocalLaw.FullEndpointAmbientDiameter
import LocalLaw.SourceFilledEndpointBudget
import LocalLaw.TwoHubEnclosure
import LocalLaw.TwoBallAugmentation
import LocalLaw.EffectiveAugmentedMargins
import LocalLaw.FilledEndpointLocality

/-! # A single outside target added to the full filled switched model

Each augmented component is enclosed in a genuine strong-radius ball of
the target graph. The endpoint inverse-state partition supplies a sharp
ambient enclosure, while the logarithmic intrinsic cap may be coarser.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance singleTargetFilledDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) singleTargetFilledComponentDecidable {V : Type*}
    (G : SimpleGraph V) (C : G.ConnectedComponent) : DecidablePred (fun x => x∈C.supp) :=
  fun _ => Classical.propDecidable _

namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

def singleTargetFilledVertices (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (y : Fin N) : Set (Fin N) :=
  twoBallAugment (g.labelledResampledGraph T labels samples selector).graph
    (filledExteriorVertices T ((g.admissibleState T labels samples).endpointModelVertices selector r)) y y r


def singleTargetFilledInnerVertex (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (y : Fin N) (x : T) : g.singleTargetFilledVertices T labels samples selector r y :=
  ⟨x.val,Or.inl (Or.inl x.property)⟩

def singleTargetFilledTargetVertex (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (y : Fin N) : g.singleTargetFilledVertices T labels samples selector r y :=
  ⟨y,Or.inr (Or.inl (center_mem_graphBall _ y r))⟩

theorem singleTargetFilled_pair_P (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (y : Fin N) (x : T) (q z : ℂ) :
    let gnew := g.labelledResampledGraph T labels samples selector
    (gnew.deficient.restrict (g.singleTargetFilledVertices T labels samples selector r y)).P r z q
      (g.singleTargetFilledInnerVertex T labels samples selector r y x)
      (g.singleTargetFilledTargetVertex T labels samples selector r y)=gnew.P r z q x.val y := by
  dsimp only
  let s := g.admissibleState T labels samples
  let gnew := g.labelledResampledGraph T labels samples selector
  let S := g.singleTargetFilledVertices T labels samples selector r y
  have hx : graphBallVertices gnew.graph x.val r⊆S := fun v hv =>
    Or.inl (s.filledEndpoint_captures_inner_ball selector r x
      (graphBallVertices_mono gnew.graph x.val (Nat.le_succ r) hv))
  have hy : graphBallVertices gnew.graph y r⊆S := fun _ hv => Or.inr (Or.inl hv)
  exact (gnew.deficient.restrict_pair_P S
    (g.singleTargetFilledInnerVertex T labels samples selector r y x)
    (g.singleTargetFilledTargetVertex T labels samples selector r y) r hx hy q z).trans
      (gnew.deficient_P r z q x.val y)

theorem singleTargetFilled_component_reference_budget (g : RegularGraph N d)
    (o : Fin N) (ell selector r R : ℕ)
    (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (hsep : 2*r+2≤selector) (hmargin : 7*r+4*ell+7≤R)
    (hballs : ∀ v,graphBallExcess (g.labelledResampledGraph (graphBallVertices g.graph o ell) labels samples selector).graph v R≤finiteOmega d)
    (y : Fin N) :
    let T := graphBallVertices g.graph o ell
    let gnew := g.labelledResampledGraph T labels samples selector
    (gnew.deficient.restrict (g.singleTargetFilledVertices T labels samples selector r y)).ComponentReferenceBudget := by
  dsimp only
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T labels samples
  let gnew := g.labelledResampledGraph T labels samples selector
  let K := filledExteriorVertices T (s.endpointModelVertices selector r)
  let H := gnew.graph
  let S := g.singleTargetFilledVertices T labels samples selector r y
  let l := twoBallLeft H K y y r
  let f : H.induce S →g H := ⟨Subtype.val,fun h => h⟩
  have hK : ∀ C:(H.induce K).ConnectedComponent,∀ u v:S,
      u.val∈liftedComponent H K C → v.val∈liftedComponent H K C →
      H.edist (f u) (f v)≤((2*r+2*ell+2:ℕ):ℕ∞) := by
    intro C u v hu hv
    exact s.fullEndpoint_new_component_ambient o ell selector r rfl hsep C
      ⟨⟨u.val,hu.1⟩,hu.2⟩ ⟨⟨v.val,hv.1⟩,hv.2⟩
  intro C
  obtain ⟨a,ha,hnear⟩ := twoHub_component_enclosure H K (graphBallVertices H y r) (graphBallVertices H y r)
    H f l l (center_mem_graphBall H y r) (center_mem_graphBall H y r) (2*r+2*ell+2) r hK
    (twoBall_left_radial H K y y r H f) (twoBall_right_radial H K y y r H f) C
  let emb : (H.induce S).induce C.supp →g graphBall H a.val R :=
    { toFun := fun v => ⟨v.val.val,(hnear v.val v.property).trans
          (ENat.coe_le_coe.mpr (by omega : 3*r+2*(2*r+2*ell+2)+3≤R))⟩
      map_rel' := fun h => h }
  have hinj : Function.Injective emb := by
    intro u v h
    exact Subtype.ext (Subtype.ext (congrArg (fun w : graphBallVertices H a.val R => w.val) h))
  have hbound := (connected_embedding_graphExcess_le ((H.induce S).induce C.supp) (graphBall H a.val R)
    C.connected_induce_supp (graphBall_connected H a.val R) emb hinj).trans (hballs a.val)
  have hzero : (∑ v, ((gnew.deficient.restrict S).restrict C.supp).deficit v)=0 := by
    apply Finset.sum_eq_zero
    intro v _
    rfl
  rw [hzero,Nat.zero_add]
  exact hbound

end RegularGraph

 def singleTargetFilledDiameter (d ell r : ℕ) : ℕ := 3*filledEndpointDiameter d ell r+4*r+4
 def singleTargetFilledLogCap (d : ℕ) (β : ℝ) : ℝ := 3*filledEndpointLogCap d β+sourceObservationLogCap d β

namespace RegularGraph

theorem eventually_singleTargetFilled_geometry (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop,∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell := actualCavityDepth a d N z-1
      let R := logarithmicRadius (c/4) d N
      let T := graphBallVertices g.graph o ell
      let r := effectiveModelRadius a d N β
      let gnew := g.labelledResampledGraph T labels samples (R/4)
      gnew.SourceOmegaWithRadii a r (logarithmicRadius β d N) R (finiteOmega d) badCount z →
      ∀ y : Fin N, SourceFullEndpointGeometry
        (gnew.deficient.restrict (g.singleTargetFilledVertices T labels samples (R/4) r y))
        (singleTargetFilledDiameter d ell r) (singleTargetFilledLogCap d β) (Real.log (N:ℝ)) := by
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_source_fullEndpoint_geometry a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effective_augmented_radius_margin a d c β hd hc hβ hβc,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,hdepth]
    with N hfull hnum hmargin hradii hdepth
  intro g o z hz hfloor Cq badCount hplus ι _ labels samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let R := logarithmicRadius (c/4) d N
  let T := graphBallVertices g.graph o ell
  let r := effectiveModelRadius a d N β
  let gnew := g.labelledResampledGraph T labels samples (R/4)
  let K := filledExteriorVertices T ((g.admissibleState T labels samples).endpointModelVertices (R/4) r)
  intro htarget y
  have geom := hfull g o z hz hfloor Cq badCount hplus labels samples
  have num := hnum z hz hfloor
  have hell : ell≤doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hm : 7*r+4*ell+7≤R := (by have hh := hmargin ell hell; dsimp only [r,R]; omega)
  have hs : 2*r+2≤R/4 := by have hh := hradii.2.2.2 z; change r+ell+1≤R/8 at hh; omega
  refine ⟨g.singleTargetFilled_component_reference_budget o ell (R/4) r R labels samples hs hm htarget.1.1 y,?_,?_⟩
  · exact twoBallAugment_distance_bound gnew.graph K y y r (filledEndpointDiameter d ell r) geom.diameter
  · change ((3*filledEndpointDiameter d ell r+4*r+4:ℕ):ℝ)+1≤(3*filledEndpointLogCap d β+sourceObservationLogCap d β)*Real.log (N:ℝ)
    have h1 := geom.diameter_log
    have h2 := num.pair_log
    push_cast at h1 h2 ⊢
    nlinarith only [h1,h2]

end RegularGraph
end LocalLaw
