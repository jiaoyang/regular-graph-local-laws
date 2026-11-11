import LocalLaw.FullOldTwoTargetGeometry
import LocalLaw.AugmentedPairCapture
import LocalLaw.EffectiveAugmentedMargins
import LocalLaw.HereditaryReferenceBounds

/-! # All source numerical budgets for the old full augmentation -/

noncomputable section
namespace LocalLaw
local instance sourceFullTwoTargetDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def fullTwoTargetDiameter (d ell r : ℕ) : ℕ := 3*filledEndpointDiameter d ell r+4*r+4

def fullTwoTargetLogCap (d : ℕ) (β : ℝ) : ℝ := 8*filledEndpointLogCap d β

def fullTwoTargetHereditaryLogCap (d : ℕ) (β : ℝ) : ℝ :=
  ((2*(finiteOmega d+2)+1:ℕ):ℝ)*fullTwoTargetLogCap d β

theorem hereditaryReferenceRadius_log_bound (d D : ℕ) (A L : ℝ)
    (hD : (D:ℝ)+1 ≤ A*L) :
    (hereditaryReferenceRadius d D:ℝ)+1 ≤ ((2*(finiteOmega d+2)+1:ℕ):ℝ)*A*L := by
  have hn : hereditaryReferenceRadius d D+1≤(2*(finiteOmega d+2)+1)*(D+1) := by
    unfold hereditaryReferenceRadius
    nlinarith
  have hh : (hereditaryReferenceRadius d D:ℝ)+1≤((2*(finiteOmega d+2)+1:ℕ):ℝ)*((D:ℝ)+1) := by
    exact_mod_cast hn
  exact hh.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg (2*(finiteOmega d+2)+1)))

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem subset_restriction_intrinsic_diameter (g : DeficientGraph V d) (M K : Set V) (hKM : K ⊆ M)
    (hb : (g.restrict M).ComponentFiniteReferenceBudget) (R : ℕ)
    (hR : ∀ u v,(g.restrict M).graph.dist u v ≤ R) (x y : K) :
    (g.restrict K).graph.dist x y ≤ hereditaryReferenceRadius d R := by
  let U : Set M := {v | v.val ∈ K}
  let e := inducePreimageIso g.graph M K hKM
  have hh := (g.restrict M).finite_class_restriction_intrinsic_diameter hb R hR U (e.symm x) (e.symm y)
  have he := graphIso_dist e (e.symm x) (e.symm y)
  rw [e.apply_symm_apply,e.apply_symm_apply] at he
  change (g.graph.induce K).dist x y ≤ hereditaryReferenceRadius d R
  rw [he]
  exact hh

end DeficientGraph
namespace RegularGraph

theorem eventually_source_fullTwoTarget_geometry (a b d : ℕ) (c β B : ℝ)
    (ha : 12 ≤ a) (hb : 25*a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c/32) :
    ∀ᶠ N : ℕ in Filter.atTop,∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → Real.log (N:ℝ)^b/(N:ℝ) ≤ z.im →
      (∀ v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y : Fin N),
      let ell := actualCavityDepth a d N z-1
      let T := graphBallVertices g.graph o ell
      let r := effectiveModelRadius a d N β
      let selector := logarithmicRadius (c/4) d N/4
      let s := g.admissibleState T labels samples
      let S := s.fullTwoTargetVertices selector r x y
      let K := pairBallVertices (s.fullResample selector).graph x y r
      SourceFullEndpointGeometry (g.deficient.restrict S) (fullTwoTargetDiameter d ell r)
        (fullTwoTargetLogCap d β) (Real.log (N:ℝ)) ∧
      K ⊆ S ∧ (g.deficient.restrict K).ComponentFiniteReferenceBudget ∧
      (∀ u v,(g.deficient.restrict K).graph.dist u v≤hereditaryReferenceRadius d (fullTwoTargetDiameter d ell r)) ∧
      (∀ u∈s.fullEndpointRoots selector∪{x,y},graphBallVertices g.graph u r⊆S) := by
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_effective_augmented_radius_margin a d c β hd hc hβ hβc,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    eventually_filledEndpoint_diameter_log a b d c β B 1 ha hb hd hc hβ hβc le_rfl,
    hdepth] with N hmargin hcommon hlog hdepth
  intro g o z hz hfloor hballs ι _ labels samples x y
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let T := graphBallVertices g.graph o ell
  let r := effectiveModelRadius a d N β
  let R := logarithmicRadius (c/4) d N
  let selector := R/4
  let s := g.admissibleState T labels samples
  let S := s.fullTwoTargetVertices selector r x y
  let K := pairBallVertices (s.fullResample selector).graph x y r
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hm : 7*r+6*ell+8≤R := hmargin ell hell
  have hs : 2*r+2≤selector := by
    have hh := Nat.mul_le_mul_left 2 hcommon
    dsimp only [selector,R,r]
    omega
  have hbase := g.old_fullTwoTarget_component_budget o ell selector r R (by omega) hs hballs labels samples x y
  have hdiam := g.old_fullTwoTarget_distance_bound o ell selector r R (by omega) hs (hballs o) labels samples x y
  have hlogBase := hlog z hz hfloor
  have hrD : r ≤ filledEndpointDiameter d ell r := by
    have hm := Nat.mul_le_mul_right (2*r+1) (show 1 ≤ 2*(finiteOmega d+1) by omega)
    simp only [one_mul] at hm
    unfold filledEndpointDiameter
    omega
  have hlogAug : (fullTwoTargetDiameter d ell r:ℝ)+1≤fullTwoTargetLogCap d β*Real.log (N:ℝ) := by
    have hnat : fullTwoTargetDiameter d ell r+1≤8*(filledEndpointDiameter d ell r+1) := by
      unfold fullTwoTargetDiameter
      omega
    have hcast : (fullTwoTargetDiameter d ell r:ℝ)+1≤8*((filledEndpointDiameter d ell r:ℝ)+1) := by
      exact_mod_cast hnat
    dsimp only [fullTwoTargetLogCap]
    nlinarith only [hcast,hlogBase]
  have hsub : K⊆S := s.switched_full_pair_subset_old_augmentation selector r x y
  have hfinite : (g.deficient.restrict S).ComponentFiniteReferenceBudget := hbase.to_componentFinite
  refine ⟨⟨hbase,hdiam,hlogAug⟩,hsub,
    g.deficient.subset_restriction_component_budget S K hsub hfinite,
    g.deficient.subset_restriction_intrinsic_diameter S K hsub hfinite _ hdiam,?_⟩
  intro u hu v hv
  rw [s.fullTwoTarget_eq_setBall selector r x y]
  exact ⟨u,hu,hv⟩

end RegularGraph
end LocalLaw
