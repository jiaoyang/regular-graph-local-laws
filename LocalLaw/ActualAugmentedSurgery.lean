import LocalLaw.SourceAugmentedIndexRows
import LocalLaw.RestrictedSurgeryRowStability
import LocalLaw.AugmentedIndexParameters
import LocalLaw.OldTwoTargetParameters

/-!
# Actual outside Green comparison with a two-target surgery model

The old strong structural event and the actual F1 occupancy are sufficient.
No finite reference class or entry cap is assumed for the switched augmented
model: its required finite rows were derived by endpoint model surgery.
-/
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 3000000
namespace LocalLaw
local instance actualAugmentedSurgeryDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def augmentedSurgeryErrorConstant (d : ℕ) (C1 : ℝ) (Bnear : ℕ) : ℝ :=
  4*(1+augmentedTwoTargetRowCap d Bnear*endpointSurgeryCouplingCap d)^2*C1

namespace RegularGraph

theorem eventually_actual_augmented_surgery (a b d Bnear : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ‖z‖≤B → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z →
      (∀ v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let R := logarithmicRadius (c/4) d N
      let selector := R/4
      let r := effectiveModelRadius a d N β
      let s := g.admissibleState T boundary samples
      let gnew := g.labelledResampledGraph T boundary samples selector
      (∀ v : (Tᶜ : Set (Fin N)),(tripleNearIndices g.graph T (R/2) samples v).card≤Bnear) →
      ∀ x y : (Tᶜ : Set (Fin N)),
      let S := s.twoTargetEndpointVertices selector r x y
      let xl := twoBallLeft (outsideGraph g.graph T) (s.endpointModelVertices selector r) x y r
      let yl := twoBallRight (outsideGraph g.graph T) (s.endpointModelVertices selector r) x y r
      ‖(gnew.deficient.delete T).G z x y-
        ((gnew.deficient.delete T).restrict S).extensionGreen (g.Q z) z xl yl‖ ≤
          augmentedSurgeryErrorConstant d C1 Bnear * g.sourcePrime a (logarithmicRadius β d N) z := by
  let C := augmentedTwoTargetRowCap d Bnear
  let w := endpointSurgeryCouplingCap d
  have hCextra := finiteExtraReferenceConstant_ge_one d hd
  have hC : 0≤C := by
    dsimp only [C,augmentedTwoTargetRowCap,augmentedOldTargetRowCap,augmentedTargetRowCap,
      endpointSurgeryModelRowCap,endpointSurgeryCouplingCap]
    positivity
  have hw : 0≤w := by dsimp only [w,endpointSurgeryCouplingCap]; positivity
  have hC1zero : 0≤C1 := (by norm_num : (0:ℝ)≤1).trans hC1
  filter_upwards [eventually_source_augmented_index_rows a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_old_twoTarget_geometry a d c β hd hc hβ hβc,
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_augmented_index_surgery_smallness a b d β C w (2*C1) ha hb hd hβ hC hw (by positivity),
    (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)]
    with N hrows hgeo hnum hsmall hdepth
  intro g o z hz hfloor hzB Cq badCount hplus hstrong ι _ boundary samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let R := logarithmicRadius (c/4) d N
  let selector := R/4
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary samples
  let old := g.deficient.delete T
  let gnew := g.labelledResampledGraph T boundary samples selector
  let new := gnew.deficient.delete T
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let L := Real.log (N:ℝ)
  intro hnear x y
  let S := s.twoTargetEndpointVertices selector r x y
  let xl : S := twoBallLeft (outsideGraph g.graph T) (s.endpointModelVertices selector r) x y r
  let yl : S := twoBallRight (outsideGraph g.graph T) (s.endpointModelVertices selector r) x y r
  let contain := s.endpointModelVertices_subset_twoTargetEndpointVertices selector r x y
  let er := g.augmentedEndpointEmbedding T boundary samples selector r S contain
  let I := twoTargetIndexSet er xl yl
  let e : I ↪ S := ⟨Subtype.val,Subtype.val_injective⟩
  have hell : ell≤doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have geo := hgeo g o ell hell hstrong boundary samples x y
  have hrow : ∀ v : I, ∑ u : I, ‖(new.restrict S).extensionGreen (g.Q z) z v.val u.val‖≤C :=
    hrows g o z hz hfloor hzB Cq badCount hplus boundary samples S contain geo.1
      (augmentedObservationDiameter d r) geo.2.1 geo.2.2 Bnear xl yl (hnear x) (hnear y)
  have hcol : ∀ v : I, ∑ u : I, ‖(new.restrict S).extensionGreen (g.Q z) z u.val v.val‖≤C := by
    intro v
    have hs := (new.restrict S).extensionGreen_isSymm (g.Q z) z
    have heq : (∑ u : I, ‖(new.restrict S).extensionGreen (g.Q z) z u.val v.val‖)=
        ∑ u : I, ‖(new.restrict S).extensionGreen (g.Q z) z v.val u.val‖ :=
      Finset.sum_congr rfl (fun u _ => congrArg norm (hs.apply u.val v.val).symm)
    rw [heq]
    exact hrow v
  have hcapture : ∀ i : I, graphBallVertices old.graph (e i).val r⊆S := by
    intro i v hv
    rcases i.property with ⟨j,hj⟩ | hi
    · have heq : (e i).val=j.val := congrArg Subtype.val hj.symm
      apply Or.inl
      exact ⟨j.val,j.property,by simpa only [heq] using hv⟩
    · rcases hi with hi | hi
      · apply Or.inr; apply Or.inl
        have heq : (e i).val=x := congrArg Subtype.val hi
        simpa only [heq] using hv
      · apply Or.inr; apply Or.inr
        have heq : (e i).val=y := congrArg Subtype.val hi
        simpa only [heq] using hv
  have hgraph : ∀ u v, u∉Set.range (fun i : I => (e i).val) ∨ v∉Set.range (fun i : I => (e i).val) →
      (old.graph.Adj u v ↔ new.graph.Adj u v) := by
    intro u v huv
    have avoid (u : (Tᶜ : Set (Fin N))) (hu : u∉Set.range (fun i : I => (e i).val)) :
        u∉s.fullResampleOutsideEndpoints selector := by
      intro h
      let j : s.endpointModelRoots selector := ⟨u,s.fullResampleOutsideEndpoints_subset_modelRoots selector h⟩
      exact hu ⟨⟨er j,Or.inl ⟨j,rfl⟩⟩,rfl⟩
    rcases huv with hu | hv
    · exact (s.fullResample_outside_adj_of_away_left selector u v (avoid u hu)).symm
    · rw [old.graph.adj_comm,new.graph.adj_comm]
      exact (s.fullResample_outside_adj_of_away_left selector v u (avoid v hv)).symm
  have hcard : Fintype.card I≤Nat.card (s.endpointModelRoots selector)+2 := by
    simpa only [I,Nat.card_eq_fintype_card] using two_target_index_card er xl yl
  have hsmall' : (Fintype.card I:ℝ)*(1+C*w)*w*(2*C1*L^3*ε)≤1/2 := by
    have hh := hsmall g o ell hell boundary samples selector z hz hfloor (Fintype.card I) hcard
    simpa only [sourcePrime,inflatedPrime,mul_assoc] using hh
  have happ : ∀ i j : I, ‖old.G z (e i).val (e j).val-old.P r z (g.Q z) (e i).val (e j).val‖≤C1*L^3*ε := by
    intro i j
    simpa only [sourcePrime,inflatedPrime,mul_assoc] using hplus.deleted (e i).val (e j).val
  have num := hnum z hz hfloor
  have hfinal := old.restricted_endpoint_surgery_stability_of_rows new hd S e r
    (augmentedObservationDiameter d r) z (g.Q z) hz (g.Q_im_nonnegative z hz)
    B C1 ε L (sourceObservationLogCap d β) hzB num
    (g.deleted_degree_deficit_saturated T) (gnew.deleted_degree_deficit_saturated T) hgraph
    geo.1 geo.2.1 geo.2.2 hcapture C hC hrow hcol hplus.cavity happ hsmall'
  let ix : I := ⟨xl,Or.inr (Or.inl rfl)⟩
  let iy : I := ⟨yl,Or.inr (Or.inr rfl)⟩
  exact (hfinal ix iy).trans_eq (by unfold augmentedSurgeryErrorConstant sourcePrime inflatedPrime; ring)

end RegularGraph
end LocalLaw
