import LocalLaw.SourceAugmentedTargetRows
import LocalLaw.TwoTargetInverseRows

/-!
# Actual switched augmented rows on endpoints and two targets

Only the OLD augmented reference class is used. Actual inverse identities,
F1 occupancy and the already proved switched endpoint model control all
rows of the enlarged finite surgery index.
-/
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2800000
namespace LocalLaw
local instance sourceAugmentedIndexRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def augmentedOldTargetRowCap (d Bnear : ℕ) : ℝ :=
  2*finiteExtraReferenceConstant d*(3*(Bnear:ℝ)+1)

def augmentedTwoTargetRowCap (d Bnear : ℕ) : ℝ :=
  endpointSurgeryModelRowCap d (2*(finiteOmega d+1))+1 + 3*augmentedTargetRowCap d Bnear +
    2*(2*finiteExtraReferenceConstant d + augmentedOldTargetRowCap d Bnear *
      endpointSurgeryCouplingCap d * augmentedTargetRowCap d Bnear)

namespace RegularGraph

theorem eventually_source_augmented_index_rows (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25*a ≤ b) (hd : 3 ≤ d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ‖z‖≤B → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let R := logarithmicRadius (c/4) d N
      let selector := R/4
      let r := effectiveModelRadius a d N β
      let s := g.admissibleState T boundary samples
      let gnew := g.labelledResampledGraph T boundary samples selector
      ∀ (Saug : Set (Tᶜ : Set (Fin N))) (hcontain : s.endpointModelVertices selector r ⊆ Saug),
      ((g.deficient.delete T).restrict Saug).ComponentFiniteReferenceBudget →
      ∀ Raug : ℕ, (∀ u v, ((g.deficient.delete T).restrict Saug).graph.dist u v≤Raug) →
      (Raug:ℝ)+1≤sourceObservationLogCap d β*Real.log (N:ℝ) →
      ∀ (Bnear : ℕ) (x y : Saug),
      (tripleNearIndices g.graph T (R/2) samples x.val).card≤Bnear →
      (tripleNearIndices g.graph T (R/2) samples y.val).card≤Bnear →
      let e := g.augmentedEndpointEmbedding T boundary samples selector r Saug hcontain
      let M := (gnew.deficient.delete T).restrict Saug
      ∀ v : twoTargetIndexSet e x y,
        ∑ u : twoTargetIndexSet e x y, ‖M.extensionGreen (g.Q z) z v.val u.val‖ ≤
          augmentedTwoTargetRowCap d Bnear := by
  let C := endpointSurgeryModelRowCap d (2*(finiteOmega d+1))+1
  let w := endpointSurgeryCouplingCap d
  have hCextra := finiteExtraReferenceConstant_ge_one d hd
  have hC : 0≤C := by dsimp only [C,endpointSurgeryModelRowCap]; positivity
  have hw : 0≤w := by dsimp only [w,endpointSurgeryCouplingCap]; positivity
  filter_upwards [eventually_source_augmented_target_rows a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_augmented_endpoint_rows a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_endpoint_far_tail_small a d 1 ha hd (by norm_num),
    eventually_source_radius_hierarchy a d c β hd hc hβ hβc,
    (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)]
    with N htarget hrows hnum htail hradii hdepth
  intro g o z hz hscale hzB Cq badCount hplus ι _ boundary samples
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
  intro Saug hcontain hbudget Raug hdiam hRlog Bnear x y hx hy
  let e := g.augmentedEndpointEmbedding T boundary samples selector r Saug hcontain
  let A := (old.restrict Saug).extensionMatrix (g.Q z) z
  let Bmat := (new.restrict Saug).extensionMatrix (g.Q z) z
  let aa := augmentedOldTargetRowCap d Bnear
  let bb := augmentedTargetRowCap d Bnear
  have haa : 0≤aa := by dsimp only [aa,augmentedOldTargetRowCap]; positivity
  have hbb : 0≤bb := by dsimp only [bb,augmentedTargetRowCap,endpointSurgeryModelRowCap]; positivity
  have num := hnum z hz hscale
  have hε : 0≤ε := num.error_nonnegative
  have hprior := hplus.cavity.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) hε hC1)
  have hfeedback := (DeficientGraph.weak_localization_feedback_budgets d hd z (g.Q z) hz B
    (C1^2*ε) L (sourceObservationLogCap d β) (mul_nonneg (sq_nonneg C1) hε) num.log_one
      num.log_cap_nonnegative num.error_scaled hprior Raug (4*r+1) hRlog num.pair_log num.localization_large).1
  have hell : ell≤doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have htailSmall : (Nat.card (s.endpointModelRoots selector):ℝ)*physicalTransfer d z^(R/2)≤ε/L^16 := by
    have hh := htail g o ell hell boundary samples selector (logarithmicRadius β d N) (R/2)
      (by dsimp only [R]; have hh:=hradii.1; omega) z hz.le
    simpa only [one_mul] using hh
  have hεone : ε≤1 := by
    have hC1sq : 1≤C1^2 := by nlinarith
    have hh : ε≤(C1^2*ε)*L^4 :=
      (le_mul_of_one_le_left hε hC1sq).trans (le_mul_of_one_le_right
        (mul_nonneg (sq_nonneg C1) hε) (one_le_pow₀ num.log_one))
    exact hh.trans num.error_scaled
  have htailOne : (Nat.card (s.endpointModelRoots selector):ℝ)*physicalTransfer d z^(R/2)≤1 :=
    htailSmall.trans ((div_le_self hε (one_le_pow₀ num.log_one)).trans hεone)
  have hnear (v : Saug) (hv : v=x ∨ v=y) :
      (tripleNearIndices g.graph T (R/2) samples v.val).card≤Bnear := by
    rcases hv with hv | hv <;> rw [hv]
    · exact hx
    · exact hy
  have hOldTarget (v : Saug) (hv : v=x ∨ v=y) : ∑ i, ‖A⁻¹ v (e i)‖≤aa := by
    have hh := g.augmented_old_endpoint_rows hd T boundary samples selector r Saug hcontain hbudget Raug hdiam
      (g.Q z) z hz (g.Q_im_nonnegative z hz) hfeedback (R/2) Bnear v (hnear v hv)
    exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add_left htailOne _) (by positivity))
  have htone : physicalTransfer d z≤1 := by nlinarith [physicalTransfer_sq_le_half d hd z,physicalTransfer_pos d hd z]
  have hOldEntry (u : Saug) (_hu : u=x ∨ u=y) (v : Saug) (_hv : v=x ∨ v=y) : ‖A⁻¹ u v‖≤2*finiteExtraReferenceConstant d := by
    have hh := (old.restrict Saug).componentwise_finite_kernel_decay hd hbudget (g.Q z) z hz
      (g.Q_im_nonnegative z hz) Raug hdiam hfeedback u v
    apply hh.trans
    calc
      _ ≤ 2*finiteExtraReferenceConstant d*1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ (physicalTransfer_pos d hd z).le htone) (by positivity)
      _ = _ := mul_one _
  have hNewEndpoint : ∀ i, ∑ j, ‖Bmat⁻¹ (e i) (e j)‖≤C :=
    (hrows g o z hz hscale hzB Cq badCount hplus boundary samples Saug hcontain hbudget Raug hdiam hRlog).1
  have hNewTarget (v : Saug) (hv : v=x ∨ v=y) : ∑ i, ‖Bmat⁻¹ v (e i)‖≤bb :=
    htarget g o z hz hscale hzB Cq badCount hplus boundary samples Saug hcontain hbudget Raug hdiam hRlog
      Bnear v (hnear v hv)
  have hcross : ∀ v : Saug, ∀ t : (Saugᶜ : Set (Tᶜ : Set (Fin N))),
      old.graph.Adj v.val t.val ↔ new.graph.Adj v.val t.val := by
    intro v t
    have ht : t.val ∉ s.fullResampleOutsideEndpoints selector := by
      intro h
      have hr := s.fullResampleOutsideEndpoints_subset_modelRoots selector h
      exact t.property (hcontain (s.endpointModelKernelEmbedding selector r ⟨t.val,hr⟩).property)
    rw [old.graph.adj_comm,new.graph.adj_comm]
    exact (s.fullResample_outside_adj_of_away_left selector t.val v.val ht).symm
  have hmatrix := old.restrict_extensionMatrix_difference new Saug
    (g.deleted_degree_deficit_saturated T) (gnew.deleted_degree_deficit_saturated T) hcross (g.Q z) z
  have hsupp : ∀ u v, u∉Set.range e ∨ v∉Set.range e → (Bmat-A) u v=0 := by
    intro u v huv
    rw [hmatrix]
    apply s.fullResample_outside_difference_supported selector d u.val v.val
    exact huv.imp
      (fun hu hr => hu ⟨⟨u.val,s.fullResampleOutsideEndpoints_subset_modelRoots selector hr⟩,Subtype.ext rfl⟩)
      (fun hv hr => hv ⟨⟨v.val,s.fullResampleOutsideEndpoints_subset_modelRoots selector hr⟩,Subtype.ext rfl⟩)
  have hW : ∀ i, ∑ j, ‖(Bmat-A) (e i) (e j)‖≤w := by
    intro i
    have heq : (Bmat-A).submatrix e e=g.sourceEndpointW T boundary samples selector := by rw [hmatrix]; rfl
    change (∑ j, ‖((Bmat-A).submatrix e e) i j‖)≤w
    rw [heq]
    exact (g.source_endpoint_coupling_mass T boundary samples selector).1 i
  exact inverse_supported_two_target_rows A Bmat
    ((old.restrict Saug).extensionMatrix_isUnit hd (g.Q z) z hz (g.Q_im_nonnegative z hz))
    ((new.restrict Saug).extensionMatrix_isUnit hd (g.Q z) z hz (g.Q_im_nonnegative z hz)) e hsupp x y
    (2*finiteExtraReferenceConstant d) aa C bb w (by positivity) haa hC hbb hw
    ((new.restrict Saug).extensionGreen_isSymm (g.Q z) z)
    hOldEntry hOldTarget hNewEndpoint hNewTarget hW

end RegularGraph
end LocalLaw
