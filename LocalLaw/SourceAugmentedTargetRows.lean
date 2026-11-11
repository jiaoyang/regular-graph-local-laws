import LocalLaw.SourceAugmentedEndpointRows
import LocalLaw.AugmentedOldEndpointRows
import LocalLaw.EndpointFarTailParameters

/-!
# Actual augmented target rows from the original plus event and F1 occupancy

All scalar feedback and far-tail errors are realized. The old augmented
reference class and its intrinsic logarithmic diameter remain geometric
inputs. No class is required of the new augmented model.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance sourceAugmentedTargetRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def augmentedTargetRowCap (d Bnear : ℕ) : ℝ :=
  (2 * finiteExtraReferenceConstant d * (3 * (Bnear : ℝ) + 1)) *
    (1 + endpointSurgeryCouplingCap d * (endpointSurgeryModelRowCap d (2 * (finiteOmega d + 1)) + 1))

namespace RegularGraph

theorem eventually_source_augmented_target_rows (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ‖z‖ ≤ B → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1)
        (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      let R := logarithmicRadius (c / 4) d N
      let selector := R / 4
      let r := effectiveModelRadius a d N β
      let s := g.admissibleState T boundary samples
      let gnew := g.labelledResampledGraph T boundary samples selector
      ∀ (Saug : Set (Tᶜ : Set (Fin N)))
      (hcontain : s.endpointModelVertices selector r ⊆ Saug),
      ((g.deficient.delete T).restrict Saug).ComponentFiniteReferenceBudget →
      ∀ Raug : ℕ, (∀ x y, ((g.deficient.delete T).restrict Saug).graph.dist x y ≤ Raug) →
      (Raug : ℝ) + 1 ≤ sourceObservationLogCap d β * Real.log (N : ℝ) →
      ∀ (Bnear : ℕ) (x : Saug), (tripleNearIndices g.graph T (R / 2) samples x.val).card ≤ Bnear →
      let e := g.augmentedEndpointEmbedding T boundary samples selector r Saug hcontain
      let M := (gnew.deficient.delete T).restrict Saug
      (∑ i : s.endpointModelRoots selector, ‖M.extensionGreen (g.Q z) z x (e i)‖) ≤ augmentedTargetRowCap d Bnear := by
  let C := endpointSurgeryModelRowCap d (2 * (finiteOmega d + 1)) + 1
  let w := endpointSurgeryCouplingCap d
  have hCextra := finiteExtraReferenceConstant_ge_one d hd
  have hC : 0 ≤ C := by dsimp only [C, endpointSurgeryModelRowCap]; positivity
  have hw : 0 ≤ w := by dsimp only [w, endpointSurgeryCouplingCap]; positivity
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_source_augmented_endpoint_rows a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_endpoint_far_tail_small a d 1 ha hd (by norm_num),
    eventually_source_radius_hierarchy a d c β hd hc hβ hβc, hdepth]
    with N hnewRows hnum htail hradii hdepth
  intro g o z hz hscale hzB Cq badCount hplus ι _ boundary samples
  dsimp only
  let ell := actualCavityDepth a d N z - 1
  let R := logarithmicRadius (c / 4) d N
  let selector := R / 4
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary samples
  let old := g.deficient.delete T
  let gnew := g.labelledResampledGraph T boundary samples selector
  let new := gnew.deficient.delete T
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let L := Real.log (N : ℝ)
  intro Saug hcontain hbudget Raug hdiam hRlog Bnear x hnear
  let e := g.augmentedEndpointEmbedding T boundary samples selector r Saug hcontain
  let A := (old.restrict Saug).extensionMatrix (g.Q z) z
  let Bmat := (new.restrict Saug).extensionMatrix (g.Q z) z
  let aa := 2 * finiteExtraReferenceConstant d * (3 * (Bnear : ℝ) + 1)
  have haa : 0 ≤ aa := by dsimp only [aa]; positivity
  have num := hnum z hz hscale
  have hε : 0 ≤ ε := num.error_nonnegative
  have hprior := hplus.cavity.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) hε hC1)
  have hfeedback := (DeficientGraph.weak_localization_feedback_budgets d hd z (g.Q z) hz B
    (C1 ^ 2 * ε) L (sourceObservationLogCap d β) (mul_nonneg (sq_nonneg C1) hε) num.log_one
      num.log_cap_nonnegative num.error_scaled hprior Raug (4 * r + 1) hRlog num.pair_log num.localization_large).1
  have hOldRaw := g.augmented_old_endpoint_rows hd T boundary samples selector r Saug hcontain hbudget
    Raug hdiam (g.Q z) z hz (g.Q_im_nonnegative z hz) hfeedback (R / 2) Bnear x hnear
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have htailSmall : (Nat.card (s.endpointModelRoots selector) : ℝ) * physicalTransfer d z ^ (R / 2) ≤ ε / L ^ 16 := by
    have hh := htail g o ell hell boundary samples selector (logarithmicRadius β d N) (R / 2)
      (by dsimp only [R]; have hh := hradii.1; omega) z hz.le
    simpa only [one_mul] using hh
  have hC1sq : 1 ≤ C1 ^ 2 := by nlinarith
  have hεone : ε ≤ 1 := by
    have hh : ε ≤ (C1 ^ 2 * ε) * L ^ 4 :=
      (le_mul_of_one_le_left hε hC1sq).trans (le_mul_of_one_le_right
        (mul_nonneg (sq_nonneg C1) hε) (one_le_pow₀ num.log_one))
    exact hh.trans num.error_scaled
  have htailOne : (Nat.card (s.endpointModelRoots selector) : ℝ) * physicalTransfer d z ^ (R / 2) ≤ 1 :=
    htailSmall.trans ((div_le_self hε (one_le_pow₀ num.log_one)).trans hεone)
  have hOld : ∑ i, ‖A⁻¹ x (e i)‖ ≤ aa := by
    apply hOldRaw.trans
    exact mul_le_mul_of_nonneg_left (add_le_add_left htailOne _) (by positivity)
  have hNew : ∀ i, ∑ j, ‖Bmat⁻¹ (e i) (e j)‖ ≤ C :=
    (hnewRows g o z hz hscale hzB Cq badCount hplus boundary samples Saug hcontain hbudget Raug hdiam hRlog).1
  have hcross : ∀ v : Saug, ∀ y : (Saugᶜ : Set (Tᶜ : Set (Fin N))),
      old.graph.Adj v.val y.val ↔ new.graph.Adj v.val y.val := by
    intro v y
    have hy : y.val ∉ s.fullResampleOutsideEndpoints selector := by
      intro h
      have hr := s.fullResampleOutsideEndpoints_subset_modelRoots selector h
      exact y.property (hcontain (s.endpointModelKernelEmbedding selector r ⟨y.val, hr⟩).property)
    rw [old.graph.adj_comm, new.graph.adj_comm]
    exact (s.fullResample_outside_adj_of_away_left selector y.val v.val hy).symm
  have hmatrix := old.restrict_extensionMatrix_difference new Saug
    (g.deleted_degree_deficit_saturated T) (gnew.deleted_degree_deficit_saturated T) hcross (g.Q z) z
  have hsupp : ∀ u v, u ∉ Set.range e ∨ v ∉ Set.range e → (Bmat - A) u v = 0 := by
    intro u v huv
    rw [hmatrix]
    apply s.fullResample_outside_difference_supported selector d u.val v.val
    exact huv.imp
      (fun hu hr => hu ⟨⟨u.val, s.fullResampleOutsideEndpoints_subset_modelRoots selector hr⟩, Subtype.ext rfl⟩)
      (fun hv hr => hv ⟨⟨v.val, s.fullResampleOutsideEndpoints_subset_modelRoots selector hr⟩, Subtype.ext rfl⟩)
  have hW : ∀ i, ∑ j, ‖(Bmat - A) (e i) (e j)‖ ≤ w := by
    intro i
    have heq : (Bmat - A).submatrix e e = g.sourceEndpointW T boundary samples selector := by
      rw [hmatrix]
      rfl
    change (∑ j, ‖((Bmat - A).submatrix e e) i j‖) ≤ w
    rw [heq]
    exact (g.source_endpoint_coupling_mass T boundary samples selector).1 i
  exact inverse_supported_endpoint_row_sum A Bmat
    ((old.restrict Saug).extensionMatrix_isUnit hd (g.Q z) z hz (g.Q_im_nonnegative z hz))
    ((new.restrict Saug).extensionMatrix_isUnit hd (g.Q z) z hz (g.Q_im_nonnegative z hz))
    e hsupp aa C w haa hC hw x hOld hNew hW

end RegularGraph
end LocalLaw
