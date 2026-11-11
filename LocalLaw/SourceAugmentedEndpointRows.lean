import LocalLaw.AugmentedEndpointStability
import LocalLaw.SourceEndpointReferenceRows
import LocalLaw.SourceNewEndpointCaps
import LocalLaw.AugmentedRowTransfer

/-!
# Realized new augmented endpoint rows without a post augmented class

The canonical post endpoint model has its proved row bound. The actual
four-model comparison and the realized endpoint count transfer this bound
to both rows and columns of every augmented post inverse.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceAugmentedEndpointRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_augmented_endpoint_rows (a b d : ℕ) (c β B C1 : ℝ)
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
      let selector := logarithmicRadius (c / 4) d N / 4
      let r := effectiveModelRadius a d N β
      let s := g.admissibleState T boundary samples
      let gnew := g.labelledResampledGraph T boundary samples selector
      ∀ (Saug : Set (Tᶜ : Set (Fin N)))
      (hcontain : s.endpointModelVertices selector r ⊆ Saug),
      ((g.deficient.delete T).restrict Saug).ComponentFiniteReferenceBudget →
      ∀ Raug : ℕ, (∀ x y, ((g.deficient.delete T).restrict Saug).graph.dist x y ≤ Raug) →
      (Raug : ℝ) + 1 ≤ sourceObservationLogCap d β * Real.log (N : ℝ) →
      let e := g.augmentedEndpointEmbedding T boundary samples selector r Saug hcontain
      let U := (((gnew.deficient.delete T).restrict Saug).extensionGreen (g.Q z) z).submatrix e e
      (∀ i, ∑ j, ‖U i j‖ ≤ endpointSurgeryModelRowCap d (2 * (finiteOmega d + 1)) + 1) ∧
        (∀ j, ∑ i, ‖U i j‖ ≤ endpointSurgeryModelRowCap d (2 * (finiteOmega d + 1)) + 1) := by
  let C := endpointSurgeryModelRowCap d (2 * (finiteOmega d + 1))
  let D := 2 * sourceEndpointErrorConstant d C1
  have hC : 0 ≤ C := by dsimp only [C, endpointSurgeryModelRowCap]; have hh := finiteExtraReferenceConstant_ge_one d hd; positivity
  have hC10 : 0 ≤ C1 := (by norm_num : (0 : ℝ) ≤ 1).trans hC1
  have hD : 0 ≤ D := mul_nonneg (by norm_num) (sourceEndpointErrorConstant_nonnegative d C1 hC10)
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_augmented_endpoint_stability_with_diameter a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_endpoint_reference_rows a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_endpoint_surgery_smallness a b d β 0 1 D ha hb hd hβ (by norm_num) (by norm_num) hD,
    hdepth, eventually_log_ge_nat 1, Filter.eventually_ge_atTop 1]
    with N happrox hQ hsmall hdepth hlog hN
  intro g o z hz hscale hzB Cq badCount hplus ι _ boundary samples
  dsimp only
  let ell := actualCavityDepth a d N z - 1
  let T := graphBallVertices g.graph o ell
  let selector := logarithmicRadius (c / 4) d N / 4
  let r := effectiveModelRadius a d N β
  let s := g.admissibleState T boundary samples
  let gnew := g.labelledResampledGraph T boundary samples selector
  let δ := D * g.sourcePrime a (logarithmicRadius β d N) z
  intro Saug hcontain hbudget Raug hdiam hRlog
  let e := g.augmentedEndpointEmbedding T boundary samples selector r Saug hcontain
  let U := (((gnew.deficient.delete T).restrict Saug).extensionGreen (g.Q z) z).submatrix e e
  let Q := g.sourceEndpointQ T boundary samples selector r (g.Q z) z
  have hδ : 0 ≤ δ := by
    have hε := graphPaperError_nonnegative a d N (logarithmicRadius β d N) z hN hz.le
    unfold δ sourcePrime inflatedPrime
    positivity
  have hE : ∀ i j, ‖U i j - Q i j‖ ≤ δ :=
    happrox g o z hz hscale hzB Cq badCount hplus boundary samples Saug hcontain hbudget Raug hdiam hRlog
  have hrows := hQ g o z hz hscale hzB Cq badCount hplus boundary samples
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hdim : (Fintype.card (s.endpointModelRoots selector) : ℝ) * δ ≤ 1 := by
    have hh := hsmall g o ell hell boundary samples selector z hz hscale
    have hh' : (Nat.card (s.endpointModelRoots selector) : ℝ) * δ ≤ 1 / 2 := by
      simpa only [zero_mul, mul_zero, add_zero, one_mul, mul_one] using hh
    have hcast : (Fintype.card (s.endpointModelRoots selector) : ℝ) * δ ≤ 1 / 2 := by
      simpa only [Nat.card_eq_fintype_card] using hh'
    exact hcast.trans (by norm_num)
  constructor
  · intro i
    exact (endpoint_row_sum_of_entry_approximation U Q C δ hC hδ hrows.1 hE i).trans
      (add_le_add_left hdim C)
  · intro j
    have hh := endpoint_row_sum_of_entry_approximation U.transpose Q.transpose C δ hC hδ hrows.2
      (fun i j => hE j i) j
    exact hh.trans (add_le_add_left hdim C)

end RegularGraph
end LocalLaw
