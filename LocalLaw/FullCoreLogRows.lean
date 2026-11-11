import LocalLaw.FullCoreMateModel
import LocalLaw.FullEndpointLogRows

/-! # Actual edge-cut core rows from finite reference squared-mass bounds -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance fullCoreLogRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

omit [Fintype ι] in
theorem fullCoreEdgeCut_log_rows (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (labels : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T) (selector : ℕ) (S : Set (Fin N))
    (hb : (g.deficient.restrict S).ComponentFiniteReferenceBudget) (R : ℕ)
    (hR : ∀ x y, (g.graph.induce S).dist x y ≤ R)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (a : ℕ) (L U A : ℝ) (ha : 2 ≤ a) (hL : 1 ≤ L) (hU : 0 ≤ U) (hA : 0 ≤ A)
    (hcount : (Nat.card ((g.admissibleState T labels samples).fullCoreMask S) : ℝ) ≤
      U * L ^ (2 * a - 4))
    (hlog : (hereditaryReferenceRadius d R : ℝ) + 1 ≤ A * L)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((hereditaryReferenceRadius d R : ℝ) + 1) ≤ 1 / 2) :
    let s := g.admissibleState T labels samples
    let e := s.fullCoreEmbedding S
    let cut := g.fullCoreEdgeCutModel T labels samples selector S
    ∀ k, (∑ k', ‖cut.extensionGreen q z (e k) (e k')‖) ≤
      (U * (8 * finiteExtraReferenceConstant d ^ 2 * A) + 1) * L ^ (a - 1) := by
  dsimp only
  let s := g.admissibleState T labels samples
  let e := s.fullCoreEmbedding S
  let cut := g.fullCoreEdgeCutModel T labels samples selector S
  have hcut := g.fullCoreEdgeCut_reference_budget T labels samples selector S hb
  have hdiam := g.fullCoreEdgeCut_intrinsic_diameter T labels samples selector S hb R hR
  intro k
  have hsq := cut.componentwise_extensionGreen_square_sum hd hcut z q hz hq
    (hereditaryReferenceRadius d R) hdiam small (e k)
  have hsub : (∑ k', ‖cut.extensionGreen q z (e k) (e k')‖ ^ 2) ≤
      ∑ v, ‖cut.extensionGreen q z (e k) v‖ ^ 2 := by
    calc
      _ = ∑ v ∈ Finset.univ.image e, ‖cut.extensionGreen q z (e k) v‖ ^ 2 :=
        (Finset.sum_image (fun _ _ _ _ h => e.injective h)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  have hmass : (∑ k', ‖cut.extensionGreen q z (e k) (e k')‖ ^ 2) ≤
      (8 * finiteExtraReferenceConstant d ^ 2 * A) * L := by
    calc
      _ ≤ 8 * finiteExtraReferenceConstant d ^ 2 * ((hereditaryReferenceRadius d R : ℝ) + 1) := hsub.trans hsq
      _ ≤ 8 * finiteExtraReferenceConstant d ^ 2 * (A * L) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by ring
  have hcard : (Fintype.card (s.fullCoreMask S) : ℝ) ≤ U * L ^ (2 * a - 4) := by
    simpa only [Nat.card_eq_fintype_card] using hcount
  exact full_mask_log_row_bound (fun k' => cut.extensionGreen q z (e k) (e k')) a L U
    (8 * finiteExtraReferenceConstant d ^ 2 * A) ha hL hU (by positivity) hcard hmass

end RegularGraph
end LocalLaw
