import LocalLaw.ActualFullQuadCoupling

/-! # Genuine retained precision differences give both resolvent updates -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance inversePrecisionUpdateDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem inverse_precision_updates {I : Type} [Fintype I] [DecidableEq I]
    (R U W : Matrix I I ℂ) (hR : IsUnit R) (hU : IsUnit U) (h : U⁻¹ = R⁻¹ + W) :
    (U + R * W * U = R) ∧ (U + U * W * R = R) := by
  have hW : W = U⁻¹ - R⁻¹ := by rw [h]; abel
  have hRR : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det R).mp hR)
  have hR'R : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R ((Matrix.isUnit_iff_isUnit_det R).mp hR)
  have hUU : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U ((Matrix.isUnit_iff_isUnit_det U).mp hU)
  have hU'U : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U ((Matrix.isUnit_iff_isUnit_det U).mp hU)
  constructor
  · calc
      _ = U + (R * U⁻¹ * U - R * R⁻¹ * U) := by rw [hW,Matrix.mul_sub,Matrix.sub_mul]
      _ = U + (R - U) := by rw [Matrix.mul_assoc,hU'U,hRR,Matrix.mul_one,Matrix.one_mul]
      _ = R := by abel
  · calc
      _ = U + (U * U⁻¹ * R - U * R⁻¹ * R) := by rw [hW,Matrix.mul_sub,Matrix.sub_mul]
      _ = U + (R - U) := by rw [hUU,Matrix.mul_assoc,hR'R,Matrix.one_mul,Matrix.mul_one]
      _ = R := by abel

namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem full_partial_model_endpoint_updates (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (labels : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T) (selector : ℕ) (hs : 1 ≤ selector)
    (S : Set (Fin N)) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let s := g.admissibleState T labels samples
    let h := g.labelledResampledGraph T labels samples selector
    let e := s.fullPartialEmbedding selector S hs
    let R := ((g.deficient.restrict S).extensionGreen q z).submatrix e e
    let U := ((h.deficient.restrict S).extensionGreen q z).submatrix e e
    let W : Matrix (s.FullEndpointIndex selector S) (s.FullEndpointIndex selector S) ℂ :=
      fullQuadSurgeryCoupling (s.fullInnerMate selector S) (s.fullOuterMate selector S)
        (s.fullFirstMask selector S) (s.fullSecondMask selector S) q (treeEdgeWeight d)
    IsUnit R ∧ IsUnit U ∧ (U + R * W * U = R) ∧ (U + U * W * R = R) := by
  dsimp only
  have hh := g.full_partial_retained_quad_precision hd T labels samples selector hs S q z hz hq
  dsimp only at hh
  exact ⟨hh.1,hh.2.1,inverse_precision_updates _ _ _ hh.1 hh.2.1 hh.2.2⟩

end RegularGraph
end LocalLaw
