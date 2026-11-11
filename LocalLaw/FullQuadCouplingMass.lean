import LocalLaw.ActualFullQuadCoupling

/-! # Constant row and column mass of the actual full switching coupling -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance fullQuadCouplingMassDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem matrix_row_charge_mass {J : Type} [Fintype J] [DecidableEq J]
    (W : Matrix J J ℂ) (β : ℂ) (w : ℝ) (_hw : 0 ≤ w) (hβ : ‖β‖ ≤ 1)
    (hrow : ∀ i, ∑ j, ‖W i j‖ ≤ w) (hcol : ∀ j, ∑ i, ‖W i j‖ ≤ w) :
    let U := W + β • Matrix.diagonal (fun i => ∑ j, W i j)
    (∀ i, ∑ j, ‖U i j‖ ≤ 2*w) ∧ (∀ j, ∑ i, ‖U i j‖ ≤ 2*w) := by
  dsimp only
  have hsum (i : J) : ‖∑ j,W i j‖ ≤ w := (norm_sum_le _ _).trans (hrow i)
  constructor
  · intro i
    calc
      _ ≤ ∑ j, (‖W i j‖ + ‖β‖ * ‖Matrix.diagonal (fun i => ∑ j,W i j) i j‖) := by
        apply Finset.sum_le_sum
        intro j _
        exact (norm_add_le _ _).trans (add_le_add_left (le_of_eq (norm_mul _ _)) _)
      _ = (∑ j,‖W i j‖) + ‖β‖ * ‖∑ j,W i j‖ := by
        rw [Finset.sum_add_distrib,←Finset.mul_sum]
        simp [Matrix.diagonal_apply,apply_ite norm]
      _ ≤ w + 1*w := add_le_add (hrow i) (mul_le_mul hβ (hsum i) (norm_nonneg _) (by norm_num))
      _ = _ := by ring
  · intro j
    calc
      _ ≤ ∑ i, (‖W i j‖ + ‖β‖ * ‖Matrix.diagonal (fun i => ∑ j,W i j) i j‖) := by
        apply Finset.sum_le_sum
        intro i _
        exact (norm_add_le _ _).trans (add_le_add_left (le_of_eq (norm_mul _ _)) _)
      _ = (∑ i,‖W i j‖) + ‖β‖ * ‖∑ k,W j k‖ := by
        rw [Finset.sum_add_distrib,←Finset.mul_sum]
        simp [Matrix.diagonal_apply,apply_ite norm]
      _ ≤ w + 1*w := add_le_add (hcol j) (mul_le_mul hβ (hsum j) (norm_nonneg _) (by norm_num))
      _ = _ := by ring

namespace LabelledResamplingState
variable {V : Type} [Fintype V] {T : Set V} {ι : Type} [Fintype ι]

theorem fullQuadSurgeryCoupling_mass (s : LabelledResamplingState V T ι)
    (selector : ℕ) (S : Set V) (hs : 1 ≤ selector) (d : ℕ)
    (hdegree : ∀ v, s.graph.degree v ≤ d) (q : ℂ) (hq : ‖q * treeEdgeWeight d‖ ≤ 1) :
    let W : Matrix (s.FullEndpointIndex selector S) (s.FullEndpointIndex selector S) ℂ :=
      fullQuadSurgeryCoupling (s.fullInnerMate selector S) (s.fullOuterMate selector S)
        (s.fullFirstMask selector S) (s.fullSecondMask selector S) q (treeEdgeWeight d)
    (∀ i,∑ j,‖W i j‖≤4*(d:ℝ)/Real.sqrt ((d:ℝ)-1)) ∧
      (∀ j,∑ i,‖W i j‖≤4*(d:ℝ)/Real.sqrt ((d:ℝ)-1)) := by
  dsimp only
  let J := s.fullCoreMask S ⊕ (s.fullFirstMask selector S ⊕ s.fullSecondMask selector S)
  let φ : s.FullEndpointIndex selector S ≃ J := Equiv.refl _
  let f : J ↪ V := ⟨fun i => (s.fullPartialEmbedding selector S hs i).val,by
    intro i j he
    exact (s.fullPartialEmbedding selector S hs).injective (Subtype.ext he)⟩
  let W0 : Matrix J J ℂ := fullQuadSurgeryCoupling (s.fullInnerMate selector S) (s.fullOuterMate selector S)
    (s.fullFirstMask selector S) (s.fullSecondMask selector S) 0 (treeEdgeWeight d)
  have hW : W0 = (normalizedAdjacency (s.fullResample selector).graph d - normalizedAdjacency s.graph d).submatrix f f := by
    ext i j
    have he := congrArg (fun M : Matrix (s.FullEndpointIndex selector S) (s.FullEndpointIndex selector S) ℂ => M i j)
      (s.fullSignedEdgeBlock_eq selector S hs (treeEdgeWeight d))
    change _ = W0 i j at he
    rw [←he]
    simp only [fullSignedEdgeBlock,Matrix.submatrix_apply,Matrix.sub_apply,normalizedAdjacency,
      Matrix.smul_apply,smul_eq_mul,SimpleGraph.adjMatrix_apply,treeEdgeWeight,f,Function.Embedding.coeFn_mk]
    ring
  have hp := s.fullResample_endpoint_mass selector d hdegree f
  rw [←hW] at hp
  have hm := matrix_row_charge_mass W0 (q*treeEdgeWeight d)
    (2*(d:ℝ)/Real.sqrt ((d:ℝ)-1)) (by positivity) hq hp.1 hp.2
  have he := fullQuadSurgery_row_charge (s.fullInnerMate selector S) (s.fullOuterMate selector S)
    (s.fullFirstMask selector S) (s.fullSecondMask selector S) q (treeEdgeWeight d)
  change _ = W0 + _ at he
  rw [←he] at hm
  let Qraw : Matrix J J ℂ := fullQuadSurgeryCoupling (s.fullInnerMate selector S) (s.fullOuterMate selector S)
    (s.fullFirstMask selector S) (s.fullSecondMask selector S) q (treeEdgeWeight d)
  let Q0 : Matrix (s.FullEndpointIndex selector S) (s.FullEndpointIndex selector S) ℂ := Qraw
  constructor
  · intro i
    change (∑ j, ‖Q0 i j‖) ≤ _
    have hsum : (∑ j, ‖Q0 i j‖) = ∑ j : J, ‖Qraw (φ i) j‖ := φ.sum_comp (fun j : J => ‖fullQuadSurgeryCoupling (s.fullInnerMate selector S) (s.fullOuterMate selector S)
      (s.fullFirstMask selector S) (s.fullSecondMask selector S) q (treeEdgeWeight d) (φ i) j‖)
    rw [hsum]
    convert hm.1 (φ i) using 1; ring
  · intro j
    change (∑ i, ‖Q0 i j‖) ≤ _
    have hsum : (∑ i, ‖Q0 i j‖) = ∑ i : J, ‖Qraw i (φ j)‖ := φ.sum_comp (fun i : J => ‖fullQuadSurgeryCoupling (s.fullInnerMate selector S) (s.fullOuterMate selector S)
      (s.fullFirstMask selector S) (s.fullSecondMask selector S) q (treeEdgeWeight d) i (φ j)‖)
    rw [hsum]
    convert hm.2 (φ j) using 1; ring

end LabelledResamplingState
end LocalLaw
