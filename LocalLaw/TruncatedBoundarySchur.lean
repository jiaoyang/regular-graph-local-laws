import LocalLaw.PhysicalBoundarySchur
import LocalLaw.BoundaryChargeGram

/-! # Exact T-Schur defect relative to the genuine truncated T model

The comparison model is Ext(T,q), with its actual missing-neighbor charge.
The driving boundary defect is the physical outside kernel minus q times
the identity. Every physical and model inverse is proved nonsingular.
-/

noncomputable section
namespace LocalLaw
local instance truncatedBoundarySchurDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}

def truncatedBoundaryDefect (g : RegularGraph N d) (T : Set (Fin N)) (q z : ℂ) :
    Matrix (BoundaryOrientedEdge g.graph T) (BoundaryOrientedEdge g.graph T) ℂ :=
  ((g.deficient.delete T).G z).submatrix (boundaryOutsideVertex g.graph T) (boundaryOutsideVertex g.graph T) - q • 1

theorem truncated_boundary_inverse_difference (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    ((g.deficient.restrict T).extensionGreen q z)⁻¹ -
      ((g.G z).submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N))⁻¹ =
    cutInnerCoupling g.graph d T * g.truncatedBoundaryDefect T q z * (cutInnerCoupling g.graph d T).transpose := by
  rw [g.truncatedModelGreen_inverse hd T q z hz hq, (g.physical_retained_boundary_inverse T z hz).2]
  unfold truncatedBoundaryDefect
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    ← g.truncated_boundaryDiagonal_eq_cutGram hd T]
  abel

/-- Exact source-(6.35) expansion with the actual truncated T Green matrix.
The defect includes the diagonal scalar q, rather than a filled reference. -/
theorem truncated_boundary_retained_expansion (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let R := (g.G z).submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N)
    let P := (g.deficient.restrict T).extensionGreen q z
    let U := cutInnerCoupling g.graph d T
    let D := g.truncatedBoundaryDefect T q z
    R - P = P * (U * D * U.transpose) * P + (R - P) * (U * D * U.transpose) * P := by
  dsimp only
  exact retained_difference_expansion _ _ _ (g.physical_retained_boundary_inverse T z hz).1
    (g.truncatedModelGreen_isUnit hd T q z hz hq) (g.truncated_boundary_inverse_difference hd T q z hz hq)

end RegularGraph
end LocalLaw
