import LocalLaw.CutIncidence
import LocalLaw.DeficientGraphModel

/-! # Exact physical retained Schur and literal truncated-model inverses -/

noncomputable section
namespace LocalLaw
local instance physicalBoundarySchurDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}

theorem physical_retained_boundary_inverse (g : RegularGraph N d)
    (T : Set (Fin N)) (z : ℂ) (hz : 0 < z.im) :
    IsUnit ((g.G z).submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N)) ∧
    ((g.G z).submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N))⁻¹ =
      spectralMatrix (g.H.submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N)) z -
        cutInnerCoupling g.graph d T *
          ((g.deficient.delete T).G z).submatrix (boundaryOutsideVertex g.graph T) (boundaryOutsideVertex g.graph T) *
          (cutInnerCoupling g.graph d T).transpose := by
  have h := green_retained_principal_inverse T g.H (normalizedAdjacency_isHermitian _ _) z hz
  constructor
  · exact h.1
  · have hself := normalized_cut_selfEnergy g.graph d T ((g.deficient.delete T).G z)
    have hdel : green (g.H.submatrix (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)
        (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)) z = (g.deficient.delete T).G z := by
      change green (g.deficient.H.submatrix (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)
        (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)) z = _
      rw [← g.deficient.H_delete T]
      rfl
    rw [hdel] at h
    exact h.2.trans (congrArg (fun M => spectralMatrix
      (g.H.submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N)) z - M) hself)

theorem truncatedModelGreen_isUnit (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    IsUnit ((g.deficient.restrict T).extensionGreen q z) := by
  change IsUnit (((g.deficient.restrict T).extensionMatrix q z)⁻¹)
  exact Matrix.isUnit_nonsing_inv_iff.mpr ((g.deficient.restrict T).extensionMatrix_isUnit hd q z hz hq)

theorem truncatedModelGreen_inverse (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    ((g.deficient.restrict T).extensionGreen q z)⁻¹ =
      spectralMatrix (g.H.submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N)) z -
        q • (g.deficient.restrict T).boundaryDiagonal := by
  change (((g.deficient.restrict T).extensionMatrix q z)⁻¹)⁻¹ = _
  rw [((g.deficient.restrict T).extensionMatrix q z).nonsing_inv_nonsing_inv
    (((g.deficient.restrict T).extensionMatrix q z).isUnit_iff_isUnit_det.mp
    ((g.deficient.restrict T).extensionMatrix_isUnit hd q z hz hq))]
  change spectralMatrix (g.deficient.restrict T).H z - q • (g.deficient.restrict T).boundaryDiagonal = _
  rw [g.deficient.H_restrict T]
  rfl

end RegularGraph
end LocalLaw
