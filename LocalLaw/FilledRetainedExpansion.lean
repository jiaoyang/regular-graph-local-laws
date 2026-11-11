import LocalLaw.FilledBoundarySchur
import LocalLaw.BoundaryDiagonalExpansion

/-!
# Exact row expansion using the same exterior kernel as surgery

The full finite model fills a chosen actual outside restriction by T. Its
Schur difference is the genuine deleted physical Green matrix minus that
outside restriction, on actual boundary-edge labels.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance filledRetainedExpansionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}

def filledBoundaryDefect (g : RegularGraph N d) (T : Set (Fin N))
    (K : Set (Tᶜ : Set (Fin N)))
    (hK : ∀ e : BoundaryOrientedEdge g.graph T, boundaryOutsideVertex g.graph T e ∈ K)
    (q z : ℂ) : Matrix (BoundaryOrientedEdge g.graph T) (BoundaryOrientedEdge g.graph T) ℂ :=
  ((g.deficient.delete T).G z).submatrix (boundaryOutsideVertex g.graph T) (boundaryOutsideVertex g.graph T) -
    (((g.deficient.delete T).restrict K).extensionGreen q z).submatrix
      (g.filledBoundaryVertex T K hK) (g.filledBoundaryVertex T K hK)

theorem physicalRetained_boundary_inverse (g : RegularGraph N d)
    (T : Set (Fin N)) (z : ℂ) (hz : 0 < z.im) :
    ((g.G z).submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N))⁻¹ =
      spectralMatrix (g.H.submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N)) z -
        cutInnerCoupling g.graph d T *
          ((g.deficient.delete T).G z).submatrix
            (boundaryOutsideVertex g.graph T) (boundaryOutsideVertex g.graph T) *
          (cutInnerCoupling g.graph d T).transpose := by
  have hh := (green_retained_principal_inverse T g.H (normalizedAdjacency_isHermitian g.graph d) z hz).2
  have hdel : green (g.H.submatrix (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)
      (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)) z = (g.deficient.delete T).G z := by
    change _ = green (normalizedAdjacency (g.graph.induce Tᶜ) d) z
    rw [normalizedAdjacency_induce]
    rfl
  rw [hdel] at hh
  change ((g.G z).submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N))⁻¹ =
    spectralMatrix (g.H.submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N)) z -
      (normalizedAdjacency g.graph d).submatrix (Subtype.val : T → Fin N) (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N) *
        (g.deficient.delete T).G z *
        (normalizedAdjacency g.graph d).submatrix (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N) (Subtype.val : T → Fin N) at hh
  rw [normalized_cut_selfEnergy] at hh
  exact hh

theorem filledRetained_inverse_difference (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (K : Set (Tᶜ : Set (Fin N)))
    (hK : ∀ e : BoundaryOrientedEdge g.graph T, boundaryOutsideVertex g.graph T e ∈ K)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    (g.filledRetainedGreen T K q z)⁻¹ -
      ((g.G z).submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N))⁻¹ =
      cutInnerCoupling g.graph d T * g.filledBoundaryDefect T K hK q z *
        (cutInnerCoupling g.graph d T).transpose := by
  rw [g.filledRetainedGreen_boundary_inverse hd T K hK q z hz hq,
    g.physicalRetained_boundary_inverse T z hz]
  unfold filledBoundaryDefect
  rw [Matrix.mul_sub, Matrix.sub_mul]
  abel

/-- A literal three-term row estimate with physical inverse units and the
self-energy factorization proved for this actual exterior model. -/
theorem filledRetained_row_three_term (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (K : Set (Tᶜ : Set (Fin N)))
    (hK : ∀ e : BoundaryOrientedEdge g.graph T, boundaryOutsideVertex g.graph T e ∈ K)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (x y : T) :
    let R := (g.G z).submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N)
    let P := g.filledRetainedGreen T K q z
    let U := cutInnerCoupling g.graph d T
    let D := g.filledBoundaryDefect T K hK q z
    ‖R x y - P x y‖ ≤
      ‖∑ a, (P * U) x a * (U.transpose * P) a y * D a a‖ +
      ‖∑ a, ∑ b ∈ (Finset.univ.erase a), (P * U) x a * D a b * (U.transpose * P) b y‖ +
      ‖((R - P) * U * D * U.transpose * P) x y‖ := by
  apply retained_boundary_row_three_term _ _ _ _ _
    (green_retained_principal_inverse T g.H (normalizedAdjacency_isHermitian g.graph d) z hz).1
    (g.filledRetainedGreen_isUnit hd T K q z hz hq)
    (g.filledRetained_inverse_difference hd T K hK q z hz hq)

end RegularGraph
end LocalLaw
