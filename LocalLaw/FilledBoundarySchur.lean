import LocalLaw.FilledExteriorModel
import LocalLaw.CutIncidence

/-! # Exact boundary-labelled Schur formula for a filled exterior model -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance filledBoundarySchurDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Projection
variable {J K : Type*} [Fintype J] [Fintype K] [DecidableEq K]

def endpointProjection (p : J → K) : Matrix J K ℂ := fun j k => if p j = k then 1 else 0

omit [Fintype J] in
/-- Repeated endpoint labels select the genuine kernel with their full
multiplicity; endpoint injectivity is not required. -/
theorem endpointProjection_sandwich (p : J → K) (Q : Matrix K K ℂ) :
    endpointProjection p * Q * (endpointProjection p).transpose = Q.submatrix p p := by
  have hleft (j : J) (k : K) : (endpointProjection p * Q) j k = Q (p j) k := by
    simp [Matrix.mul_apply, endpointProjection, ite_mul]
  ext i j
  simp [Matrix.mul_apply, hleft, endpointProjection, Matrix.transpose_apply, mul_ite]

end Projection

section Reindex
variable {I J K : Type*} [Fintype J] [Fintype K]

theorem sandwich_equiv_middle (A : Matrix I K ℂ) (Q : Matrix K K ℂ)
    (B : Matrix K I ℂ) (e : J ≃ K) :
    A * Q * B = A.submatrix id e * Q.submatrix e e * B.submatrix e id := by
  have hh := Matrix.submatrix_mul (A * Q) B id e id e.bijective
  simp only [Matrix.submatrix_id_id] at hh
  rw [Matrix.submatrix_mul A Q id e e e.bijective] at hh
  exact hh

end Reindex

namespace RegularGraph
variable {N d : ℕ}

def filledBoundaryVertex (g : RegularGraph N d) (T : Set (Fin N)) (K : Set (Tᶜ : Set (Fin N)))
    (hK : ∀ e : BoundaryOrientedEdge g.graph T, boundaryOutsideVertex g.graph T e ∈ K) :
    BoundaryOrientedEdge g.graph T → K := fun e => ⟨boundaryOutsideVertex g.graph T e, hK e⟩

theorem filledCutCoupling_factor (g : RegularGraph N d)
    (T : Set (Fin N)) (K : Set (Tᶜ : Set (Fin N)))
    (hK : ∀ e : BoundaryOrientedEdge g.graph T, boundaryOutsideVertex g.graph T e ∈ K) :
    g.filledCutCoupling T K = cutInnerCoupling g.graph d T *
      endpointProjection (g.filledBoundaryVertex T K hK) := by
  ext i j
  have hh := congrFun (congrFun (normalized_cut_incidence g.graph d T) i) j.val
  change g.H i.val j.val.val = _
  convert hh using 1
  simp only [Matrix.mul_apply, cutOuterProjection, endpointProjection, filledBoundaryVertex]
  apply Finset.sum_congr rfl
  intro e _
  have heq : (⟨boundaryOutsideVertex g.graph T e, hK e⟩ : K) = j ↔ e.val.2 = j.val.val := by
    constructor
    · intro h
      exact congrArg (fun x : K => x.val.val) h
    · intro h
      exact Subtype.ext (Subtype.ext h)
  simp only [heq]

/-- Every exterior contribution is indexed by the actual boundary edges. -/
theorem filledCutCoupling_selfEnergy (g : RegularGraph N d)
    (T : Set (Fin N)) (K : Set (Tᶜ : Set (Fin N)))
    (hK : ∀ e : BoundaryOrientedEdge g.graph T, boundaryOutsideVertex g.graph T e ∈ K)
    (Q : Matrix K K ℂ) :
    g.filledCutCoupling T K * Q * (g.filledCutCoupling T K).transpose =
      cutInnerCoupling g.graph d T *
        Q.submatrix (g.filledBoundaryVertex T K hK) (g.filledBoundaryVertex T K hK) *
          (cutInnerCoupling g.graph d T).transpose := by
  rw [g.filledCutCoupling_factor T K hK]
  calc
    _ = cutInnerCoupling g.graph d T *
        (endpointProjection (g.filledBoundaryVertex T K hK) * Q *
          (endpointProjection (g.filledBoundaryVertex T K hK)).transpose) *
        (cutInnerCoupling g.graph d T).transpose := by
      rw [Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [endpointProjection_sandwich]

theorem filledRetainedGreen_boundary_inverse (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (K : Set (Tᶜ : Set (Fin N)))
    (hK : ∀ e : BoundaryOrientedEdge g.graph T, boundaryOutsideVertex g.graph T e ∈ K)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    (g.filledRetainedGreen T K q z)⁻¹ =
      spectralMatrix (g.H.submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N)) z -
        cutInnerCoupling g.graph d T *
          (((g.deficient.delete T).restrict K).extensionGreen q z).submatrix
            (g.filledBoundaryVertex T K hK) (g.filledBoundaryVertex T K hK) *
          (cutInnerCoupling g.graph d T).transpose := by
  rw [g.filledRetainedGreen_inverse hd T K hK q z hz hq, g.filledCutCoupling_selfEnergy T K hK]


/-- Boundary labels may be relabelled by a true edge equivalence. Preserving
its inner endpoints and the exact exterior block preserves the full retained
finite Green function. -/
theorem filledRetainedGreen_eq_of_boundary_block (g h : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (K L : Set (Tᶜ : Set (Fin N)))
    (hK : ∀ e : BoundaryOrientedEdge g.graph T, boundaryOutsideVertex g.graph T e ∈ K)
    (hL : ∀ e : BoundaryOrientedEdge h.graph T, boundaryOutsideVertex h.graph T e ∈ L)
    (boundary : BoundaryOrientedEdge g.graph T ≃ BoundaryOrientedEdge h.graph T)
    (hfirst : ∀ e, (boundary e).val.1 = e.val.1)
    (hinner : g.H.submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N) =
      h.H.submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N))
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (hblock : ∀ a b,
      ((g.deficient.delete T).restrict K).extensionGreen q z
        (g.filledBoundaryVertex T K hK a) (g.filledBoundaryVertex T K hK b) =
      ((h.deficient.delete T).restrict L).extensionGreen q z
        (h.filledBoundaryVertex T L hL (boundary a)) (h.filledBoundaryVertex T L hL (boundary b))) :
    g.filledRetainedGreen T K q z = h.filledRetainedGreen T L q z := by
  apply g.filledRetainedGreen_eq_of_selfEnergy h hd T K L hK hL hinner q z hz hq
  rw [g.filledCutCoupling_selfEnergy T K hK, h.filledCutCoupling_selfEnergy T L hL]
  rw [sandwich_equiv_middle _ _ _ boundary]
  have hU : (cutInnerCoupling h.graph d T).submatrix id boundary = cutInnerCoupling g.graph d T := by
    ext i e
    simp only [Matrix.submatrix_apply, id_eq, cutInnerCoupling, hfirst]
  have hUt : (cutInnerCoupling h.graph d T).transpose.submatrix boundary id =
      (cutInnerCoupling g.graph d T).transpose := by
    ext e i
    exact congrFun (congrFun hU i) e
  have hQ : ((((h.deficient.delete T).restrict L).extensionGreen q z).submatrix
      (h.filledBoundaryVertex T L hL) (h.filledBoundaryVertex T L hL)).submatrix boundary boundary =
      (((g.deficient.delete T).restrict K).extensionGreen q z).submatrix
        (g.filledBoundaryVertex T K hK) (g.filledBoundaryVertex T K hK) := by
    ext a b
    exact (hblock a b).symm
  rw [hU, hUt, hQ]

end RegularGraph
end LocalLaw
