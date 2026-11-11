import LocalLaw.TruncatedBoundarySchur
import LocalLaw.TruncatedTreeCavity

/-! # The same boundary defect for the actual neighbor-deleted physical row

Removing a retained vertex restricts both retained inverse operators to
their genuine principal minor. Consequently the outside boundary defect is
unchanged and only the coupling rows are restricted.
-/

noncomputable section
set_option maxHeartbeats 2800000
namespace LocalLaw
local instance minorTruncatedBoundarySchurDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}

def retainedMinorEmbedding (_g : RegularGraph N d) (T : Set (Fin N)) (j : T) :
    {v : T // v ≠ j} ↪ {v : Fin N // v ≠ j.val} where
  toFun v := ⟨v.val.val, fun he => v.property (Subtype.ext he)⟩
  inj' := fun _ _ h => Subtype.ext (Subtype.ext
    (congrArg (fun v : {v : Fin N // v ≠ j.val} => v.val) h))

def retainedPhysicalMinor (g : RegularGraph N d) (T : Set (Fin N)) (j : T) (z : ℂ) :
    Matrix {v : T // v ≠ j} {v : T // v ≠ j} ℂ :=
  ((g.deficient.deleteVertex j.val).G z).submatrix (g.retainedMinorEmbedding T j) (g.retainedMinorEmbedding T j)

def retainedMinorOutsideEquiv (_g : RegularGraph N d) (T : Set (Fin N)) (j : T) :
    (Tᶜ : Set (Fin N)) ≃ ({v : {v : Fin N // v ≠ j.val} | v.val ∈ T}ᶜ : Set {v : Fin N // v ≠ j.val}) where
  toFun v := ⟨⟨v.val, fun h => v.property (h ▸ j.property)⟩, v.property⟩
  invFun v := ⟨v.val.val, v.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The physical deleted row has exactly the retained inverse with its
deleted row and column removed; every inverse unit is derived. -/
theorem retainedPhysicalMinor_inverse (g : RegularGraph N d) (T : Set (Fin N)) (j : T)
    (z : ℂ) (hz : 0 < z.im) :
    IsUnit (g.retainedPhysicalMinor T j z) ∧
    (g.retainedPhysicalMinor T j z)⁻¹ =
      (((g.G z).submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N))⁻¹).submatrix
        (Subtype.val : {v : T // v ≠ j} → T) (Subtype.val : {v : T // v ≠ j} → T) := by
  let D := g.deficient.deleteVertex j.val
  let A : Set {v : Fin N // v ≠ j.val} := {v | v.val ∈ T}
  let e := (g.deficient.restrictDeleteVertexIso T j).toEquiv
  let ψ := g.retainedMinorOutsideEquiv T j
  let H := D.H
  have h := green_retained_principal_inverse A H (normalizedAdjacency_isHermitian _ _) z hz
  have hfull := (green_retained_principal_inverse T g.H (normalizedAdjacency_isHermitian _ _) z hz).2
  have hGreen : (green (H.submatrix (Subtype.val : (Aᶜ : Set _) → _) (Subtype.val : (Aᶜ : Set _) → _)) z).submatrix ψ ψ =
      (g.deficient.delete T).G z := by
    have hH : (H.submatrix (Subtype.val : (Aᶜ : Set _) → _) (Subtype.val : (Aᶜ : Set _) → _)).submatrix ψ ψ =
        (g.deficient.delete T).H := by
      ext x y
      rfl
    unfold green
    rw [← Matrix.inv_submatrix_equiv, ← spectralMatrix_principal _ z ψ ψ.injective, hH]
    rfl
  constructor
  · have hu := (Matrix.isUnit_submatrix_equiv e e).mpr h.1
    exact hu
  · have hh := congrArg (fun M : Matrix A A ℂ => M.submatrix e e) h.2
    dsimp only at hh
    rw [← Matrix.inv_submatrix_equiv] at hh
    simp only [Matrix.submatrix_sub, Pi.sub_apply] at hh
    rw [Matrix.submatrix_mul _ _ e ψ e ψ.bijective,
      Matrix.submatrix_mul _ _ e ψ ψ ψ.bijective, hGreen,
      ← spectralMatrix_principal _ z e e.injective] at hh
    have hdel : green (g.H.submatrix (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)
        (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)) z = (g.deficient.delete T).G z := by
      change green (g.deficient.H.submatrix (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)
        (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)) z = _
      rw [← g.deficient.H_delete T]
      rfl
    rw [hdel] at hfull
    have hf := congrArg (fun M : Matrix T T ℂ => M.submatrix
      (Subtype.val : {v : T // v ≠ j} → T) (Subtype.val : {v : T // v ≠ j} → T)) hfull
    dsimp only at hf
    simp only [Matrix.submatrix_sub, Pi.sub_apply] at hf
    rw [Matrix.submatrix_mul _ _ Subtype.val id Subtype.val Function.bijective_id,
      Matrix.submatrix_mul _ _ Subtype.val id id Function.bijective_id] at hf
    simp only [Matrix.submatrix_id_id] at hf
    rw [← spectralMatrix_principal _ z Subtype.val Subtype.val_injective] at hf
    exact hh.trans hf.symm

theorem truncatedMinorGreen_inverse (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (j : T) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    IsUnit (((g.deficient.restrict T).deleteVertex j).extensionGreen q z) ∧
    (((g.deficient.restrict T).deleteVertex j).extensionGreen q z)⁻¹ =
      (((g.deficient.restrict T).extensionGreen q z)⁻¹).submatrix
        (Subtype.val : {v : T // v ≠ j} → T) (Subtype.val : {v : T // v ≠ j} → T) := by
  let M := g.deficient.restrict T
  have hu := (M.deleteVertex j).extensionMatrix_isUnit hd q z hz hq
  have hu0 := M.extensionMatrix_isUnit hd q z hz hq
  constructor
  · exact Matrix.isUnit_nonsing_inv_iff.mpr hu
  · change (((M.deleteVertex j).extensionMatrix q z)⁻¹)⁻¹ = ((M.extensionMatrix q z)⁻¹)⁻¹.submatrix _ _
    rw [((M.deleteVertex j).extensionMatrix q z).nonsing_inv_nonsing_inv
      (((M.deleteVertex j).extensionMatrix q z).isUnit_iff_isUnit_det.mp hu),
      (M.extensionMatrix q z).nonsing_inv_nonsing_inv ((M.extensionMatrix q z).isUnit_iff_isUnit_det.mp hu0)]
    exact M.deleteVertex_extensionMatrix j q z

theorem truncated_minor_boundary_inverse_difference (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (j : T) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    (((g.deficient.restrict T).deleteVertex j).extensionGreen q z)⁻¹ - (g.retainedPhysicalMinor T j z)⁻¹ =
      (cutInnerCoupling g.graph d T).submatrix (Subtype.val : {v : T // v ≠ j} → T) id *
        g.truncatedBoundaryDefect T q z *
      ((cutInnerCoupling g.graph d T).submatrix (Subtype.val : {v : T // v ≠ j} → T) id).transpose := by
  rw [(g.truncatedMinorGreen_inverse hd T j q z hz hq).2, (g.retainedPhysicalMinor_inverse T j z hz).2]
  have h := congrArg (fun M : Matrix T T ℂ => M.submatrix
    (Subtype.val : {v : T // v ≠ j} → T) (Subtype.val : {v : T // v ≠ j} → T))
      (g.truncated_boundary_inverse_difference hd T q z hz hq)
  dsimp only at h
  rw [Matrix.submatrix_mul _ _ Subtype.val id Subtype.val Function.bijective_id,
    Matrix.submatrix_mul _ _ Subtype.val id id Function.bijective_id] at h
  exact h

theorem truncated_minor_boundary_retained_expansion (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (j : T) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let R := g.retainedPhysicalMinor T j z
    let P := ((g.deficient.restrict T).deleteVertex j).extensionGreen q z
    let U := (cutInnerCoupling g.graph d T).submatrix (Subtype.val : {v : T // v ≠ j} → T) id
    let D := g.truncatedBoundaryDefect T q z
    R - P = P * (U * D * U.transpose) * P + (R - P) * (U * D * U.transpose) * P := by
  dsimp only
  exact retained_difference_expansion _ _ _ (g.retainedPhysicalMinor_inverse T j z hz).1
    (g.truncatedMinorGreen_inverse hd T j q z hz hq).1 (g.truncated_minor_boundary_inverse_difference hd T j q z hz hq)

end RegularGraph
end LocalLaw
