import LocalLaw.LocalizationIdentity
import LocalLaw.EmbeddedDeletionComparison

/-!
# Exact retained-Green expansion for the source local improvement

The ambient Hermitian graph and the local boundary model may have different
vertex sets. Their actual deleted resolvents determine the self-energy error.
The retained Green difference is expanded into the leading model sandwich and
a genuine nonlinear remainder, as in source (5.85)/(6.24).
-/

set_option maxHeartbeats 300000

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance boundarySchurExpansionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Algebra
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem inverse_difference_from_inverse_difference (R P : Matrix I I ℂ)
    (hR : IsUnit R) (hP : IsUnit P) :
    R - P = R * (P⁻¹ - R⁻¹) * P := by
  have hRR := Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det R).mp hR)
  have hPP := Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP)
  rw [mul_sub, sub_mul, Matrix.mul_assoc, hPP, Matrix.mul_one, hRR, Matrix.one_mul]

/-- The nonlinear remainder is an exact consequence of inverse algebra. -/
theorem retained_difference_expansion (R P W : Matrix I I ℂ)
    (hR : IsUnit R) (hP : IsUnit P) (hW : P⁻¹ - R⁻¹ = W) :
    R - P = P * W * P + (R - P) * W * P := by
  have hidentity := inverse_difference_from_inverse_difference R P hR hP
  rw [hW] at hidentity
  calc
    _ = R * W * P := hidentity
    _ = (P + (R - P)) * W * P := by rw [add_sub_cancel]
    _ = _ := by rw [add_mul, add_mul]

end Algebra

section EmbeddedSchur
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

/-- The literal ambient outside block after deleting the embedded retained set. -/
def embeddedSelfEnergy (H : Matrix A A ℂ) (e : V ↪ A) (T : Set V) (z : ℂ) : Matrix T T ℂ :=
  H.submatrix (fun x : T => e x.val) (Subtype.val : ((e '' T)ᶜ : Set A) → A) *
    green (H.submatrix (Subtype.val : ((e '' T)ᶜ : Set A) → A)
      (Subtype.val : ((e '' T)ᶜ : Set A) → A)) z *
    H.submatrix (Subtype.val : ((e '' T)ᶜ : Set A) → A) (fun x : T => e x.val)

/-- The Schur complement of the actual ambient resolvent, reindexed only
on the retained finite set. -/
theorem embedded_green_retained_schur (H : Matrix A A ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (e : V ↪ A) (T : Set V) :
    (((green H z).submatrix e e).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ =
      spectralMatrix (H.submatrix (fun x : T => e x.val) (fun x : T => e x.val)) z -
        embeddedSelfEnergy H e T z := by
  let U := e '' T
  letI : DecidablePred (fun a => a ∈ U) := fun _ => Classical.propDecidable _
  letI : Fintype U := Subtype.fintype _
  letI : Fintype (Uᶜ : Set A) := Subtype.fintype _
  let φ := Equiv.Set.image (e : V → A) T e.injective
  have hh := (green_retained_principal_inverse U H hH z hz).2
  have hInv := congrArg (fun M : Matrix U U ℂ => M.submatrix φ φ) hh
  dsimp only at hInv
  simp only [Matrix.submatrix_sub, Pi.sub_apply] at hInv
  rw [Matrix.submatrix_mul _ _ φ id φ Function.bijective_id,
    Matrix.submatrix_mul _ _ φ id id Function.bijective_id] at hInv
  have hmatrix : ((green H z).submatrix e e).submatrix (Subtype.val : T → V) (Subtype.val : T → V) =
      ((green H z).submatrix (Subtype.val : U → A) (Subtype.val : U → A)).submatrix φ φ := by
    ext i j
    rfl
  have hret : (((green H z).submatrix e e).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ =
      (((green H z).submatrix (Subtype.val : U → A) (Subtype.val : U → A))⁻¹).submatrix φ φ := by
    rw [hmatrix, Matrix.inv_submatrix_equiv]
  rw [hret, hInv]
  congr 1
  exact (spectralMatrix_principal (H.submatrix (Subtype.val : U → A) (Subtype.val : U → A))
    z φ φ.injective).symm

end EmbeddedSchur

namespace DeficientGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

/-- The literal deleted-model self energy on the retained set. -/
def retainedSelfEnergy (g : DeficientGraph V d) (T : Set V) (q z : ℂ) : Matrix T T ℂ :=
  g.H.submatrix (Subtype.val : T → V) (Subtype.val : (Tᶜ : Set V) → V) *
    (g.delete T).extensionGreen q z *
    g.H.submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V)

/-- The genuine model retained inverse has its exact diagonal boundary
charge and deleted resolvent; every inverse is justified by upper half-plane
conditions. -/
theorem retained_extensionGreen_schur (g : DeficientGraph V d) (hd : 3 ≤ d)
    (T : Set V) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    ((g.extensionGreen q z).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ =
      spectralMatrix (g.H.submatrix (Subtype.val : T → V) (Subtype.val : T → V)) z -
        q • (g.boundaryDiagonal.submatrix (Subtype.val : T → V) (Subtype.val : T → V)) -
        g.retainedSelfEnergy T q z := by
  have hD := (g.delete T).extensionMatrix_isUnit hd q z hz hq
  rw [g.extensionMatrix_delete] at hD
  have hh := retained_principal_inverse T (g.extensionMatrix q z) (g.extensionMatrix_isUnit hd q z hz hq) hD
  rw [g.extensionMatrix_cross12 T q z, g.extensionMatrix_cross21 T q z,
    ← g.extensionMatrix_delete] at hh
  change _ = (g.extensionMatrix q z).submatrix (Subtype.val : T → V) (Subtype.val : T → V) -
    g.retainedSelfEnergy T q z at hh
  change ((g.extensionMatrix q z)⁻¹.submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ = _
  rw [hh]
  congr 1
  rw [spectralMatrix_principal g.H z Subtype.val Subtype.val_injective]
  rfl

/-- The actual error driving source (5.85). It includes the boundary charge
on retained vertices, which vanishes in a neighborhood containing every
incident edge of the retained set. -/
def embeddedRetainedError {A : Type*} [Fintype A] [DecidableEq A]
    (g : DeficientGraph V d) (H : Matrix A A ℂ) (e : V ↪ A) (T : Set V) (q z : ℂ) : Matrix T T ℂ :=
  embeddedSelfEnergy H e T z -
    q • (g.boundaryDiagonal.submatrix (Subtype.val : T → V) (Subtype.val : T → V)) -
    g.retainedSelfEnergy T q z

/-- Exact different-size physical/model row expansion. No full Green entry,
deleted comparison, desired row error, or inverse-unit assumption is supplied. -/
theorem embedded_retained_expansion {A : Type*} [Fintype A] [DecidableEq A]
    (g : DeficientGraph V d) (hd : 3 ≤ d) (H : Matrix A A ℂ) (hH : H.IsHermitian)
    (e : V ↪ A) (hHmodel : g.H = H.submatrix e e) (T : Set V)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let R := ((green H z).submatrix e e).submatrix (Subtype.val : T → V) (Subtype.val : T → V)
    let P := (g.extensionGreen q z).submatrix (Subtype.val : T → V) (Subtype.val : T → V)
    let W := g.embeddedRetainedError H e T q z
    R - P = P * W * P + (R - P) * W * P := by
  dsimp only
  have hR := embedded_green_retained_isUnit H hH z hz e T
  have hD := (g.delete T).extensionMatrix_isUnit hd q z hz hq
  rw [g.extensionMatrix_delete] at hD
  have hP := retained_principal_inverse_isUnit T (g.extensionMatrix q z)
    (g.extensionMatrix_isUnit hd q z hz hq) hD
  apply retained_difference_expansion _ _ _ hR hP
  change ((g.extensionGreen q z).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ - _ = _
  rw [g.retained_extensionGreen_schur hd T q z hz hq, embedded_green_retained_schur H hH z hz e T]
  rw [hHmodel]
  change (spectralMatrix (H.submatrix (fun x : T => e x.val) (fun x : T => e x.val)) z - _ - _) - (_ - _) = _
  unfold embeddedRetainedError
  abel

end DeficientGraph
end LocalLaw
