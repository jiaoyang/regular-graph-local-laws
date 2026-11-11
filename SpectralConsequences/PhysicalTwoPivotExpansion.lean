import SpectralConsequences.TwoPivotQuadraticAlgebra
import LocalLaw.PrincipalDeletion

/-! # The quadratic expansion for an actual two-vertex-deleted resolvent

Every inverse unit and the Schur identity are derived from the Hermitian
upper-half-plane resolvent. Only primitive entrywise approximation bounds
remain as finite analytic inputs to this reusable theorem.
-/
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1400000
namespace SpectralConsequences
open LocalLaw
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Exact physical deletion expressed in any injective two-vertex labeling. -/
theorem physical_two_pivot_formula (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (S : Set V) [DecidablePred (fun v => v∈S)] (φ : Fin 2 ≃ S)
    (z : ℂ) (hz : 0 < z.im) (x y : (Sᶜ : Set V)) :
    green (H.submatrix (Subtype.val : (Sᶜ : Set V) → V)
      (Subtype.val : (Sᶜ : Set V) → V)) z x y =
      green H z x.val y.val-
        twoPivotSchur ((green H z).submatrix (fun i => (φ i).val) (fun i => (φ i).val))
          (fun i => green H z x.val (φ i).val) (fun j => green H z (φ j).val y.val) := by
  let P := (green H z).submatrix (Subtype.val : S → V) (Subtype.val : S → V)
  let U := (green H z).submatrix (fun i => (φ i).val) (fun i => (φ i).val)
  have hU : U = P.submatrix φ φ := by ext i j;rfl
  have hi : U⁻¹ = P⁻¹.submatrix φ φ := by rw [hU,Matrix.inv_submatrix_equiv]
  have hs : twoPivotSchur U (fun i => green H z x.val (φ i).val)
      (fun j => green H z (φ j).val y.val) =
      ∑ i:S,∑ j:S,green H z x.val i.val*P⁻¹ i j*green H z j.val y.val := by
    unfold twoPivotSchur
    rw [hi]
    simp only [Matrix.submatrix_apply]
    calc
      _ = ∑ i:S,∑ j:Fin 2,green H z x.val i.val*P⁻¹ i (φ j)*green H z (φ j).val y.val := by
        apply Fintype.sum_equiv φ
        intro _
        rfl
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        exact φ.sum_comp (fun j:S => green H z x.val i.val*P⁻¹ i j*green H z j.val y.val)
  have hh := congrArg (fun A : Matrix (Sᶜ : Set V) (Sᶜ : Set V) ℂ => A x y)
    (green_deleted_principal S H hH z hz)
  dsimp only at hh
  simp only [Matrix.sub_apply,Matrix.mul_apply,Matrix.submatrix_apply,Finset.sum_mul] at hh
  rw [Finset.sum_comm] at hh
  change _ = green H z x.val y.val-twoPivotSchur U _ _
  rw [hs]
  exact hh

/-- Literal version of (7.24), with a q-dependent deterministic coefficient. -/
theorem physical_two_pivot_quadratic_expansion (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (S : Set V) [DecidablePred (fun v => v∈S)] (φ : Fin 2 ≃ S)
    (z : ℂ) (hz : 0 < z.im) (x y : (Sᶜ : Set V)) (t a : ℂ) (ht : t≠0)
    (C P δ : ℝ) (hC : 1≤C) (hP : 1≤P) (hδ : 0≤δ) (hδone : δ≤1)
    (htnorm : ‖t‖≤C) (htinv : ‖t⁻¹‖≤P) (hanorm : ‖a‖≤1)
    (hl : ∀i:Fin 2,‖green H z x.val (φ i).val‖≤C)
    (hr : ∀j:Fin 2,‖green H z (φ j).val y.val‖≤C)
    (hl0 : ‖green H z x.val (φ 0).val+a*t‖≤δ)
    (hr1 : ‖green H z (φ 1).val y.val+a*t‖≤δ)
    (hl1 : ‖green H z x.val (φ 1).val‖≤δ)
    (hr0 : ‖green H z (φ 0).val y.val‖≤δ)
    (hdiag : ∀i:Fin 2,‖green H z (φ i).val (φ i).val-t‖≤δ)
    (hoff : ∀i j:Fin 2,i≠j→‖green H z (φ i).val (φ j).val‖≤δ)
    (hsmall : 2*P*δ≤1/2) :
    ‖green (H.submatrix (Subtype.val : (Sᶜ : Set V) → V)
      (Subtype.val : (Sᶜ : Set V) → V)) z x y-
      (green H z x.val y.val+a*green H z (φ 0).val y.val+
        a*green H z x.val (φ 1).val+a^2*green H z (φ 0).val (φ 1).val)‖≤
      (2*P+(4*C+1)*P^2+16*C^2*P^3)*δ^2 := by
  let U := (green H z).submatrix (fun i => (φ i).val) (fun i => (φ i).val)
  let PP := (green H z).submatrix (Subtype.val : S → V) (Subtype.val : S → V)
  have hPi : IsUnit PP := (green_retained_principal_inverse S H hH z hz).1
  have hUeq : U = PP.submatrix φ φ := by ext i j;rfl
  have hUi : IsUnit U := by
    rw [hUeq]
    exact (Matrix.isUnit_submatrix_equiv φ φ).mpr hPi
  have hh := twoPivot_quadratic_expansion U hUi
    (fun i => green H z x.val (φ i).val) (fun j => green H z (φ j).val y.val)
    t a ht C P δ hC hP hδ hδone htnorm htinv hanorm hl hr hl0 hr1 hl1 hr0 hdiag hoff hsmall
  rw [physical_two_pivot_formula H hH S φ z hz x y]
  have heq : green H z x.val y.val-twoPivotSchur U
      (fun i => green H z x.val (φ i).val) (fun j => green H z (φ j).val y.val)-
      (green H z x.val y.val+a*green H z (φ 0).val y.val+
        a*green H z x.val (φ 1).val+a^2*green H z (φ 0).val (φ 1).val) =
      -(twoPivotSchur U (fun i => green H z x.val (φ i).val)
        (fun j => green H z (φ j).val y.val)+a*green H z (φ 0).val y.val+
          a*green H z x.val (φ 1).val+a^2*U 0 1) := by
    dsimp only [U,Matrix.submatrix_apply]
    ring
  rw [heq,norm_neg]
  exact hh

end SpectralConsequences
