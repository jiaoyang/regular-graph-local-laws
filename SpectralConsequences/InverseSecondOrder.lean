import LocalLaw.DeletionStability

/-! # Second-order inverse remainder for the two-pivot mean expansion

The linear inverse term is kept explicitly. The quadratic remainder is proved
from the genuine inverse identity and the existing entrywise stability theorem.
-/
open scoped BigOperators
namespace SpectralConsequences
open LocalLaw
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem inverse_first_order_remainder (U P : Matrix I I ℂ)
    (hU : IsUnit U) (hP : IsUnit P) (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hrow : ∀ i, ∑ j, ‖P⁻¹ i j‖ ≤ C)
    (hcol : ∀ j, ∑ i, ‖P⁻¹ i j‖ ≤ C)
    (hentry : ∀ i j, ‖(U-P) i j‖ ≤ δ)
    (hsmall : (Fintype.card I:ℝ)*C*δ ≤ 1/2) (i j : I) :
    ‖((U⁻¹-P⁻¹)+P⁻¹*(U-P)*P⁻¹) i j‖ ≤
      2*(Fintype.card I:ℝ)*C^3*δ^2 := by
  have heq : P+(U-P)=U := by abel
  have hid := inverse_perturbation_identity P (U-P) hP
    (show IsUnit (P+(U-P)) by rw [heq];exact hU)
  rw [heq] at hid
  have hX := inverse_entry_stability_pair U P hU hP C δ hC hδ hrow hcol hentry hsmall
  have hWrow (k : I) : ∑ l, ‖(U-P) k l‖ ≤ (Fintype.card I:ℝ)*δ := by
    calc
      _ ≤ ∑ _l : I, δ := Finset.sum_le_sum (fun l _ => hentry k l)
      _ = _ := by simp [nsmul_eq_mul]
  have hWX (k l : I) : ‖((U-P)*(U⁻¹-P⁻¹)) k l‖ ≤
      (Fintype.card I:ℝ)*δ*(2*C^2*δ) :=
    matrix_mul_entry_bound_of_row _ _ k l _ _ (by positivity) (hWrow k) (fun m => hX m l)
  have hprod : ‖(P⁻¹*(U-P)*(U⁻¹-P⁻¹)) i j‖ ≤
      C*((Fintype.card I:ℝ)*δ*(2*C^2*δ)) := by
    rw [Matrix.mul_assoc]
    exact matrix_mul_entry_bound_of_row _ _ i j _ _ (by positivity) (hrow i) (fun k => hWX k j)
  have hrem : (U⁻¹-P⁻¹)+P⁻¹*(U-P)*P⁻¹ =
      -(P⁻¹*(U-P)*(U⁻¹-P⁻¹)) := by
    apply eq_neg_iff_add_eq_zero.mpr
    calc
      _ = (U⁻¹-P⁻¹)+P⁻¹*(U-P)*(U⁻¹-P⁻¹)+P⁻¹*(U-P)*P⁻¹ := by abel
      _ = 0 := hid
  rw [hrem,Matrix.neg_apply,norm_neg]
  convert hprod using 1
  ring

end SpectralConsequences
