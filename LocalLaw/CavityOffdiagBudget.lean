import LocalLaw.BoundaryOffdiagStrongParameters
import LocalLaw.BoundaryMaxProfile
import LocalLaw.BoundaryDefectAggregation

/-! # Strong cavity off-diagonal forcing with two decaying root factors -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance cavityOffdiagBudgetDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem sparse_cavity_offdiag_budget {I F : Type*} [Fintype F]
    (P : Matrix I I ℂ) (hsym : P.IsSymm) (l : F → I) (root : I)
    (a : ℕ) (L Uprofile M0 W0 : ℝ)
    (profile : BoundaryMaxProfile P l root a L Uprofile M0 W0)
    (Dmat : Matrix F F ℂ) (bad : Finset F)
    (ε n δ φ γ U V D0 G C0 : ℝ)
    (ha : 12 ≤ a) (hL : 1 ≤ L) (hε : 0 ≤ ε) (hn : 0 ≤ n) (hδ : 0 ≤ δ)
    (hφ : 0 ≤ φ) (hγ : 0 ≤ γ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hD0 : 0 ≤ D0)
    (hG : 0 ≤ G) (hC0 : 0 ≤ C0) (hW0 : 0 ≤ W0)
    (hcap : ε * L ^ (4 * a) ≤ 1) (hcount : n ≤ U * L ^ (2 * a))
    (hlabels : (Fintype.card F : ℝ) ≤ n) (hbad : (bad.card : ℝ) ≤ V * L ^ 2)
    (herror : δ ≤ D0 * L ^ 3 * ε) (hcorr : φ * L ^ (4 * a) ≤ ε)
    (hgoodError : γ ≤ G * (δ ^ 2 + n * φ * δ + φ))
    (hglobal : ∀ α β, ‖Dmat α β‖ ≤ δ)
    (hpattern : ∀ α β, α ≠ β → (α ∉ bad ∨ β ∉ bad) → ‖Dmat α β‖ ≤ γ)
    (hroot : ∀ α, ‖P root (l α)‖ ≤ C0 / L ^ 9)
    (hlarge1 : 3 * G * U * W0 * D0 ^ 2 ≤ L)
    (hlarge2 : 3 * G * U ^ 2 * W0 * D0 ≤ L)
    (hlarge3 : 3 * G * U * W0 ≤ L) :
    ‖∑ α, ∑ β, if α = β then 0 else P root (l α) * Dmat α β * P (l β) root‖ ≤
      (D0 * V ^ 2 * C0 ^ 2 + 1) * (ε / L ^ 4) := by
  have hLp : 0 < L := by linarith
  have hL0 := hLp.le
  let A := fun α => P root (l α)
  let B := fun β => P (l β) root
  have hbase := sparse_boundary_defect_weighted_offdiag Dmat bad A B δ γ hδ hγ hglobal hpattern
  have hbadA : (∑ α ∈ bad, ‖A α‖) ≤ (V * L ^ 2) * (C0 / L ^ 9) := by
    calc
      _ ≤ ∑ _α ∈ bad, C0 / L ^ 9 := Finset.sum_le_sum (fun α _ => hroot α)
      _ = (bad.card : ℝ) * (C0 / L ^ 9) := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hbad (by positivity)
  have hbadB : (∑ β ∈ bad, ‖B β‖) ≤ (V * L ^ 2) * (C0 / L ^ 9) := by
    calc
      _ ≤ ∑ _β ∈ bad, C0 / L ^ 9 := Finset.sum_le_sum (fun β _ => by
        change ‖P (l β) root‖ ≤ _
        rw [hsym.apply]
        exact hroot β)
      _ = (bad.card : ℝ) * (C0 / L ^ 9) := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hbad (by positivity)
  have hbadTerm : δ * (∑ α ∈ bad, ‖A α‖) * (∑ β ∈ bad, ‖B β‖) ≤
      (D0 * V ^ 2 * C0 ^ 2) * (ε / L ^ 4) := by
    calc
      _ ≤ (D0 * L ^ 3 * ε) * ((V * L ^ 2) * (C0 / L ^ 9)) * ((V * L ^ 2) * (C0 / L ^ 9)) := by
        gcongr
      _ = (D0 * V ^ 2 * C0 ^ 2) * (ε / L ^ 11) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hε (pow_pos hLp 4) (pow_le_pow_right₀ hL (by omega))) (by positivity)
  have hA : (∑ α, ‖A α‖) ≤ profile.S := by
    have heq : (∑ α, ‖A α‖) = ∑ α, ‖P (l α) root‖ := by
      apply Finset.sum_congr rfl
      intro α _
      exact congrArg norm (hsym.apply (l α) root)
    rw [heq]
    exact profile.column_bound root
  have hB : (∑ β, ‖B β‖) ≤ profile.S := profile.column_bound root
  have hweights : (∑ α, ‖A α‖) * (∑ β, ‖B β‖) ≤ n * W0 * L := by
    calc
      _ ≤ profile.S * profile.S := mul_le_mul hA hB (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) profile.column_nonnegative
      _ = profile.S ^ 2 := (pow_two _).symm
      _ ≤ (Fintype.card F : ℝ) * profile.W := profile.column_square
      _ ≤ n * (W0 * L) := mul_le_mul hlabels profile.row_log profile.square_nonnegative (by positivity)
      _ = _ := by ring
  have hgoodTerm : γ * (∑ α, ‖A α‖) * (∑ β, ‖B β‖) ≤ ε / L ^ 4 := by
    calc
      _ = γ * ((∑ α, ‖A α‖) * (∑ β, ‖B β‖)) := by ring
      _ ≤ γ * (n * W0 * L) := mul_le_mul_of_nonneg_left hweights hγ
      _ ≤ (G * (δ ^ 2 + n * φ * δ + φ)) * (n * W0 * L) :=
        mul_le_mul_of_nonneg_right hgoodError (by positivity)
      _ ≤ _ := paired_weighted_good_strong_absorption a L ε n δ φ U D0 G W0 ha hL hε hn hδ hφ
        hU hD0 hG hW0 hcap hcount herror hcorr hlarge1 hlarge2 hlarge3
  exact hbase.trans ((add_le_add hbadTerm hgoodTerm).trans_eq (by ring))

end LocalLaw
