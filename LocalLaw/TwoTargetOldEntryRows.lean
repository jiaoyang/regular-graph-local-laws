import LocalLaw.TwoTargetRowExtension

/-! A two-target inverse bound using old entry caps and new endpoint rows. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance twoTargetOldEntryRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V]

theorem inverse_supported_entry_of_new_row (A B : Matrix V V ℂ) (hA : IsUnit A) (hB : IsUnit B)
    (e : I ↪ V) (hsupport : ∀ u v, u ∉ Set.range e ∨ v ∉ Set.range e → (B-A) u v=0)
    (K b w : ℝ) (hK : 0≤K) (_hb : 0≤b) (hw : 0≤w) (x y : V)
    (hentry : ‖A⁻¹ x y‖≤K) (hold : ∀ i, ‖A⁻¹ (e i) y‖≤K)
    (hnew : ∑i,‖B⁻¹ x (e i)‖≤b)
    (hW : ∀i,∑j,‖(B-A) (e i) (e j)‖≤w) :
    ‖B⁻¹ x y‖≤K+b*w*K := by
  have hid : B⁻¹-A⁻¹=B⁻¹*(A-B)*A⁻¹ := by
    rw [Matrix.inv_sub_inv (show IsUnit B↔IsUnit A from ⟨fun _=>hA,fun _=>hB⟩)]
  have hs : ∀u v,u∉Set.range e∨v∉Set.range e→(A-B) u v=0 := by
    intro u v h
    rw [←neg_sub B A,Matrix.neg_apply,hsupport u v h,neg_zero]
  have hW' : ∀i,∑j,‖(A-B) (e i) (e j)‖≤w := by
    intro i
    simpa only [Matrix.sub_apply,norm_sub_rev] using hW i
  have herror : ‖B⁻¹ x y-A⁻¹ x y‖≤b*w*K := by
    have hh := congrArg (fun M:Matrix V V ℂ=>M x y) hid
    dsimp only at hh
    rw [Matrix.sub_apply,supported_middle_entry e _ _ _ hs] at hh
    rw [hh]
    calc
      _ ≤ ∑i,∑j,‖B⁻¹ x (e i)‖*(‖(A-B) (e i) (e j)‖*‖A⁻¹ (e j) y‖) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
        intro i _
        simpa only [norm_mul] using norm_sum_le Finset.univ
          (fun j:I=>B⁻¹ x (e i)*((A-B) (e i) (e j)*A⁻¹ (e j) y))
      _ ≤ ∑i,∑j,‖B⁻¹ x (e i)‖*(‖(A-B) (e i) (e j)‖*K) := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hold j) (norm_nonneg _)) (norm_nonneg _))
      _ = ∑i,‖B⁻¹ x (e i)‖*((∑j,‖(A-B) (e i) (e j)‖)*K) := by simp only [Finset.mul_sum,Finset.sum_mul]
      _ ≤ ∑i,‖B⁻¹ x (e i)‖*(w*K) := Finset.sum_le_sum (fun i _=>
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hW' i) hK) (norm_nonneg _))
      _ = (∑i,‖B⁻¹ x (e i)‖)*(w*K) := (Finset.sum_mul ..).symm
      _ ≤ b*(w*K) := mul_le_mul_of_nonneg_right hnew (mul_nonneg hw hK)
      _ = _ := by ring
  have hh := norm_sub_le_norm_sub_add_norm_sub (B⁻¹ x y) (A⁻¹ x y) 0
  simp only [sub_zero] at hh
  exact (hh.trans (add_le_add herror hentry)).trans_eq (by ring)

theorem inverse_supported_two_target_rows_of_old_entries
    (A B : Matrix V V ℂ) (hA : IsUnit A) (hB : IsUnit B)
    (e : I ↪ V) (hsupport : ∀u v,u∉Set.range e∨v∉Set.range e→(B-A) u v=0)
    (x y : V) (K C b w : ℝ) (hK : 0≤K) (hC : 0≤C) (hb : 0≤b) (hw : 0≤w)
    (hsym : B⁻¹.IsSymm) (hOldEntry : ∀u v,‖A⁻¹ u v‖≤K)
    (hNewEndpoint : ∀i,∑j,‖B⁻¹ (e i) (e j)‖≤C)
    (hNewTarget : ∀s,s=x∨s=y→∑i,‖B⁻¹ s (e i)‖≤b)
    (hW : ∀i,∑j,‖(B-A) (e i) (e j)‖≤w) :
    ∀v:twoTargetIndexSet e x y,∑u:twoTargetIndexSet e x y,‖B⁻¹ v.val u.val‖≤C+3*b+2*(K+b*w*K) := by
  refine two_target_row_extension e x y B⁻¹ hsym C b (K+b*w*K) hC hb (by positivity)
    hNewEndpoint hNewTarget ?_
  intro s hs t _
  exact inverse_supported_entry_of_new_row A B hA hB e hsupport K b w hK hb hw s t
    (hOldEntry s t) (fun i=>hOldEntry (e i) t) (hNewTarget s hs) hW
end LocalLaw
