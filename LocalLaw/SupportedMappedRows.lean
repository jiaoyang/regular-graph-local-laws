import LocalLaw.AugmentedRowTransfer

/-! Supported inverse surgery controls rows on any finite target family. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
variable {V I J : Type} [Fintype V] [Fintype I] [Fintype J] [DecidableEq V]

theorem inverse_supported_mapped_row_sum (A B : Matrix V V ℂ) (hA : IsUnit A) (hB : IsUnit B)
    (e : I ↪ V) (f : J → V)
    (hsupport : ∀ u v, u ∉ Set.range e ∨ v ∉ Set.range e → (B-A) u v=0)
    (a b w : ℝ) (ha : 0≤a) (_hb : 0≤b) (hw : 0≤w) (x : V)
    (hOld : ∀u, ∑j, ‖A⁻¹ u (f j)‖≤a)
    (hNew : ∑i, ‖B⁻¹ x (e i)‖≤b)
    (hW : ∀i, ∑k, ‖(B-A) (e i) (e k)‖≤w) :
    ∑j, ‖B⁻¹ x (f j)‖≤a+b*w*a := by
  have hid : B⁻¹-A⁻¹=B⁻¹*(A-B)*A⁻¹ := by
    rw [Matrix.inv_sub_inv (show IsUnit B↔IsUnit A from ⟨fun _=>hA,fun _=>hB⟩)]
  have hs : ∀u v,u∉Set.range e∨v∉Set.range e→(A-B) u v=0 := by
    intro u v h
    rw [←neg_sub B A,Matrix.neg_apply,hsupport u v h,neg_zero]
  have hW' : ∀i,∑k,‖(A-B) (e i) (e k)‖≤w := by
    intro i
    simpa only [Matrix.sub_apply,norm_sub_rev] using hW i
  have herror (j:J) : ‖B⁻¹ x (f j)-A⁻¹ x (f j)‖≤
      ∑i,∑k,‖B⁻¹ x (e i)‖*(‖(A-B) (e i) (e k)‖*‖A⁻¹ (e k) (f j)‖) := by
    have hh:=congrArg (fun M:Matrix V V ℂ=>M x (f j)) hid
    dsimp only at hh
    rw [Matrix.sub_apply,supported_middle_entry e _ _ _ hs] at hh
    rw [hh]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro i _
    simpa only [norm_mul] using norm_sum_le Finset.univ
      (fun k:I=>B⁻¹ x (e i)*((A-B) (e i) (e k)*A⁻¹ (e k) (f j)))
  have htotal : (∑j,‖B⁻¹ x (f j)-A⁻¹ x (f j)‖)≤b*w*a := by
    calc
      _≤∑j,∑i,∑k,‖B⁻¹ x (e i)‖*(‖(A-B) (e i) (e k)‖*‖A⁻¹ (e k) (f j)‖) :=
        Finset.sum_le_sum (fun j _=>herror j)
      _=∑i,∑k,‖B⁻¹ x (e i)‖*(‖(A-B) (e i) (e k)‖*(∑j,‖A⁻¹ (e k) (f j)‖)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _≤∑i,∑k,‖B⁻¹ x (e i)‖*(‖(A-B) (e i) (e k)‖*a) :=
        Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun k _=>
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hOld (e k)) (norm_nonneg _)) (norm_nonneg _)))
      _=∑i,‖B⁻¹ x (e i)‖*((∑k,‖(A-B) (e i) (e k)‖)*a) := by
        simp only [Finset.mul_sum,Finset.sum_mul]
      _≤∑i,‖B⁻¹ x (e i)‖*(w*a) := Finset.sum_le_sum (fun i _=>
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hW' i) ha) (norm_nonneg _))
      _=(∑i,‖B⁻¹ x (e i)‖)*(w*a) := (Finset.sum_mul ..).symm
      _≤b*(w*a) := mul_le_mul_of_nonneg_right hNew (mul_nonneg hw ha)
      _=_ := by ring
  calc
    _≤∑j,(‖A⁻¹ x (f j)‖+‖B⁻¹ x (f j)-A⁻¹ x (f j)‖) := by
      apply Finset.sum_le_sum
      intro j _
      have h:=norm_sub_le_norm_sub_add_norm_sub (B⁻¹ x (f j)) (A⁻¹ x (f j)) 0
      simpa only [sub_zero,add_comm] using h
    _=(∑j,‖A⁻¹ x (f j)‖)+∑j,‖B⁻¹ x (f j)-A⁻¹ x (f j)‖ := Finset.sum_add_distrib
    _≤_ := add_le_add (hOld x) htotal

end LocalLaw
