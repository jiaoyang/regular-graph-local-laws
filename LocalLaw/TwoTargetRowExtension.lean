import LocalLaw.AugmentedRowTransfer

/-!
# Extending finite endpoint rows by two genuine target vertices

The target-target entries follow from the actual inverse identity and old
and new endpoint rows. A surjective finite index map handles coincidences
between either target and the original endpoints without double-counting.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance twoTargetRowExtensionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem finite_nonnegative_sum_le_of_surjective {I J : Type} [Fintype I] [Fintype J]
    (f : J → I) (hf : Function.Surjective f) (F : I → ℝ) (hF : ∀ i, 0 ≤ F i) :
    (∑ i, F i) ≤ ∑ j, F (f j) := by
  let g : I → J := fun i => Classical.choose (hf i)
  have hg (i : I) : f (g i) = i := Classical.choose_spec (hf i)
  have hgi : Function.Injective g := by
    intro i j h
    have hh := congrArg f h
    simpa only [hg] using hh
  calc
    _ = ∑ i, F (f (g i)) := Finset.sum_congr rfl (fun i _ => (congrArg F (hg i)).symm)
    _ = ∑ j ∈ Finset.univ.image g, F (f j) := by
      rw [Finset.sum_image]
      intro i _ j _ hij
      exact hgi hij
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hF (f j))

section Inverses
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V]

theorem inverse_supported_target_entry_bound (A B : Matrix V V ℂ) (hA : IsUnit A) (hB : IsUnit B)
    (e : I ↪ V)
    (hsupport : ∀ u v, u ∉ Set.range e ∨ v ∉ Set.range e → (B - A) u v = 0)
    (K a b w : ℝ) (_hK : 0 ≤ K) (_ha : 0 ≤ a) (hb : 0 ≤ b) (hw : 0 ≤ w) (x y : V)
    (hentry : ‖A⁻¹ x y‖ ≤ K) (hleft : ∑ i, ‖A⁻¹ x (e i)‖ ≤ a)
    (hright : ∀ i, ‖B⁻¹ (e i) y‖ ≤ b)
    (hW : ∀ i, ∑ j, ‖(B - A) (e i) (e j)‖ ≤ w) :
    ‖B⁻¹ x y‖ ≤ K + a * w * b := by
  have hdiff : A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
    rw [Matrix.inv_sub_inv (show IsUnit A ↔ IsUnit B from ⟨fun _ => hB, fun _ => hA⟩)]
  have hid := congrArg (fun M : Matrix V V ℂ => M x y) hdiff
  dsimp only at hid
  rw [Matrix.sub_apply, supported_middle_entry e _ _ _ hsupport] at hid
  have hinner (i : I) : (∑ j, ‖(B - A) (e i) (e j)‖ * ‖B⁻¹ (e j) y‖) ≤ w * b := by
    calc
      _ ≤ ∑ j, ‖(B - A) (e i) (e j)‖ * b :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hright j) (norm_nonneg _))
      _ = (∑ j, ‖(B - A) (e i) (e j)‖) * b := (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hW i) hb
  have herror : ‖A⁻¹ x y - B⁻¹ x y‖ ≤ a * w * b := by
    rw [hid]
    calc
      _ ≤ ∑ i, ‖∑ j, A⁻¹ x (e i) * ((B - A) (e i) (e j) * B⁻¹ (e j) y)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖A⁻¹ x (e i)‖ * (‖(B - A) (e i) (e j)‖ * ‖B⁻¹ (e j) y‖) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [norm_mul] using (norm_sum_le Finset.univ
          (fun j : I => A⁻¹ x (e i) * ((B - A) (e i) (e j) * B⁻¹ (e j) y)))
      _ = ∑ i, ‖A⁻¹ x (e i)‖ * (∑ j, ‖(B - A) (e i) (e j)‖ * ‖B⁻¹ (e j) y‖) := by
        simp only [Finset.mul_sum]
      _ ≤ ∑ i, ‖A⁻¹ x (e i)‖ * (w * b) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hinner i) (norm_nonneg _))
      _ = (∑ i, ‖A⁻¹ x (e i)‖) * (w * b) := (Finset.sum_mul ..).symm
      _ ≤ a * (w * b) := mul_le_mul_of_nonneg_right hleft (mul_nonneg hw hb)
      _ = _ := by ring
  have hh := norm_sub_le_norm_sub_add_norm_sub (B⁻¹ x y) (A⁻¹ x y) 0
  simp only [sub_zero] at hh
  exact (hh.trans (add_le_add (by simpa only [norm_sub_rev] using herror) hentry)).trans_eq (by ring)

end Inverses

section Rows
variable {V I : Type} [Fintype V] [Fintype I]

def twoTargetIndexSet (e : I ↪ V) (x y : V) : Set V := Set.range e ∪ {x, y}

theorem two_target_index_card (e : I ↪ V) (x y : V) :
    Nat.card (twoTargetIndexSet e x y) ≤ Fintype.card I + 2 := by
  let f : I ⊕ Fin 2 → twoTargetIndexSet e x y :=
    Sum.elim (fun i => ⟨e i, Or.inl ⟨i, rfl⟩⟩)
      (fun j => if j = 0 then ⟨x, Or.inr (Or.inl rfl)⟩ else ⟨y, Or.inr (Or.inr rfl)⟩)
  have hf : Function.Surjective f := by
    rintro ⟨v, hv⟩
    rcases hv with ⟨i, rfl⟩ | (rfl | rfl)
    · exact ⟨Sum.inl i, rfl⟩
    · exact ⟨Sum.inr 0, by simp [f]⟩
    · exact ⟨Sum.inr 1, by simp [f]⟩
  have hh := Nat.card_le_card_of_surjective f hf
  simpa only [Nat.card_sum, Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin] using hh

theorem two_target_row_extension (e : I ↪ V) (x y : V) (Q : Matrix V V ℂ) (hsym : Q.IsSymm)
    (C a B : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hendpoint : ∀ i, ∑ j, ‖Q (e i) (e j)‖ ≤ C)
    (htarget : ∀ t, t = x ∨ t = y → ∑ j, ‖Q t (e j)‖ ≤ a)
    (hentry : ∀ s, s = x ∨ s = y → ∀ t, t = x ∨ t = y → ‖Q s t‖ ≤ B) :
    ∀ v : twoTargetIndexSet e x y,
      ∑ u : twoTargetIndexSet e x y, ‖Q v.val u.val‖ ≤ C + 3 * a + 2 * B := by
  intro v
  have hrootrow : (∑ j, ‖Q v.val (e j)‖) ≤ C + a := by
    rcases v.property with ⟨i, hi⟩ | hv
    · rw [← hi]
      exact (hendpoint i).trans (le_add_of_nonneg_right ha)
    · exact (htarget v.val hv).trans (le_add_of_nonneg_left hC)
  have htargetpoint (t : V) (ht : t = x ∨ t = y) : ‖Q v.val t‖ ≤ a + B := by
    rcases v.property with ⟨i, hi⟩ | hv
    · rw [← hi, hsym.apply]
      have hh := Finset.single_le_sum (fun j _ => norm_nonneg (Q t (e j))) (Finset.mem_univ i)
      exact (hh.trans (htarget t ht)).trans (le_add_of_nonneg_right hB)
    · exact (hentry v.val hv t ht).trans (le_add_of_nonneg_left ha)
  let f : I ⊕ Fin 2 → twoTargetIndexSet e x y :=
    Sum.elim (fun i => ⟨e i, Or.inl ⟨i, rfl⟩⟩)
      (fun j => if j = 0 then ⟨x, Or.inr (Or.inl rfl)⟩ else ⟨y, Or.inr (Or.inr rfl)⟩)
  have hf : Function.Surjective f := by
    rintro ⟨u, hu⟩
    rcases hu with ⟨i, rfl⟩ | (rfl | rfl)
    · exact ⟨Sum.inl i, rfl⟩
    · exact ⟨Sum.inr 0, by simp [f]⟩
    · exact ⟨Sum.inr 1, by simp [f]⟩
  have hh := finite_nonnegative_sum_le_of_surjective f hf (fun u => ‖Q v.val u.val‖) (fun _ => norm_nonneg _)
  have hsum : (∑ j, ‖Q v.val (f j).val‖) = (∑ j, ‖Q v.val (e j)‖) + ‖Q v.val x‖ + ‖Q v.val y‖ := by
    simp only [Fintype.sum_sum_type, Fin.sum_univ_two]
    simp [f, add_assoc]
  rw [hsum] at hh
  linarith [htargetpoint x (Or.inl rfl), htargetpoint y (Or.inr rfl)]

end Rows
end LocalLaw
