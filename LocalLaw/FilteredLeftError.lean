import LocalLaw.FilteredSurgeryColumns

/-! Filtered left error from sampled rows and an approximately diagonal reference. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance filteredLeftErrorDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]

/-- A genuinely diagonal reference tip row and a single changed edge use
only the two sampled old error rows. -/
theorem diagonal_tip_left_error_columns (Q W E : Matrix I I ℂ) (tip base : J→I) (lam : J→ℂ)
    (C w e : ℝ) (hC : 0≤C) (hw : 0≤w) (_he : 0≤e)
    (hQ : ∀ a k, Q (tip a) k=if k=tip a then lam a else 0)
    (hlam : ∀ a, ‖lam a‖≤C)
    (hW : ∀ a k, k≠base a→W (tip a) k=0)
    (hWcap : ∀ a, ‖W (tip a) (base a)‖≤w)
    (htip : ∀ k, ∑ a:J, ‖E (tip a) k‖≤e)
    (hbase : ∀ k, ∑ a:J, ‖E (base a) k‖≤e) (k : I) :
    (∑ a:J, ‖((1-Q*W)*E) (tip a) k‖)≤(1+C*w)*e := by
  have hproduct (a : J) : (Q*W*E) (tip a) k=lam a*W (tip a) (base a)*E (base a) k := by
    rw [Matrix.mul_assoc,Matrix.mul_apply]
    simp_rw [hQ]
    simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    rw [Matrix.mul_apply]
    have hh : (∑ l, W (tip a) l*E l k)=W (tip a) (base a)*E (base a) k := by
      apply Finset.sum_eq_single (base a)
      · intro l _ hl
        rw [hW a l hl,zero_mul]
      · intro hn
        exact False.elim (hn (Finset.mem_univ _))
    rw [hh]
    ring
  have hpoint (a : J) : ‖((1-Q*W)*E) (tip a) k‖≤‖E (tip a) k‖+C*w*‖E (base a) k‖ := by
    rw [Matrix.sub_mul,Matrix.one_mul,Matrix.sub_apply,hproduct]
    apply (norm_sub_le _ _).trans
    apply add_le_add_left
    rw [norm_mul,norm_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hlam a) (hWcap a) (norm_nonneg _) hC) (norm_nonneg _)
  calc
    _ ≤ ∑ a:J, (‖E (tip a) k‖+C*w*‖E (base a) k‖) := Finset.sum_le_sum (fun a _ => hpoint a)
    _ = (∑ a:J, ‖E (tip a) k‖)+C*w*(∑ a:J, ‖E (base a) k‖) := by rw [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ e+C*w*e := add_le_add (htip k) (mul_le_mul_of_nonneg_left (hbase k) (mul_nonneg hC hw))
    _ = _ := by ring

/-- Deviating from the diagonal reference costs a quadratic old-error
remainder; the row bound is on the product with the genuine surgery matrix. -/
theorem filtered_left_error_reference_comparison (Q Q₀ W E : Matrix I I ℂ) (tip : J→I)
    (s r δ : ℝ) (_hs : 0≤s) (_hr : 0≤r) (hδ : 0≤δ)
    (hreference : ∀ k, ∑ a:J, ‖((1-Q₀*W)*E) (tip a) k‖≤s)
    (hrow : ∀ a, ∑ l, ‖((Q-Q₀)*W) (tip a) l‖≤r)
    (hE : ∀ l k, ‖E l k‖≤δ) (k : I) :
    (∑ a:J, ‖((1-Q*W)*E) (tip a) k‖)≤s+(Fintype.card J:ℝ)*r*δ := by
  have hid : (1-Q*W)*E=(1-Q₀*W)*E-((Q-Q₀)*W)*E := by noncomm_ring
  have hrem (a : J) : ‖(((Q-Q₀)*W)*E) (tip a) k‖≤r*δ :=
    matrix_mul_entry_bound_of_row ((Q-Q₀)*W) E (tip a) k r δ hδ (hrow a) (fun l => hE l k)
  calc
    _ = ∑ a:J, ‖((1-Q₀*W)*E-((Q-Q₀)*W)*E) (tip a) k‖ := by rw [hid]
    _ ≤ ∑ a:J, (‖((1-Q₀*W)*E) (tip a) k‖+‖(((Q-Q₀)*W)*E) (tip a) k‖) :=
      Finset.sum_le_sum (fun a _ => norm_sub_le _ _)
    _ = _ := Finset.sum_add_distrib
    _ ≤ s+∑ _a:J, r*δ := add_le_add (hreference k) (Finset.sum_le_sum (fun a _ => hrem a))
    _ = _ := by simp; ring

/-- A supported surgery ignores uncontrolled target columns of the model
row: only its actual endpoint entries enter this product. -/
theorem supported_product_row_sum_bound {L : Type} [Fintype L]
    (U W : Matrix I I ℂ) (e : L↪I) (i : I) (ζ w : ℝ) (hw : 0≤w)
    (hsupport : ∀ u v, u∉Set.range e→W u v=0)
    (hU : ∀ l, ‖U i (e l)‖≤ζ) (hW : ∀ u, ∑ v, ‖W u v‖≤w) :
    (∑ v, ‖(U*W) i v‖)≤(Fintype.card L:ℝ)*ζ*w := by
  have hsum : (∑ u, ‖U i u‖*(∑ v, ‖W u v‖))=
      ∑ l:L, ‖U i (e l)‖*(∑ v, ‖W (e l) v‖) := by
    calc
      _ = ∑ u∈Finset.univ.image e, ‖U i u‖*(∑ v, ‖W u v‖) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro u _ hu
        have hn : u∉Set.range e := by
          simpa only [Finset.mem_image,Finset.mem_univ,true_and,Set.mem_range] using hu
        simp only [hsupport u _ hn,norm_zero,Finset.sum_const_zero,mul_zero]
      _ = _ := Finset.sum_image (fun _ _ _ _ h => e.injective h)
  calc
    _ ≤ ∑ v, ∑ u, ‖U i u‖*‖W u v‖ := Finset.sum_le_sum (fun v _ => matrix_mul_entry_norm_le U W i v)
    _ = ∑ u, ‖U i u‖*(∑ v, ‖W u v‖) := by rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    _ = _ := hsum
    _ ≤ ∑ _l:L, ζ*w := by
      apply Finset.sum_le_sum
      intro l _
      exact (mul_le_mul_of_nonneg_left (hW (e l)) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (hU l) hw)
    _ = _ := by simp; ring

end LocalLaw
