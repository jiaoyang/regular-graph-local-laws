import LocalLaw.UnicyclicReferenceBounds
import LocalLaw.CycleReferenceImag
import LocalLaw.ReferenceImagComparison

/-!
# Uniform imaginary-part bounds through all unicyclic attachments

The verified cycle kernel supplies a length-independent reflection bound.
Exact leaf pruning contracts the inherited imaginary term, and the proved
uniform norm-eight estimate bounds the new real/imaginary cross term.
-/

open scoped BigOperators Matrix
namespace LocalLaw
universe u
noncomputable section
local instance unicyclicImagDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A product imaginary part is bounded by one norm and one imaginary part
in each direction. -/
theorem abs_im_mul_le_norm (a b : ℂ) :
    |(a * b).im| ≤ ‖a‖ * |b.im| + |a.im| * ‖b‖ := by
  rw [Complex.mul_im]
  calc
    _ ≤ |a.re * b.im| + |a.im * b.re| := abs_add_le _ _
    _ = |a.re| * |b.im| + |a.im| * |b.re| := by rw [abs_mul, abs_mul]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm a) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm b) (abs_nonneg _))

/-- Transfer factors introduce at most Imm in their own imaginary part. -/
theorem physical_leaf_transfer_im (d : ℕ) (hd : 3 ≤ d) (z : ℂ) (hz : 0 < z.im) :
    |(-semicircleRoot z * treeEdgeWeight d).im| ≤ (semicircleRoot z).im := by
  let m := semicircleRoot z
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hspos : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  have hsone : 1 ≤ Real.sqrt ((d : ℝ) - 1) := by
    have hh := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ d - 1 by linarith)
    simpa only [Real.sqrt_one] using hh
  have hα : (Real.sqrt ((d : ℝ) - 1))⁻¹ ≤ 1 := (inv_le_one₀ hspos).mpr hsone
  have him : 0 ≤ m.im := (semicircleRoot_im_pos hz).le
  simp only [treeEdgeWeight, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  rw [abs_mul, abs_neg, abs_of_nonneg him, abs_of_pos (inv_pos.mpr hspos)]
  exact (mul_le_mul_of_nonneg_left hα him).trans_eq (mul_one _)

/-- The squared transfer introduces at most Imm in its imaginary part. -/
theorem physical_leaf_factor_im (d : ℕ) (hd : 3 ≤ d) (z : ℂ) (hz : 0 < z.im) :
    |(semicircleRoot z ^ 2 / ((d : ℂ) - 1)).im| ≤ (semicircleRoot z).im := by
  let m := semicircleRoot z
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hkpos : 0 < (d : ℝ) - 1 := by linarith
  have him : 0 ≤ m.im := (semicircleRoot_im_pos hz).le
  have hre : |m.re| ≤ 1 := (Complex.abs_re_le_norm m).trans (semicircleRoot_norm_le_one z)
  have hcast : (d : ℂ) - 1 = ((d : ℝ) - 1 : ℝ) := by simp
  rw [hcast, Complex.div_ofReal_im, abs_div, abs_of_pos hkpos]
  have hpow : |(m ^ 2).im| ≤ 2 * m.im := by
    rw [pow_two, Complex.mul_im]
    have hid : m.re * m.im + m.im * m.re = 2 * m.re * m.im := by ring
    rw [hid, abs_mul, abs_mul, abs_of_nonneg him]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  exact (div_le_div_of_nonneg_right hpow hkpos.le).trans ((div_le_iff₀ hkpos).mpr (by nlinarith))

section FiniteGraph
variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- The actual abstract two-regular core inherits the proved cycle imaginary
bound by its constructed graph isomorphism and genuine inverse covariance. -/
theorem two_regular_reference_im (hconn : G.Connected) (hdeg : ∀ v, G.degree v = 2)
    (d : ℕ) (hd : 3 ≤ d) (z : ℂ) (hz : 0 < z.im) (i j : V) :
    |(fullTreeGreen G d (semicircleRoot z) z i j).im| ≤ 128 * (semicircleRoot z).im := by
  obtain ⟨ell, hell, ⟨e⟩⟩ := connected_two_regular_cycle_iso G hconn hdeg
  obtain ⟨n, rfl⟩ : ∃ n, ell = n + 3 := ⟨ell - 3, by omega⟩
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  rw [two_regular_reference_inverse_reindex G hdeg n d e]
  exact cycleReferenceMatrix_im_bound n d hd z hz a b

/-- Actual leaf attachment preserves the same constant 128 for every entry.
The uniform norm-eight bound is already proved for the entire remaining graph. -/
theorem leaf_reference_im_step (hconn : G.Connected) (hexcess : graphExcess G = 1)
    (d : ℕ) (hd : 3 ≤ d) (hdeg : ∀ x, G.degree x ≤ d)
    (v u : V) (hv : G.degree v = 1) (hvu : G.Adj v u) (z : ℂ) (hz : 0 < z.im)
    (hrem : ∀ a b : {x : V // x ≠ v},
      |(fullTreeGreen (G.induce {x | x ≠ v}) d (semicircleRoot z) z a b).im| ≤
        128 * (semicircleRoot z).im) :
    ∀ i j, |(fullTreeGreen G d (semicircleRoot z) z i j).im| ≤ 128 * (semicircleRoot z).im := by
  let m := semicircleRoot z
  let t := -m * treeEdgeWeight d
  let f := m ^ 2 / ((d : ℂ) - 1)
  let H := G.induce {x | x ≠ v}
  let u' : {x : V // x ≠ v} := ⟨u, hvu.ne.symm⟩
  have him : 0 ≤ m.im := (semicircleRoot_im_pos hz).le
  have hm := semicircleRoot_equation z
  have hconnH := leaf_delete_connected G hconn v u hv hvu
  have hexcessH := leaf_delete_excess G hconn hexcess v u hv hvu
  have hdegH : ∀ a : {x : V // x ≠ v}, H.degree a ≤ d := by
    intro a
    convert (induced_degree_le G {x | x ≠ v} a).trans (hdeg a.val) using 1
    apply congrArg (fun inst => @SimpleGraph.degree _ _ a inst)
    exact Subsingleton.elim _ _
  have hnormH : ∀ a b : {x : V // x ≠ v}, ‖fullTreeGreen H d m z a b‖ ≤ 8 := by
    intro a b
    have hh := unicyclic_reference_entry_bound H hconnH hexcessH d hd hdegH z hz a b
    have ht : ‖t‖ ≤ 1 := (cycle_transfer_norm_le_three_quarters d hd m (semicircleRoot_norm_le_one z)).trans (by norm_num)
    exact hh.trans ((mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg t) ht) (by norm_num)).trans_eq (mul_one _))
  have hret := leaf_reference_retained G d hd hdeg v u hv hvu m z hm hz him
  have hretEntry : ∀ a b : {x : V // x ≠ v}, fullTreeGreen G d m z a.val b.val = fullTreeGreen H d m z a b := by
    intro a b
    exact congrArg (fun M : Matrix {x : V // x ≠ v} {x : V // x ≠ v} ℂ => M a b) hret
  have hcrossBound : ∀ a b : {x : V // x ≠ v}, |(t * fullTreeGreen H d m z a b).im| ≤ 128 * m.im := by
    intro a b
    have ht := cycle_transfer_norm_le_three_quarters d hd m (semicircleRoot_norm_le_one z)
    have hti := physical_leaf_transfer_im d hd z hz
    have hh := abs_im_mul_le_norm t (fullTreeGreen H d m z a b)
    have h₁ := mul_le_mul ht (hrem a b) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3 / 4)
    have h₂ := mul_le_mul hti (hnormH a b) (norm_nonneg _) him
    linarith
  have hdiagonalBound : |(fullTreeGreen G d m z v v).im| ≤ 128 * m.im := by
    rw [leaf_reference_diagonal G d hd hdeg v u hv hvu m z hm hz him, Complex.add_im]
    have hh := abs_im_mul_le_norm f (fullTreeGreen H d m z u' u')
    have h₁ := mul_le_mul (physical_leaf_factor_norm d hd z) (hrem u' u')
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have h₂ := mul_le_mul (physical_leaf_factor_im d hd z hz) (hnormH u' u') (norm_nonneg _) him
    have hadd := abs_add_le m.im (f * fullTreeGreen H d m z u' u').im
    rw [abs_of_nonneg him] at hadd
    exact hadd.trans (by linarith)
  intro i j
  by_cases hi : i = v
  · subst i
    by_cases hj : j = v
    · subst j; exact hdiagonalBound
    · rw [(leaf_reference_cross G d hd hdeg v u hv hvu m z hm hz him ⟨j, hj⟩).1]
      exact hcrossBound u' ⟨j, hj⟩
  · by_cases hj : j = v
    · subst j
      rw [(leaf_reference_cross G d hd hdeg v u hv hvu m z hm hz him ⟨i, hi⟩).2]
      exact hcrossBound ⟨i, hi⟩ u'
    · rw [hretEntry ⟨i, hi⟩ ⟨j, hj⟩]
      exact hrem ⟨i, hi⟩ ⟨j, hj⟩

/-- Uniform imaginary-part bound for the actual full reference inverse of
any finite connected excess-one graph, including all attached trees. -/
theorem unicyclic_reference_im_bound (hconn : G.Connected) (hexcess : graphExcess G = 1)
    (d : ℕ) (hd : 3 ≤ d) (hdeg : ∀ v, G.degree v ≤ d) (z : ℂ) (hz : 0 < z.im)
    (i j : V) : |(fullTreeGreen G d (semicircleRoot z) z i j).im| ≤ 128 * (semicircleRoot z).im := by
  have aux : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W),
      Fintype.card W = n → H.Connected → graphExcess H = 1 → (∀ w, H.degree w ≤ d) →
        ∀ a b, |(fullTreeGreen H d (semicircleRoot z) z a b).im| ≤ 128 * (semicircleRoot z).im := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ H hcard hconnH hexcessH hdegH
      rcases balanced_connected_two_regular_or_leaf H hconnH (unicyclic_degree_sum H hconnH hexcessH) with htwo | ⟨v, hv⟩
      · exact two_regular_reference_im H hconnH htwo d hd z hz
      · obtain ⟨u, hvu⟩ := (H.degree_pos_iff_exists_adj v).mp (by omega : 0 < H.degree v)
        letI : Fintype {x : W // x ≠ v} := inferInstance
        have hcardDel := delete_vertex_card v
        have hlt : Fintype.card {x : W // x ≠ v} < n := by omega
        have hconnDel := leaf_delete_connected H hconnH v u hv hvu
        have hexcessDel := leaf_delete_excess H hconnH hexcessH v u hv hvu
        have hdegDel : ∀ a : {x : W // x ≠ v}, (H.induce {x | x ≠ v}).degree a ≤ d := by
          intro a
          convert (induced_degree_le H {x | x ≠ v} a).trans (hdegH a.val) using 1
          apply congrArg (fun inst => @SimpleGraph.degree _ _ a inst)
          exact Subsingleton.elim _ _
        have hrem := ih _ hlt {x : W // x ≠ v} (H.induce {x | x ≠ v}) rfl hconnDel hexcessDel hdegDel
        exact leaf_reference_im_step H hconnH hexcessH d hd hdegH v u hv hvu z hz hrem
  exact aux (Fintype.card V) V G rfl hconn hexcess hdeg i j

/-- Original regular-tree imaginary normalization, with a fixed constant 192. -/
theorem unicyclic_reference_im_md_bound (hconn : G.Connected) (hexcess : graphExcess G = 1)
    (d : ℕ) (hd : 3 ≤ d) (hdeg : ∀ v, G.degree v ≤ d) (z : ℂ) (hz : 0 < z.im) (i j : V) :
    |(fullTreeGreen G d (semicircleRoot z) z i j).im| ≤
      192 * (kestenMcKayTransform d (semicircleRoot z) z).im := by
  have h₁ := unicyclic_reference_im_bound G hconn hexcess d hd hdeg z hz i j
  have h₂ := semicircleRoot_im_le_md d hd z hz
  linarith

end FiniteGraph
end
end LocalLaw
