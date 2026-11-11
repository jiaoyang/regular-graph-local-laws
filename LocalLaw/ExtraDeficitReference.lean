import LocalLaw.LeafDeficitAugmentation
import LocalLaw.FiniteReferenceThreshold

/-!
# Extra-deficit reference bounds by one actual leaf attachment

This is the finite source mechanism of Remark 2.8. An explicit reference
certificate for the lower-complexity augmented graph transfers through the
genuine deleted-leaf Schur identity. No post-deletion diagonal lower bound
is asserted.
-/

open scoped BigOperators Matrix
namespace LocalLaw
noncomputable section
local instance extraDeficitDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section UnitDeletion
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual inverse formula when a final singleton vertex is deleted. -/
theorem inverse_delete_unit_last (M : Matrix (V ⊕ Unit) (V ⊕ Unit) ℂ)
    (hM : IsUnit M) (hA : IsUnit M.toBlocks₁₁) (i j : V) :
    M.toBlocks₁₁⁻¹ i j = M⁻¹ (Sum.inl i) (Sum.inl j) -
      M⁻¹ (Sum.inl i) (Sum.inr ()) * M⁻¹ (Sum.inr ()) (Sum.inl j) /
        M⁻¹ (Sum.inr ()) (Sum.inr ()) := by
  let e : Unit ⊕ V ≃ V ⊕ Unit := Equiv.sumComm Unit V
  let M' := M.submatrix e e
  have hM' : IsUnit M' := (Matrix.isUnit_submatrix_equiv e e).mpr hM
  have hD : IsUnit M'.toBlocks₂₂ := hA
  have hh := deleted_block_inverse M' hM' hD
  have hinv : M'⁻¹ = M⁻¹.submatrix e e := Matrix.inv_submatrix_equiv M e e
  rw [hinv] at hh
  change M.toBlocks₁₁⁻¹ = M⁻¹.toBlocks₁₁ - M⁻¹.toBlocks₁₂ *
    M⁻¹.toBlocks₂₂⁻¹ * M⁻¹.toBlocks₂₁ at hh
  have hentry := congrArg (fun A : Matrix V V ℂ => A i j) hh
  dsimp only at hentry
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fintype.sum_unique, Matrix.inv_subsingleton,
    Matrix.diagonal_apply_eq, Ring.inverse_eq_inv, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
    Matrix.toBlocks₂₂, Matrix.toBlocks₂₁] at hentry
  rw [show (default : Unit) = () from Subsingleton.elim _ _] at hentry
  simp only [Matrix.of_apply] at hentry
  convert hentry using 1
  ring

end UnitDeletion

/-- The transfer rate is uniformly controlled by the regular-tree diagonal.
Keeping these factors avoids imposing an artificial bounded spectral domain. -/
theorem physical_transfer_reference_norm (d : ℕ) (hd : 3 ≤ d) (z : ℂ) (hz : 0 < z.im) :
    ‖-semicircleRoot z * treeEdgeWeight d‖ ≤ 2 * ‖kestenMcKayTransform d (semicircleRoot z) z‖ ∧
      ‖-semicircleRoot z * treeEdgeWeight d‖ ^ 2 ≤ ‖kestenMcKayTransform d (semicircleRoot z) z‖ := by
  let m := semicircleRoot z
  let p := kestenMcKayTransform d m z
  let f := m ^ 2 / ((d : ℂ) - 1)
  let ρ := ‖-m * treeEdgeWeight d‖
  have hfix : p = m + f * p := kestenMcKay_leaf_fixed_point d hd z hz
  have hf : ‖f‖ ≤ 1 / 2 := physical_leaf_factor_norm d hd z
  have hm : ‖m‖ ≤ 1 := semicircleRoot_norm_le_one z
  have hp0 : 0 ≤ ‖p‖ := norm_nonneg _
  have hm0 : 0 ≤ ‖m‖ := norm_nonneg _
  have hmp : ‖m‖ ≤ (3 / 2 : ℝ) * ‖p‖ := by
    have hid : m = p - f * p := by linear_combination -hfix
    have hh := norm_sub_le p (f * p)
    rw [← hid, norm_mul] at hh
    nlinarith
  have hα : ‖treeEdgeWeight d‖ ≤ 1 := by
    have hh := cycle_transfer_norm_le_three_quarters d hd (1 : ℂ) (by norm_num)
    simp only [neg_one_mul, norm_neg] at hh
    linarith
  have hρ : ρ ≤ ‖m‖ := by
    dsimp [ρ]
    rw [norm_mul, norm_neg]
    exact (mul_le_mul_of_nonneg_left hα hm0).trans_eq (mul_one _)
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hkcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hkC : ((d - 1 : ℕ) : ℂ) = (d : ℂ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hρ2 : ρ ^ 2 ≤ (1 / 2 : ℝ) * ‖m‖ := by
    have hsq : (-m * treeEdgeWeight d) ^ 2 = f := by
      dsimp [f]
      rw [mul_pow, neg_sq, treeEdgeWeight_sq d hd]
      ring
    dsimp only [ρ]
    rw [← norm_pow, hsq]
    change ‖m ^ 2 / ((d : ℂ) - 1)‖ ≤ _
    rw [← hkC, norm_div, norm_pow, Complex.norm_natCast, hkcast]
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < d - 1)).mpr
    nlinarith [mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ d - 1 by linarith) hm0]
  constructor <;> change _ ≤ _ <;> linarith

/-- Imaginary stability of the scalar deleted-vertex Schur expression. The
reference pivot scales with p, and both cross entries scale with p as well. -/
theorem schur_reference_imaginary_bound (a b c e : ℂ) (C p I : ℝ)
    (hC : 0 < C) (hp : 0 < p) (hI : 0 ≤ I)
    (hb : ‖b‖ ≤ 2 * C * p) (hc : ‖c‖ ≤ 2 * C * p) (he : p / C ≤ ‖e‖)
    (haim : |a.im| ≤ C * I) (hbim : |b.im| ≤ C * I)
    (hcim : |c.im| ≤ C * I) (heim : |e.im| ≤ C * I) :
    |(a - b * c / e).im| ≤ (C + 4 * C ^ 3 + 4 * C ^ 5) * I := by
  have hinv : ‖e⁻¹‖ ≤ C / p := by
    rw [norm_inv, ← one_div]
    calc
      _ ≤ 1 / (p / C) := one_div_le_one_div_of_le (div_pos hp hC) he
      _ = _ := by field_simp
  have hinvim : |(e⁻¹).im| ≤ C ^ 3 * I / p ^ 2 := by
    rw [Complex.inv_im, abs_div, abs_neg, Complex.normSq_eq_norm_sq]
    rw [abs_of_nonneg (sq_nonneg ‖e‖)]
    calc
      _ ≤ (C * I) / (p / C) ^ 2 := div_le_div₀ (by positivity) heim (sq_pos_of_pos (div_pos hp hC))
        (pow_le_pow_left₀ (div_nonneg hp.le hC.le) he 2)
      _ = _ := by field_simp; ring
  have hprodIm : |(b * c).im| ≤ 4 * C ^ 2 * p * I := by
    have hh := abs_im_mul_le_norm b c
    have h₁ := mul_le_mul hb hcim (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * C * p)
    have h₂ := mul_le_mul hbim hc (norm_nonneg _) (by positivity : (0 : ℝ) ≤ C * I)
    nlinarith
  have hprodNorm : ‖b * c‖ ≤ 4 * C ^ 2 * p ^ 2 := by
    rw [norm_mul]
    have hh := mul_le_mul hb hc (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * C * p)
    nlinarith
  have hquotIm : |(b * c / e).im| ≤ (4 * C ^ 3 + 4 * C ^ 5) * I := by
    have hid : b * c / e = e⁻¹ * (b * c) := by ring
    rw [hid]
    have hh := abs_im_mul_le_norm e⁻¹ (b * c)
    have h₁ := mul_le_mul hinv hprodIm (abs_nonneg _) (div_nonneg hC.le hp.le)
    have h₂ := mul_le_mul hinvim hprodNorm (norm_nonneg _) (by positivity : (0 : ℝ) ≤ C ^ 3 * I / p ^ 2)
    have hcap : (C / p) * (4 * C ^ 2 * p * I) + (C ^ 3 * I / p ^ 2) * (4 * C ^ 2 * p ^ 2) =
        (4 * C ^ 3 + 4 * C ^ 5) * I := by field_simp; ring
    exact hh.trans ((add_le_add h₁ h₂).trans_eq hcap)
  rw [Complex.sub_im]
  exact (abs_sub _ _).trans (by linarith)

namespace DeficientGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

/-- Genuine Schur identity recovering the original deficient extension after
removing the newly attached leaf. -/
theorem attachLeaf_green_schur (g : DeficientGraph V d) (hd : 3 ≤ d) (v : V)
    (hv : 0 < g.deficit v) (w z : ℂ) (hz : 0 < z.im) (hw : 0 ≤ w.im) (i j : V) :
    g.extensionGreen w z i j =
      (g.attachLeaf (by omega) v hv).extensionGreen w z (Sum.inl i) (Sum.inl j) -
        (g.attachLeaf (by omega) v hv).extensionGreen w z (Sum.inl i) (Sum.inr ()) *
        (g.attachLeaf (by omega) v hv).extensionGreen w z (Sum.inr ()) (Sum.inl j) /
        (g.attachLeaf (by omega) v hv).extensionGreen w z (Sum.inr ()) (Sum.inr ()) := by
  let g' := g.attachLeaf (by omega : 1 ≤ d) v hv
  have hprincipal : (g'.extensionMatrix w z).toBlocks₁₁ = g.extensionMatrix w z :=
    g.attachLeaf_extensionMatrix_principal (by omega) v hv w z
  have hA : IsUnit (g'.extensionMatrix w z).toBlocks₁₁ := by
    rw [hprincipal]
    exact g.extensionMatrix_isUnit hd w z hz hw
  have hh := inverse_delete_unit_last (g'.extensionMatrix w z) (g'.extensionMatrix_isUnit hd w z hz hw) hA i j
  rw [hprincipal] at hh
  exact hh

/-- Reference entry and imaginary estimates transfer from the actual
lower-complexity attached graph. The relative pivot and transfer factors
cancel, so the constants are uniform over the entire upper half-plane. -/
theorem attachLeaf_reference_bounds (g : DeficientGraph V d) (hd : 3 ≤ d)
    (v : V) (hv : 0 < g.deficit v) (hconn : g.graph.Connected) (z : ℂ) (hz : 0 < z.im)
    (C : ℝ) (hC : 1 ≤ C)
    (hentry : ∀ a b, ‖(g.attachLeaf (by omega) v hv).extensionGreen (semicircleRoot z) z a b‖ ≤
      C * ‖-semicircleRoot z * treeEdgeWeight d‖ ^ (g.attachLeaf (by omega) v hv).graph.dist a b)
    (himag : ∀ a b, |((g.attachLeaf (by omega) v hv).extensionGreen (semicircleRoot z) z a b).im| ≤
      C * (kestenMcKayTransform d (semicircleRoot z) z).im)
    (hpivot : ‖kestenMcKayTransform d (semicircleRoot z) z‖ / C ≤
      ‖(g.attachLeaf (by omega) v hv).extensionGreen (semicircleRoot z) z (Sum.inr ()) (Sum.inr ())‖) :
    (∀ i j, ‖g.extensionGreen (semicircleRoot z) z i j‖ ≤
      (C + C ^ 3) * ‖-semicircleRoot z * treeEdgeWeight d‖ ^ g.graph.dist i j) ∧
    (∀ i j, |(g.extensionGreen (semicircleRoot z) z i j).im| ≤
      (C + 4 * C ^ 3 + 4 * C ^ 5) * (kestenMcKayTransform d (semicircleRoot z) z).im) := by
  let g' := g.attachLeaf (by omega : 1 ≤ d) v hv
  let P := g'.extensionGreen (semicircleRoot z) z
  let ρ := ‖-semicircleRoot z * treeEdgeWeight d‖
  let p := ‖kestenMcKayTransform d (semicircleRoot z) z‖
  let I := (kestenMcKayTransform d (semicircleRoot z) z).im
  have hCp : 0 < C := by linarith
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hρ1 : ρ ≤ 1 := (cycle_transfer_norm_le_three_quarters d hd _ (semicircleRoot_norm_le_one z)).trans (by norm_num)
  have hI : 0 < I := kestenMcKayTransform_im_pos d _ z hz (semicircleRoot_im_pos hz).le
  have hp : 0 < p := hI.trans_le ((le_abs_self _).trans (Complex.abs_im_le_norm _))
  obtain ⟨hρp, hρ2⟩ := physical_transfer_reference_norm d hd z hz
  have hdistOld : ∀ i j, g'.graph.dist (Sum.inl i) (Sum.inl j) = g.graph.dist i j :=
    leafAugmentGraph_distance_old g.graph v hconn
  have hdistNew : ∀ j, g'.graph.dist (Sum.inr ()) (Sum.inl j) = g.graph.dist v j + 1 :=
    leafAugmentGraph_distance_new g.graph v hconn
  have hdistCross : ∀ i, g'.graph.dist (Sum.inl i) (Sum.inr ()) = g.graph.dist i v + 1 := by
    intro i
    calc
      _ = g'.graph.dist (Sum.inr ()) (Sum.inl i) := g'.graph.dist_comm
      _ = g.graph.dist v i + 1 := hdistNew i
      _ = g.graph.dist i v + 1 := by rw [g.graph.dist_comm]
  have hcross : ∀ i, ‖P (Sum.inl i) (Sum.inr ())‖ ≤ 2 * C * p ∧
      ‖P (Sum.inr ()) (Sum.inl i)‖ ≤ 2 * C * p := by
    intro i
    have h₁ := hentry (Sum.inl i) (Sum.inr ())
    have h₂ := hentry (Sum.inr ()) (Sum.inl i)
    rw [hdistCross] at h₁
    rw [hdistNew] at h₂
    have hp₁ : ρ ^ (g.graph.dist i v + 1) ≤ ρ := by
      simpa only [pow_one] using pow_le_pow_of_le_one hρ0 hρ1 (show 1 ≤ g.graph.dist i v + 1 by omega)
    have hp₂ : ρ ^ (g.graph.dist v i + 1) ≤ ρ := by
      simpa only [pow_one] using pow_le_pow_of_le_one hρ0 hρ1 (show 1 ≤ g.graph.dist v i + 1 by omega)
    constructor
    · exact h₁.trans ((mul_le_mul_of_nonneg_left hp₁ hCp.le).trans (by nlinarith))
    · exact h₂.trans ((mul_le_mul_of_nonneg_left hp₂ hCp.le).trans (by nlinarith))
  constructor
  · intro i j
    have ha := hentry (Sum.inl i) (Sum.inl j)
    rw [hdistOld] at ha
    have hb := hentry (Sum.inl i) (Sum.inr ())
    have hc := hentry (Sum.inr ()) (Sum.inl j)
    rw [hdistCross] at hb
    rw [hdistNew] at hc
    have hproduct : ‖P (Sum.inl i) (Sum.inr ())‖ * ‖P (Sum.inr ()) (Sum.inl j)‖ ≤
        C ^ 2 * p * ρ ^ g.graph.dist i j := by
      have hpow : ρ ^ (g.graph.dist i v + g.graph.dist v j) ≤ ρ ^ g.graph.dist i j :=
        pow_le_pow_of_le_one hρ0 hρ1 (hconn.dist_triangle (u := i) (v := v) (w := j))
      calc
        _ ≤ (C * ρ ^ (g.graph.dist i v + 1)) * (C * ρ ^ (g.graph.dist v j + 1)) :=
          mul_le_mul hb hc (norm_nonneg _) (by positivity)
        _ = C ^ 2 * (ρ ^ (g.graph.dist i v + g.graph.dist v j) * ρ ^ 2) := by
          simp only [pow_add, pow_one, pow_two]
          ring
        _ ≤ C ^ 2 * (ρ ^ g.graph.dist i j * p) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hpow hρ2 (sq_nonneg _) (pow_nonneg hρ0 _)) (sq_nonneg _)
        _ = _ := by ring
    have hquot : ‖P (Sum.inl i) (Sum.inr ()) * P (Sum.inr ()) (Sum.inl j) / P (Sum.inr ()) (Sum.inr ())‖ ≤
        C ^ 3 * ρ ^ g.graph.dist i j := by
      rw [norm_div, norm_mul]
      calc
        _ ≤ (C ^ 2 * p * ρ ^ g.graph.dist i j) / (p / C) :=
          div_le_div₀ (by positivity) hproduct (div_pos hp hCp) hpivot
        _ = _ := by field_simp; ring
    rw [g.attachLeaf_green_schur hd v hv _ z hz (semicircleRoot_im_pos hz).le i j]
    exact (norm_sub_le _ _).trans ((add_le_add ha hquot).trans_eq (by ring))
  · intro i j
    rw [g.attachLeaf_green_schur hd v hv _ z hz (semicircleRoot_im_pos hz).le i j]
    exact schur_reference_imaginary_bound _ _ _ _ C p I hCp hp hI.le
      (hcross i).1 (hcross j).2 hpivot (himag _ _) (himag _ _) (himag _ _) (himag _ _)

end DeficientGraph

/-- A uniform constant sufficient for both estimates after one deletion. -/
def extraDeficitConstant (C : ℝ) : ℝ := C + 4 * C ^ 3 + 4 * C ^ 5

theorem extraDeficitConstant_ge_one (C : ℝ) (hC : 1 ≤ C) : 1 ≤ extraDeficitConstant C := by
  dsimp [extraDeficitConstant]
  have hCp : 0 ≤ C := by linarith
  nlinarith [pow_nonneg hCp 3, pow_nonneg hCp 5]

/-- Finite Remark 2.8 for an arbitrary proved reference class: a positive
source deficit allows one extra unit of total deficit-plus-excess complexity.
Only the entry and imaginary estimates are asserted after deletion. -/
theorem finiteReferenceThreshold_extra_deficit (d ω : ℕ) (hd : 3 ≤ d)
    (hclass : FiniteReferenceThreshold d ω) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (g : DeficientGraph V d),
      g.graph.Connected → (∑ v, g.deficit v) + graphExcess g.graph ≤ ω + 1 →
      (∃ v, 0 < g.deficit v) → ∀ z : ℂ, 0 < z.im →
      (∀ i j, ‖g.extensionGreen (semicircleRoot z) z i j‖ ≤
        K * ‖-semicircleRoot z * treeEdgeWeight d‖ ^ g.graph.dist i j) ∧
      (∀ i j, |(g.extensionGreen (semicircleRoot z) z i j).im| ≤
        K * (kestenMcKayTransform d (semicircleRoot z) z).im) := by
  obtain ⟨C, hC, href⟩ := hclass
  refine ⟨extraDeficitConstant C, extraDeficitConstant_ge_one C hC, ?_⟩
  intro V _ _ g hconn hbudget hpositive z hz
  obtain ⟨v, hv⟩ := hpositive
  let g' := g.attachLeaf (by omega : 1 ≤ d) v hv
  have hconn' : g'.graph.Connected := leafAugmentGraph_connected g.graph v hconn
  have hcomplex := g.attachLeaf_complexity (by omega : 1 ≤ d) v hv hconn
  change ((∑ a, g'.deficit a) + graphExcess g'.graph) + 1 = (∑ a, g.deficit a) + graphExcess g.graph at hcomplex
  have hbudget' : (∑ a, g'.deficit a) + graphExcess g'.graph ≤ ω := by omega
  have h := href (V ⊕ Unit) g' hconn' hbudget' z hz
  have hh := g.attachLeaf_reference_bounds hd v hv hconn z hz C hC h.1 h.2.1 (h.2.2 (Sum.inr ()))
  refine ⟨?_, hh.2⟩
  intro i j
  apply (hh.1 i j).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
  dsimp [extraDeficitConstant]
  have hCp : 0 ≤ C := by linarith
  nlinarith [pow_nonneg hCp 3, pow_nonneg hCp 5]

/-- The actual degree-dependent extra-deficit constant chosen from the
constructed maximal finite reference threshold. -/
def finiteExtraReferenceConstant (d : ℕ) : ℝ := extraDeficitConstant (finiteReferenceConstant d)

theorem finiteExtraReferenceConstant_ge_one (d : ℕ) (hd : 3 ≤ d) :
    1 ≤ finiteExtraReferenceConstant d := extraDeficitConstant_ge_one _ (finiteReferenceConstant_ge_one d hd)

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

/-- Actual extra-deficit bounds at the constructed maximal finite threshold,
with no new reference-class or attachment assumption. -/
theorem finiteOmega_extra_reference_bounds (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hconn : g.graph.Connected)
    (hbudget : (∑ v, g.deficit v) + graphExcess g.graph ≤ finiteOmega d + 1)
    (hpositive : ∃ v, 0 < g.deficit v) (z : ℂ) (hz : 0 < z.im) :
    (∀ i j, ‖g.extensionGreen (semicircleRoot z) z i j‖ ≤
      finiteExtraReferenceConstant d * ‖-semicircleRoot z * treeEdgeWeight d‖ ^ g.graph.dist i j) ∧
    (∀ i j, |(g.extensionGreen (semicircleRoot z) z i j).im| ≤
      finiteExtraReferenceConstant d * (kestenMcKayTransform d (semicircleRoot z) z).im) := by
  obtain ⟨v, hv⟩ := hpositive
  let g' := g.attachLeaf (by omega : 1 ≤ d) v hv
  have hconn' : g'.graph.Connected := leafAugmentGraph_connected g.graph v hconn
  have hcomplex := g.attachLeaf_complexity (by omega : 1 ≤ d) v hv hconn
  change ((∑ a, g'.deficit a) + graphExcess g'.graph) + 1 = (∑ a, g.deficit a) + graphExcess g.graph at hcomplex
  have hbudget' : (∑ a, g'.deficit a) + graphExcess g'.graph ≤ finiteOmega d := by omega
  have h := LocalLaw.finiteOmega_reference_bounds d hd g' hconn' hbudget' z hz
  have hC := finiteReferenceConstant_ge_one d hd
  have hh := g.attachLeaf_reference_bounds hd v hv hconn z hz (finiteReferenceConstant d)
    hC h.1 h.2.1 (h.2.2 (Sum.inr ()))
  refine ⟨?_, hh.2⟩
  intro i j
  apply (hh.1 i j).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
  dsimp [finiteExtraReferenceConstant, extraDeficitConstant]
  have hCp : 0 ≤ finiteReferenceConstant d := by linarith
  nlinarith [pow_nonneg hCp 3, pow_nonneg hCp 5]

/-- In particular, every connected graph with a positive source deficit and
complexity at most two has the entry and imaginary reference bounds. -/
theorem reference_two_nonzero_deficit_bounds (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hconn : g.graph.Connected) (hbudget : (∑ v, g.deficit v) + graphExcess g.graph ≤ 2)
    (hpositive : ∃ v, 0 < g.deficit v) (z : ℂ) (hz : 0 < z.im) :
    (∀ i j, ‖g.extensionGreen (semicircleRoot z) z i j‖ ≤
      finiteExtraReferenceConstant d * ‖-semicircleRoot z * treeEdgeWeight d‖ ^ g.graph.dist i j) ∧
    (∀ i j, |(g.extensionGreen (semicircleRoot z) z i j).im| ≤
      finiteExtraReferenceConstant d * (kestenMcKayTransform d (semicircleRoot z) z).im) := by
  have hω := finiteOmega_positive d hd
  exact g.finiteOmega_extra_reference_bounds hd hconn (by omega) hpositive z hz

end DeficientGraph
end
end LocalLaw
