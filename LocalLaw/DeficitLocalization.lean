import LocalLaw.FiniteReferenceModelBounds
import LocalLaw.LocalizationIdentity

/-!
# Removing only the deficits outside a local model

The actual finite reference class is preserved, including the extra-deficit
case. The resulting matrix difference is exactly a nonnegative diagonal
charge supported outside the chosen neighborhood, as in source (B.11).
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance deficitLocalizationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

def clearOutsideDeficit (g : DeficientGraph V d) (S : Set V) : DeficientGraph V d where
  graph := g.graph
  deficit := fun v => if v ∈ S then g.deficit v else 0
  degree_deficit_le := by
    intro v
    split_ifs
    · exact g.degree_deficit_le v
    · simpa only [add_zero] using g.degree_le v

omit [DecidableEq V] in
theorem clearOutsideDeficit_sum_le (g : DeficientGraph V d) (S : Set V) :
    (∑ v, (g.clearOutsideDeficit S).deficit v) ≤ ∑ v, g.deficit v := by
  apply Finset.sum_le_sum
  intro v _
  change (if v ∈ S then g.deficit v else 0) ≤ g.deficit v
  split_ifs <;> omega

omit [DecidableEq V] in
/-- Removing exterior deficits preserves the actual allowed reference class,
even if it removes the last positive deficit and hence loses the extra unit. -/
theorem clearOutsideDeficit_budget (g : DeficientGraph V d) (S : Set V)
    (hbudget : g.FiniteReferenceBudget) : (g.clearOutsideDeficit S).FiniteReferenceBudget := by
  have hsum := g.clearOutsideDeficit_sum_le S
  rcases hbudget with h | ⟨h, hpositive⟩
  · left
    change (∑ v, (g.clearOutsideDeficit S).deficit v) + graphExcess g.graph ≤ finiteOmega d
    omega
  · by_cases hpos : ∃ v, 0 < (g.clearOutsideDeficit S).deficit v
    · right
      refine ⟨?_, hpos⟩
      change (∑ v, (g.clearOutsideDeficit S).deficit v) + graphExcess g.graph ≤ finiteOmega d + 1
      omega
    · have hzero : ∀ v, (g.clearOutsideDeficit S).deficit v = 0 := by
        intro v
        exact Nat.eq_zero_of_not_pos (fun hv => hpos ⟨v, hv⟩)
      obtain ⟨v, hv⟩ := hpositive
      have htotal : 0 < ∑ x, g.deficit x := hv.trans_le
        (Finset.single_le_sum (fun x _ => Nat.zero_le _) (Finset.mem_univ v))
      left
      change (∑ v, (g.clearOutsideDeficit S).deficit v) + graphExcess g.graph ≤ finiteOmega d
      simp only [hzero, Finset.sum_const_zero, zero_add]
      omega

def exteriorDeficitCharge (g : DeficientGraph V d) (S : Set V) (v : V) : ℝ :=
  if v ∈ S then 0 else (g.deficit v : ℝ) / ((d : ℝ) - 1)

omit [DecidableEq V] in
theorem exteriorDeficitCharge_nonnegative (g : DeficientGraph V d) (hd : 3 ≤ d) (S : Set V) (v : V) :
    0 ≤ g.exteriorDeficitCharge S v := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  unfold exteriorDeficitCharge
  split_ifs
  · exact le_rfl
  · exact div_nonneg (Nat.cast_nonneg _) (by linarith)

omit [DecidableEq V] in
theorem clearOutsideDeficit_boundaryCoefficient (g : DeficientGraph V d) (S : Set V) (v : V) :
    (g.clearOutsideDeficit S).boundaryCoefficient v =
      g.boundaryCoefficient v + g.exteriorDeficitCharge S v := by
  by_cases hv : v ∈ S
  · simp [clearOutsideDeficit, boundaryCoefficient, exteriorDeficitCharge, hv]
  · simp only [clearOutsideDeficit, boundaryCoefficient, exteriorDeficitCharge, if_neg hv, Nat.cast_zero, sub_zero]
    ring

theorem clearOutsideDeficit_extensionMatrix_difference (g : DeficientGraph V d) (S : Set V) (q z : ℂ) :
    (g.clearOutsideDeficit S).extensionMatrix q z - g.extensionMatrix q z =
      (-q) • Matrix.diagonal (fun v => (g.exteriorDeficitCharge S v : ℂ)) := by
  have hD : (g.clearOutsideDeficit S).boundaryDiagonal = g.boundaryDiagonal +
      Matrix.diagonal (fun v => (g.exteriorDeficitCharge S v : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [boundaryDiagonal, Matrix.add_apply, Matrix.diagonal_apply_eq,
        g.clearOutsideDeficit_boundaryCoefficient S i, Complex.ofReal_add]
    · simp only [boundaryDiagonal, Matrix.add_apply, Matrix.diagonal_apply_ne _ hij]
      simp
  change (spectralMatrix g.H z - q • (g.clearOutsideDeficit S).boundaryDiagonal) -
    (spectralMatrix g.H z - q • g.boundaryDiagonal) = _
  rw [hD]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

omit [DecidableEq V] in
theorem exteriorDeficitCharge_sum_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (hbudget : g.FiniteReferenceBudget) :
    (∑ v, g.exteriorDeficitCharge S v) ≤ ((finiteOmega d : ℝ) + 1) / ((d : ℝ) - 1) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have htotal : (∑ v, g.deficit v) ≤ finiteOmega d + 1 := by have hh := hbudget.complexity_le; omega
  have htotalR : (∑ v, (g.deficit v : ℝ)) ≤ (finiteOmega d : ℝ) + 1 := by exact_mod_cast htotal
  calc
    _ ≤ ∑ v, (g.deficit v : ℝ) / ((d : ℝ) - 1) := by
      apply Finset.sum_le_sum
      intro v _
      unfold exteriorDeficitCharge
      split_ifs
      · exact div_nonneg (Nat.cast_nonneg _) (by linarith)
      · exact le_rfl
    _ = (∑ v, (g.deficit v : ℝ)) / ((d : ℝ) - 1) := (Finset.sum_div ..).symm
    _ ≤ _ := div_le_div_of_nonneg_right htotalR (by linarith)

/-- Genuine source (B.11): exterior deficits affect the target inverse
only through two decaying kernel factors. The finite reference budget,
kernel decay and diagonal perturbation mass are all proved here. -/
theorem clearOutsideDeficit_localization_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.Connected) (hbudget : g.FiniteReferenceBudget) (S : Set V)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2)
    (i j : V) (r : ℕ)
    (hfar : ∀ v ∉ S, r ≤ g.graph.dist i v ∧ r ≤ g.graph.dist v j) :
    ‖g.extensionGreen q z i j - (g.clearOutsideDeficit S).extensionGreen q z i j‖ ≤
      4 * finiteExtraReferenceConstant d ^ 2 * ‖q‖ *
        (((finiteOmega d : ℝ) + 1) / ((d : ℝ) - 1)) * physicalTransfer d z ^ (2 * r) := by
  let g' := g.clearOutsideDeficit S
  let t := physicalTransfer d z
  let K : V → V → ℝ := fun a b => t ^ g.graph.dist a b
  let w := g.exteriorDeficitCharge S
  let C := finiteExtraReferenceConstant d
  have hC : 0 ≤ C := le_trans (by norm_num) (finiteExtraReferenceConstant_ge_one d hd)
  have ht : 0 ≤ t := (physicalTransfer_pos d hd z).le
  have htone : t ≤ 1 := by have hh := physicalTransfer_sq_le_half d hd z; change t ^ 2 ≤ 1 / 2 at hh; nlinarith
  have hw : ∀ v, 0 ≤ w v := g.exteriorDeficitCharge_nonnegative hd S
  have hconv : (∑ v, w v * K i v * K v j) ≤
      (((finiteOmega d : ℝ) + 1) / ((d : ℝ) - 1)) * t ^ (2 * r) := by
    calc
      _ ≤ ∑ v, w v * (t ^ r * t ^ r) := by
        apply Finset.sum_le_sum
        intro v _
        by_cases hv : v ∈ S
        · simp only [w, exteriorDeficitCharge, if_pos hv, zero_mul, le_refl]
        · have ha := pow_le_pow_of_le_one ht htone (hfar v hv).1
          have hb := pow_le_pow_of_le_one ht htone (hfar v hv).2
          have hh' := mul_le_mul_of_nonneg_left
            (mul_le_mul ha hb (pow_nonneg ht _) (pow_nonneg ht _)) (hw v)
          convert hh' using 1; ring
      _ = (∑ v, w v) * t ^ (2 * r) := by
        rw [← Finset.sum_mul, ← pow_add]
        congr 2
        omega
      _ ≤ _ := mul_le_mul_of_nonneg_right (g.exteriorDeficitCharge_sum_bound hd S hbudget) (pow_nonneg ht _)
  have hP : ∀ a b, ‖g.extensionGreen q z a b‖ ≤ (2 * C) * K a b :=
    g.finite_class_kernel_bound hd hG hbudget z q hz hq R hR small
  have hQ : ∀ a b, ‖g'.extensionGreen q z a b‖ ≤ (2 * C) * K a b :=
    g'.finite_class_kernel_bound hd hG (g.clearOutsideDeficit_budget S hbudget) z q hz hq R hR small
  have hprod := diagonal_kernel_product_bound (g.extensionGreen q z) (g'.extensionGreen q z) w K K
    (2 * C) (2 * C) hw (fun a b => pow_nonneg ht _) (by positivity) (by positivity)
    hP hQ i j _ hconv
  have hid := matrix_inverse_difference (g.extensionMatrix q z) (g'.extensionMatrix q z)
    (g.extensionMatrix_isUnit hd q z hz hq) (g'.extensionMatrix_isUnit hd q z hz hq)
  rw [g.clearOutsideDeficit_extensionMatrix_difference S q z, Matrix.mul_smul, Matrix.smul_mul] at hid
  have hentry := congrArg (fun M : Matrix V V ℂ => M i j) hid
  change g.extensionGreen q z i j - g'.extensionGreen q z i j =
    (-q) * (g.extensionGreen q z * Matrix.diagonal (fun v => (w v : ℂ)) * g'.extensionGreen q z) i j at hentry
  rw [hentry, norm_mul, norm_neg]
  exact (mul_le_mul_of_nonneg_left hprod (norm_nonneg q)).trans_eq (by dsimp [C, t]; ring)

/-- The exterior distance condition in (B.11) follows from literal
containment of the actual union of graph balls. -/
theorem clearOutsideDeficit_pairBall_localization_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.Connected) (hbudget : g.FiniteReferenceBudget) (S : Set V)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2)
    (i j : V) (r : ℕ) (hcontain : pairBallVertices g.graph i j r ⊆ S) :
    ‖g.extensionGreen q z i j - (g.clearOutsideDeficit S).extensionGreen q z i j‖ ≤
      4 * finiteExtraReferenceConstant d ^ 2 * ‖q‖ *
        (((finiteOmega d : ℝ) + 1) / ((d : ℝ) - 1)) * physicalTransfer d z ^ (2 * r) := by
  apply g.clearOutsideDeficit_localization_bound hd hG hbudget S z q hz hq R hR small i j r
  intro v hv
  have hfar : ∀ a : V, (g.graph.edist a v ≤ (r : ℕ∞) → v ∈ S) → r ≤ g.graph.dist a v := by
    intro a ha
    by_contra hr
    obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist a v
    have hlen : p.length ≤ r := by omega
    exact hv (ha ((SimpleGraph.edist_le p).trans (ENat.coe_le_coe.mpr hlen)))
  constructor
  · exact hfar i (fun h => hcontain (Or.inl h))
  · rw [show g.graph.dist v j = g.graph.dist j v from g.graph.dist_comm]
    exact hfar j (fun h => hcontain (Or.inr h))

end DeficientGraph
end LocalLaw
