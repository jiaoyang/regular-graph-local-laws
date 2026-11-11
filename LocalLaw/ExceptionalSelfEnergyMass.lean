import LocalLaw.ExceptionalSelfEnergy
import LocalLaw.ExteriorDeficitComponents

/-!
# Actual exceptional Schur coupling mass

Uniform deleted Green control and the actual exceptional attachment count
bound the complete exceptional matrix entry mass. No small-coupling estimate
is assumed. The intermediate rectangular matrix inequalities retain all
finite index sets explicitly.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance exceptionalMassDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Rectangular
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

omit [Fintype I] [Fintype K] in
theorem rectangular_sandwich_entry_bound (A : Matrix I J ℂ) (R : Matrix J J ℂ) (B : Matrix K J ℂ)
    (M : ℝ) (hR : ∀ a b, ‖R a b‖ ≤ M) (i : I) (j : K) :
    ‖(A * R * B.transpose) i j‖ ≤ M * (∑ a, ‖A i a‖) * (∑ b, ‖B j b‖) := by
  calc
    _ ≤ ∑ b, ∑ a, ‖A i a‖ * ‖R a b‖ * ‖B j b‖ := by
      change ‖∑ b, (A * R) i b * B j b‖ ≤ _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b _
      rw [Matrix.mul_apply, Finset.sum_mul]
      simpa only [norm_mul] using norm_sum_le Finset.univ (fun a => (A i a * R a b) * B j b)
    _ ≤ ∑ b, ∑ a, ‖A i a‖ * M * ‖B j b‖ := by
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hR a b) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum]
      ring

theorem rectangular_self_energy_mass_bound (A : Matrix I J ℂ) (R : Matrix J J ℂ)
    (M : ℝ) (hR : ∀ a b, ‖R a b‖ ≤ M) :
    (∑ i, ∑ j, ‖(A * R * A.transpose) i j‖) ≤ M * (∑ i, ∑ a, ‖A i a‖) ^ 2 := by
  apply le_trans (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
    (fun j _ => rectangular_sandwich_entry_bound A R A M hR i j)))
  let row : I → ℝ := fun i => ∑ a, ‖A i a‖
  change (∑ i, ∑ j, M * row i * row j) ≤ M * (∑ i, row i) ^ 2
  have heq : (∑ i, ∑ j, M * row i * row j) = M * (∑ i, row i) ^ 2 := by
    calc
      _ = ∑ i, M * row i * (∑ j, row j) := by simp only [Finset.mul_sum]
      _ = (∑ i, M * row i) * (∑ j, row j) := (Finset.sum_mul ..).symm
      _ = _ := by rw [← Finset.mul_sum]; ring
  exact heq.le

private theorem finite_indicator_sum {A : Type*} [Fintype A] (P : A → Prop) [DecidablePred P] (c : ℝ) :
    (∑ a, if P a then c else 0) = (Nat.card {a // P a} : ℝ) * c := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card, Fintype.card_subtype]

end Rectangular

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem exceptionalCutCoupling_row_mass (G : SimpleGraph V) (d : ℕ) (S : Set V) (u : S) :
    (∑ a : (Sᶜ : Set V), ‖exceptionalCutCoupling G d S u a‖) =
      (Nat.card (ExceptionalPortFiber G S u) : ℝ) * ‖treeEdgeWeight d‖ := by
  have h := finite_indicator_sum (fun a : (Sᶜ : Set V) => ¬ordinaryCutVertex G S a ∧ G.Adj u.val a.val)
    ‖treeEdgeWeight d‖
  calc
    _ = ∑ a : (Sᶜ : Set V), if ¬ordinaryCutVertex G S a ∧ G.Adj u.val a.val then ‖treeEdgeWeight d‖ else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : ¬ordinaryCutVertex G S a ∧ G.Adj u.val a.val <;> simp [exceptionalCutCoupling, ha]
    _ = _ := h

omit [DecidableEq V] in
theorem exceptionalCutCoupling_mass (G : SimpleGraph V) (d : ℕ) (S : Set V) :
    (∑ u : S, ∑ a : (Sᶜ : Set V), ‖exceptionalCutCoupling G d S u a‖) =
      (Nat.card (ExceptionalBoundaryEdge G S) : ℝ) * ‖treeEdgeWeight d‖ := by
  simp only [exceptionalCutCoupling_row_mass, ← Finset.sum_mul]
  congr 1
  have hcard := Nat.card_congr (exceptionalBoundaryPortEquiv G S)
  rw [Nat.card_sigma] at hcard
  exact_mod_cast hcard.symm

namespace DeficientGraph
variable {d : ℕ}

/-- The actual exceptional quadratic Schur term has mass proportional to
the square of its true attachment count, not the size of the local model. -/
theorem exceptional_coupling_mass_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (q z : ℂ) (M : ℝ)
    (hR : ∀ a b, ‖(g.delete S).extensionGreen q z a b‖ ≤ M) :
    (∑ u : S, ∑ v : S, ‖(exceptionalCutCoupling g.graph d S * (g.delete S).extensionGreen q z *
      (exceptionalCutCoupling g.graph d S).transpose) u v‖) ≤
      M * (Nat.card (ExceptionalBoundaryEdge g.graph S) : ℝ) ^ 2 / ((d : ℝ) - 1) := by
  have h := rectangular_self_energy_mass_bound (exceptionalCutCoupling g.graph d S)
    ((g.delete S).extensionGreen q z) M hR
  rw [exceptionalCutCoupling_mass, mul_pow, treeEdgeWeight_norm_sq d hd] at h
  exact h.trans_eq (by ring)

theorem unmatched_boundary_diagonal_eq (g : DeficientGraph V d) (S : Set V) :
    g.restrictionLossDiagonal S - Matrix.diagonal (fun u => (ordinaryCutCharge g.graph d S u : ℂ)) =
      Matrix.diagonal (fun u => (exceptionalCutCharge g.graph d S u : ℂ)) := by
  ext u v
  by_cases huv : u = v
  · subst v
    simp only [restrictionLossDiagonal, Matrix.sub_apply, Matrix.diagonal_apply_eq]
    rw [← Complex.ofReal_sub]
    congr 1
    have h := g.ordinary_add_exceptional_charge S u
    linarith
  · simp only [restrictionLossDiagonal, Matrix.sub_apply, Matrix.diagonal_apply_ne _ huv, sub_zero]

omit [DecidableEq V] in
theorem exceptional_charge_nonnegative (g : DeficientGraph V d) (hd : 3 ≤ d) (S : Set V) (u : S) :
    0 ≤ exceptionalCutCharge g.graph d S u := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  apply Finset.sum_nonneg
  intro a _
  change 0 ≤ if _ then 1 / ((d : ℝ) - 1) else 0
  split_ifs
  · exact div_nonneg (by norm_num) (by linarith)
  · exact le_rfl

theorem unmatched_boundary_scaled_mass (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (q : ℂ) :
    (∑ u : S, ∑ v : S, ‖(q • (g.restrictionLossDiagonal S -
      Matrix.diagonal (fun u => (ordinaryCutCharge g.graph d S u : ℂ)))) u v‖) =
      ‖q‖ * (Nat.card (ExceptionalBoundaryEdge g.graph S) : ℝ) / ((d : ℝ) - 1) := by
  rw [g.unmatched_boundary_diagonal_eq S]
  have hdiag : (∑ u : S, ∑ v : S, ‖Matrix.diagonal
      (fun x : S => (exceptionalCutCharge g.graph d S x : ℂ)) u v‖) =
      ∑ u : S, exceptionalCutCharge g.graph d S u := by
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.sum_eq_single u]
    · rw [Matrix.diagonal_apply_eq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (g.exceptional_charge_nonnegative hd S u)]
    · intro v _ hv
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hv), norm_zero]
    · simp
  calc
    _ = ‖q‖ * (∑ u : S, ∑ v : S, ‖Matrix.diagonal
        (fun x : S => (exceptionalCutCharge g.graph d S x : ℂ)) u v‖) := by
      simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Finset.mul_sum]
    _ = _ := by rw [hdiag, exceptionalCutCharge_sum]; ring

/-- The complete literal exceptional matrix has mass controlled by its
actual attachment count, including its unmatched boundary diagonal. -/
theorem exceptionalSelfEnergy_mass_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (q z : ℂ) (M : ℝ)
    (hR : ∀ a b, ‖(g.delete S).extensionGreen q z a b‖ ≤ M) :
    (∑ u : S, ∑ v : S, ‖g.exceptionalSelfEnergy S q z u v‖) ≤
      (M * (Nat.card (ExceptionalBoundaryEdge g.graph S) : ℝ) ^ 2 +
        ‖q‖ * (Nat.card (ExceptionalBoundaryEdge g.graph S) : ℝ)) / ((d : ℝ) - 1) := by
  let X := exceptionalCutCoupling g.graph d S * (g.delete S).extensionGreen q z *
    (exceptionalCutCoupling g.graph d S).transpose
  let Y := q • (g.restrictionLossDiagonal S - Matrix.diagonal (fun u => (ordinaryCutCharge g.graph d S u : ℂ)))
  have htriangle : (∑ u : S, ∑ v : S, ‖g.exceptionalSelfEnergy S q z u v‖) ≤
      (∑ u : S, ∑ v : S, ‖X u v‖) + (∑ u : S, ∑ v : S, ‖Y u v‖) := by
    calc
      _ ≤ ∑ u : S, ∑ v : S, (‖X u v‖ + ‖Y u v‖) := by
        apply Finset.sum_le_sum
        intro u _
        apply Finset.sum_le_sum
        intro v _
        exact norm_sub_le _ _
      _ = _ := by simp only [Finset.sum_add_distrib]
  have hcoupling := g.exceptional_coupling_mass_bound hd S q z M hR
  have hcharge := g.unmatched_boundary_scaled_mass hd S q
  exact htriangle.trans ((add_le_add hcoupling hcharge.le).trans_eq (by ring))

/-- Euler excess bounds the actual exceptional mass uniformly in the size
of the chosen neighborhood. -/
theorem exceptionalSelfEnergy_mass_le_excess (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (hG : g.graph.Connected) (hS : (g.graph.induce S).Connected)
    (ω : ℕ) (hω : graphExcess g.graph ≤ ω) (q z : ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hR : ∀ a b, ‖(g.delete S).extensionGreen q z a b‖ ≤ M) :
    (∑ u : S, ∑ v : S, ‖g.exceptionalSelfEnergy S q z u v‖) ≤
      (M * (2 * (ω : ℝ)) ^ 2 + ‖q‖ * (2 * (ω : ℝ))) / ((d : ℝ) - 1) := by
  apply (g.exceptionalSelfEnergy_mass_bound hd S q z M hR).trans
  have he : (Nat.card (ExceptionalBoundaryEdge g.graph S) : ℝ) ≤ 2 * (ω : ℝ) := by
    exact_mod_cast exceptionalBoundaryEdge_card_bound g.graph S hG hS ω hω
  have he0 : 0 ≤ (Nat.card (ExceptionalBoundaryEdge g.graph S) : ℝ) := Nat.cast_nonneg _
  have hsquare : (Nat.card (ExceptionalBoundaryEdge g.graph S) : ℝ) ^ 2 ≤ (2 * (ω : ℝ)) ^ 2 :=
    pow_le_pow_left₀ he0 he 2
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  exact div_le_div_of_nonneg_right
    (add_le_add (mul_le_mul_of_nonneg_left hsquare hM) (mul_le_mul_of_nonneg_left he (norm_nonneg q)))
    (by linarith)

/-- Actual finite reference bounds supply the deleted cap in the preceding
mass theorem; it is not a separate exceptional-coupling hypothesis. -/
theorem finite_class_exceptionalSelfEnergy_mass (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (hzero : ∀ v ∉ S, g.deficit v = 0)
    (hG : g.graph.Connected) (hS : (g.graph.induce S).Connected) (hbudget : g.FiniteReferenceBudget)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ a b, (outsideGraph g.graph S).dist a b ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2) :
    (∑ u : S, ∑ v : S, ‖g.exceptionalSelfEnergy S q z u v‖) ≤
      (5 * finiteExtraReferenceConstant d * (2 * (finiteOmega d : ℝ)) ^ 2 +
        ‖q‖ * (2 * (finiteOmega d : ℝ))) / ((d : ℝ) - 1) := by
  have hC : 0 ≤ finiteExtraReferenceConstant d :=
    le_trans (by norm_num) (finiteExtraReferenceConstant_ge_one d hd)
  exact g.exceptionalSelfEnergy_mass_le_excess hd S hG hS (finiteOmega d) hbudget.excess_le q z
    (5 * finiteExtraReferenceConstant d) (by positivity)
    (g.exterior_zero_deleted_kernel_bound hd S hzero hG hS hbudget q z hz hq R hR small)

end DeficientGraph
end LocalLaw
