import LocalLaw.BoundaryNearCounts
import LocalLaw.ComponentModel
import LocalLaw.ExteriorResolvent
import LocalLaw.DeletionStability

/-!
# Actual boundary Schur row bounds

The component attachment count controls the row sums of the Schur self-energy.
The kernel is the genuine inverse of the correctly deficient deleted model;
its vanishing between distinct components is derived from the graph cut.
These are the graph-specific bounds used in source Claim 5.6.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance boundarySchurDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section CutCounting
variable {V : Type*} [Fintype V]

/-- Literal incidence counting over one outside component. -/
theorem cut_component_incidence_sum (G : SimpleGraph V) (T : Set V)
    (C : CutComponent G T) :
    (∑ b : (Tᶜ : Set V), if b ∈ C.supp then
      (Nat.card {y : T // G.Adj y.val b.val} : ℝ) else 0) = cutMultiplicity G T C := by
  have hsum : (∑ b : (Tᶜ : Set V), if b ∈ C.supp then
      (Nat.card {y : T // G.Adj y.val b.val} : ℝ) else 0) =
      ∑ b : C.supp, (cutDeficit G T C b : ℝ) := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  rw [hsum, ← Nat.cast_sum, ← cutMultiplicity_eq_sum_deficit]

/-- The actual normalized coupling row is exactly the number of lost
neighbors times the edge normalization. -/
theorem normalized_cut_row_sum (G : SimpleGraph V) (d : ℕ) (T : Set V)
    (b : (Tᶜ : Set V)) :
    (∑ y : T, ‖normalizedAdjacency G d b.val y.val‖) =
      (Nat.card {y : T // G.Adj y.val b.val} : ℝ) /
        Real.sqrt ((d : ℝ) - 1) := by
  have hcount : ((Finset.univ.filter (fun y : T => G.Adj y.val b.val)).card : ℝ) =
      Nat.card {y : T // G.Adj y.val b.val} := by
    exact_mod_cast (Fintype.card_subtype (fun y : T => G.Adj y.val b.val)).symm.trans
      (Nat.card_eq_fintype_card).symm
  calc
    _ = ∑ y : T, if G.Adj y.val b.val then
        (Real.sqrt ((d : ℝ) - 1))⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      rw [normalizedAdjacency_norm]
      simp only [G.adj_comm]
    _ = _ := by rw [← Finset.sum_filter]; simp only [Finset.sum_const, nsmul_eq_mul,
      hcount, div_eq_mul_inv]

end CutCounting

section RowProducts
variable {I J K : Type*} [Fintype J] [Fintype K]

/-- The finite row-sum triangle inequality for a rectangular product. -/
theorem matrix_product_row_norm_sum (A : Matrix I K ℂ) (B : Matrix K J ℂ) (i : I) :
    (∑ j, ‖(A * B) i j‖) ≤ ∑ k, ‖A i k‖ * ∑ j, ‖B k j‖ := by
  calc
    _ ≤ ∑ j, ∑ k, ‖A i k‖ * ‖B k j‖ := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [Matrix.mul_apply, norm_mul] using
        norm_sum_le Finset.univ (fun k => A i k * B k j)
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]

end RowProducts

section CutKernel
variable {V : Type*} [Fintype V]

/-- Restricting a normalized coupling row can only decrease its absolute
sum. The degree estimate is the actual ambient graph degree. -/
theorem normalized_cut_left_row_bound (G : SimpleGraph V) (d : ℕ) (T : Set V)
    (hdegree : ∀ v, G.degree v ≤ d) (x : T) :
    (∑ a : (Tᶜ : Set V), ‖normalizedAdjacency G d x.val a.val‖) ≤
      (d : ℝ) / Real.sqrt ((d : ℝ) - 1) := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun v : V => v ∈ T)
    (fun v => ‖normalizedAdjacency G d x.val v‖)
  have hfirst : 0 ≤ ∑ y : T, ‖normalizedAdjacency G d x.val y.val‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hsub : (∑ a : (Tᶜ : Set V), ‖normalizedAdjacency G d x.val a.val‖) ≤
      ∑ v, ‖normalizedAdjacency G d x.val v‖ := by
    simp only [← finsum_eq_sum_of_fintype] at hsplit hfirst ⊢
    change (∑ᶠ y : T, ‖normalizedAdjacency G d x.val y.val‖) +
      (∑ᶠ a : (Tᶜ : Set V), ‖normalizedAdjacency G d x.val a.val‖) = _ at hsplit
    linarith
  rw [normalizedAdjacency_row_sum] at hsub
  exact hsub.trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr (hdegree x.val))
    (Real.sqrt_nonneg _))

/-- A component-supported kernel sees only the actual attachment edges of
that component when multiplied by the coupling back to the removed set. -/
theorem cut_kernel_coupling_row_bound (G : SimpleGraph V) (d : ℕ) (T : Set V)
    (K : Matrix (Tᶜ : Set V) (Tᶜ : Set V) ℂ) (C κ : ℝ) (hC : 0 ≤ C)
    (hkernel : ∀ a b, ‖K a b‖ ≤ C)
    (hzero : ∀ a b, (outsideGraph G T).connectedComponentMk a ≠
      (outsideGraph G T).connectedComponentMk b → K a b = 0)
    (hattach : ∀ c : CutComponent G T, (cutMultiplicity G T c : ℝ) ≤ κ)
    (a : (Tᶜ : Set V)) :
    (∑ y : T, ‖(K * (normalizedAdjacency G d).submatrix
      (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V)) a y‖) ≤
      C * κ / Real.sqrt ((d : ℝ) - 1) := by
  let c := (outsideGraph G T).connectedComponentMk a
  let lost := fun b : (Tᶜ : Set V) => (Nat.card {y : T // G.Adj y.val b.val} : ℝ)
  have hs : 0 ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hpoint (b : (Tᶜ : Set V)) :
      ‖K a b‖ * lost b ≤ C * (if b ∈ c.supp then lost b else 0) := by
    by_cases hb : b ∈ c.supp
    · rw [if_pos hb]
      exact mul_le_mul_of_nonneg_right (hkernel a b) (Nat.cast_nonneg _)
    · have hne : (outsideGraph G T).connectedComponentMk a ≠
          (outsideGraph G T).connectedComponentMk b := by
        intro hh
        exact hb hh.symm
      rw [hzero a b hne, norm_zero, zero_mul, if_neg hb, mul_zero]
  have hsum : (∑ b, ‖K a b‖ * lost b) ≤ C * κ := by
    calc
      _ ≤ ∑ b, C * (if b ∈ c.supp then lost b else 0) :=
        Finset.sum_le_sum (fun b _ => hpoint b)
      _ = C * (cutMultiplicity G T c : ℝ) := by
        rw [← Finset.mul_sum]
        congr 1
        exact cut_component_incidence_sum G T c
      _ ≤ C * κ := mul_le_mul_of_nonneg_left (hattach c) hC
  calc
    _ ≤ ∑ b, ‖K a b‖ * ∑ y : T,
        ‖(normalizedAdjacency G d).submatrix
          (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V) b y‖ :=
      matrix_product_row_norm_sum _ _ a
    _ = (∑ b, ‖K a b‖ * lost b) * (Real.sqrt ((d : ℝ) - 1))⁻¹ := by
      simp only [Matrix.submatrix_apply, normalized_cut_row_sum, Finset.sum_mul,
        div_eq_mul_inv, mul_assoc, lost]
    _ ≤ (C * κ) * (Real.sqrt ((d : ℝ) - 1))⁻¹ := mul_le_mul_of_nonneg_right hsum hs
    _ = _ := (div_eq_mul_inv _ _).symm

end CutKernel

namespace DeficientGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

theorem extensionMatrix_cross12 (g : DeficientGraph V d) (T : Set V) (q z : ℂ) :
    (g.extensionMatrix q z).submatrix (Subtype.val : T → V) (Subtype.val : (Tᶜ : Set V) → V) =
      g.H.submatrix (Subtype.val : T → V) (Subtype.val : (Tᶜ : Set V) → V) := by
  ext i j
  have hij : i.val ≠ j.val := fun hh => j.property (hh ▸ i.property)
  simp [extensionMatrix, boundaryMatrix, spectralMatrix, boundaryDiagonal,
    Matrix.diagonal_apply, Matrix.one_apply, hij]

theorem extensionMatrix_cross21 (g : DeficientGraph V d) (T : Set V) (q z : ℂ) :
    (g.extensionMatrix q z).submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V) =
      g.H.submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V) := by
  ext i j
  have hij : i.val ≠ j.val := fun hh => i.property (hh.symm ▸ j.property)
  simp [extensionMatrix, boundaryMatrix, spectralMatrix, boundaryDiagonal,
    Matrix.diagonal_apply, Matrix.one_apply, hij]

theorem extensionGreen_isSymm (g : DeficientGraph V d) (q z : ℂ) :
    (g.extensionGreen q z).IsSymm := by
  have hH : g.H.transpose = g.H := by
    ext i j
    simp [H, normalizedAdjacency, SimpleGraph.adjMatrix_apply, g.graph.adj_comm]
  have hA : (g.extensionMatrix q z).transpose = g.extensionMatrix q z := by
    simp only [extensionMatrix, boundaryMatrix, spectralMatrix, boundaryDiagonal,
      Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.diagonal_transpose, hH]
  change ((g.extensionMatrix q z)⁻¹).transpose = (g.extensionMatrix q z)⁻¹
  rw [Matrix.transpose_nonsing_inv, hA]

theorem retained_extensionGreen_inverse_isSymm (g : DeficientGraph V d)
    (T : Set V) (q z : ℂ) :
    (((g.extensionGreen q z).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹).IsSymm := by
  have hs := (g.extensionGreen_isSymm q z).submatrix (Subtype.val : T → V)
  change (((g.extensionGreen q z).submatrix _ _)⁻¹).transpose = _
  rw [Matrix.transpose_nonsing_inv, hs]

/-- A row bound for the actual finite extension operator, with the deficit
coefficient bounded by two from its degree budget. -/
theorem extensionMatrix_row_sum_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (q z : ℂ) (x : V) :
    (∑ y, ‖g.extensionMatrix q z x y‖) ≤
      (d : ℝ) / Real.sqrt ((d : ℝ) - 1) + ‖z‖ + 2 * ‖q‖ := by
  have hmatrix : g.extensionMatrix q z = g.H -
      Matrix.diagonal (fun v => z + q * (g.boundaryCoefficient v : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [extensionMatrix, boundaryMatrix, spectralMatrix, boundaryDiagonal,
        Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq, Matrix.one_apply,
        Pi.smul_apply, smul_eq_mul, if_pos rfl, ite_true, mul_one]
      ring
    · simp [extensionMatrix, boundaryMatrix, spectralMatrix, boundaryDiagonal,
        Matrix.diagonal_apply, Matrix.one_apply, hij]
  have hcoeff : ‖(g.boundaryCoefficient x : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (g.boundaryCoefficient_nonnegative hd x)]
    exact g.boundaryCoefficient_le_two hd x
  rw [hmatrix, row_sum_sub_diagonal g.H (normalizedAdjacency_zero_diagonal g.graph d)]
  simp only [H, normalizedAdjacency_row_sum]
  have hdegree : (g.graph.degree x : ℝ) / Real.sqrt ((d : ℝ) - 1) ≤
      (d : ℝ) / Real.sqrt ((d : ℝ) - 1) :=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr (g.degree_le x)) (Real.sqrt_nonneg _)
  have hdiag : ‖z + q * (g.boundaryCoefficient x : ℂ)‖ ≤ ‖z‖ + 2 * ‖q‖ := by
    calc
      _ ≤ ‖z‖ + ‖q * (g.boundaryCoefficient x : ℂ)‖ := norm_add_le _ _
      _ = ‖z‖ + ‖q‖ * ‖(g.boundaryCoefficient x : ℂ)‖ := by rw [norm_mul]
      _ ≤ ‖z‖ + 2 * ‖q‖ := by nlinarith [norm_nonneg q]
  linarith

theorem extensionMatrix_principal_row_sum_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (T : Set V) (q z : ℂ) (x : T) :
    (∑ y : T, ‖g.extensionMatrix q z x.val y.val‖) ≤
      (d : ℝ) / Real.sqrt ((d : ℝ) - 1) + ‖z‖ + 2 * ‖q‖ := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun v : V => v ∈ T)
    (fun v => ‖g.extensionMatrix q z x.val v‖)
  have hsecond : 0 ≤ ∑ y : (Tᶜ : Set V), ‖g.extensionMatrix q z x.val y.val‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hfull := g.extensionMatrix_row_sum_bound hd q z x.val
  simp only [← finsum_eq_sum_of_fintype] at hsplit hsecond hfull ⊢
  change (∑ᶠ y : T, ‖g.extensionMatrix q z x.val y.val‖) +
    (∑ᶠ y : (Tᶜ : Set V), ‖g.extensionMatrix q z x.val y.val‖) = _ at hsplit
  linarith

/-- The actual deleted extension inverse vanishes between distinct outside
components. This support property is derived, rather than imposed on a model. -/
theorem deleted_extensionGreen_component_zero (g : DeficientGraph V d) (hd : 3 ≤ d)
    (T : Set V) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (a b : (Tᶜ : Set V))
    (hne : (outsideGraph g.graph T).connectedComponentMk a ≠
      (outsideGraph g.graph T).connectedComponentMk b) :
    (g.delete T).extensionGreen q z a b = 0 := by
  let c := (outsideGraph g.graph T).connectedComponentMk a
  have hb : b ∉ c.supp := by
    intro hh
    exact hne hh.symm
  exact (g.delete T).extensionGreen_zero_across_cut hd c.supp
    ((g.delete T).component_cut c) q z hz hq a rfl b hb

/-- The genuine deleted inverse and Euler attachment accounting imply the
uniform coupling row estimate used in the Schur complement. -/
theorem deleted_extensionGreen_coupling_row_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (T : Set V) (hconn : g.graph.Connected) (hT : (g.graph.induce T).Connected)
    (ω : ℕ) (hbudget : graphExcess g.graph ≤ ω)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (C : ℝ) (hC : 0 ≤ C)
    (hkernel : ∀ a b, ‖(g.delete T).extensionGreen q z a b‖ ≤ C)
    (a : (Tᶜ : Set V)) :
    (∑ y : T, ‖((g.delete T).extensionGreen q z * g.H.submatrix
      (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V)) a y‖) ≤
      C * ((ω : ℝ) + 1) / Real.sqrt ((d : ℝ) - 1) := by
  apply cut_kernel_coupling_row_bound g.graph d T _ C ((ω : ℝ) + 1) hC hkernel
    (g.deleted_extensionGreen_component_zero hd T q z hz hq)
  intro c
  exact_mod_cast component_cut_multiplicity_bound g.graph T hconn hT ω hbudget c

/-- Claim 5.6's Schur self-energy row bound. The factor counts actual
attachment edges of an outside component, with no factor `card T`. -/
theorem deleted_extensionGreen_self_energy_row_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (T : Set V) (hconn : g.graph.Connected) (hT : (g.graph.induce T).Connected)
    (ω : ℕ) (hbudget : graphExcess g.graph ≤ ω)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (C : ℝ) (hC : 0 ≤ C)
    (hkernel : ∀ a b, ‖(g.delete T).extensionGreen q z a b‖ ≤ C)
    (x : T) :
    (∑ y : T, ‖(g.H.submatrix (Subtype.val : T → V) (Subtype.val : (Tᶜ : Set V) → V) *
      (g.delete T).extensionGreen q z * g.H.submatrix
        (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V)) x y‖) ≤
      (d : ℝ) * C * ((ω : ℝ) + 1) / ((d : ℝ) - 1) := by
  let L := C * ((ω : ℝ) + 1) / Real.sqrt ((d : ℝ) - 1)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hcoupling := g.deleted_extensionGreen_coupling_row_bound hd T hconn hT ω hbudget
    q z hz hq C hC hkernel
  have hrow := normalized_cut_left_row_bound g.graph d T g.degree_le x
  have hk : 0 ≤ (d : ℝ) - 1 := by
    have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
    linarith
  calc
    _ = ∑ y : T, ‖(g.H.submatrix (Subtype.val : T → V) (Subtype.val : (Tᶜ : Set V) → V) *
        ((g.delete T).extensionGreen q z * g.H.submatrix
          (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V))) x y‖ := by
      rw [Matrix.mul_assoc]
    _ ≤ ∑ a : (Tᶜ : Set V), ‖g.H x.val a.val‖ *
        ∑ y : T, ‖((g.delete T).extensionGreen q z * g.H.submatrix
          (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V)) a y‖ :=
      matrix_product_row_norm_sum _ _ x
    _ ≤ ∑ a : (Tᶜ : Set V), ‖g.H x.val a.val‖ * L := by
      exact Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hcoupling a) (norm_nonneg _))
    _ = (∑ a : (Tᶜ : Set V), ‖g.H x.val a.val‖) * L := (Finset.sum_mul ..).symm
    _ ≤ ((d : ℝ) / Real.sqrt ((d : ℝ) - 1)) * L :=
      mul_le_mul_of_nonneg_right hrow hL
    _ = (d : ℝ) * C * ((ω : ℝ) + 1) / ((d : ℝ) - 1) := by
      dsimp [L]
      rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hk]
      ring

/-- Actual Claim 5.6, with all Schur units and component support discharged.
Its constant depends on the component kernel bound, never on the cut size. -/
theorem retained_extensionGreen_inverse_row_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (T : Set V) (hconn : g.graph.Connected) (hT : (g.graph.induce T).Connected)
    (ω : ℕ) (hbudget : graphExcess g.graph ≤ ω)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (C : ℝ) (hC : 0 ≤ C)
    (hkernel : ∀ a b, ‖(g.delete T).extensionGreen q z a b‖ ≤ C) (x : T) :
    (∑ y : T, ‖((g.extensionGreen q z).submatrix
      (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ x y‖) ≤
      (d : ℝ) / Real.sqrt ((d : ℝ) - 1) + ‖z‖ + 2 * ‖q‖ +
        (d : ℝ) * C * ((ω : ℝ) + 1) / ((d : ℝ) - 1) := by
  have hdeleted := (g.delete T).extensionMatrix_isUnit hd q z hz hq
  rw [g.extensionMatrix_delete] at hdeleted
  have hschur := retained_principal_inverse T (g.extensionMatrix q z)
    (g.extensionMatrix_isUnit hd q z hz hq) hdeleted
  change ((g.extensionGreen q z).submatrix _ _)⁻¹ = _ at hschur
  rw [g.extensionMatrix_cross12, g.extensionMatrix_cross21, ← g.extensionMatrix_delete] at hschur
  have hself := g.deleted_extensionGreen_self_energy_row_bound hd T hconn hT ω hbudget
    q z hz hq C hC hkernel x
  have hop := g.extensionMatrix_principal_row_sum_bound hd T q z x
  rw [hschur]
  calc
    _ ≤ ∑ y : T, (‖g.extensionMatrix q z x.val y.val‖ +
      ‖(g.H.submatrix (Subtype.val : T → V) (Subtype.val : (Tᶜ : Set V) → V) *
        (g.delete T).extensionGreen q z * g.H.submatrix
          (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V)) x y‖) := by
      apply Finset.sum_le_sum
      intro y _
      exact norm_sub_le _ _
    _ = _ + _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add hop hself

/-- Symmetry transfers the derived Schur row bound to columns. -/
theorem retained_extensionGreen_inverse_column_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (T : Set V) (hconn : g.graph.Connected) (hT : (g.graph.induce T).Connected)
    (ω : ℕ) (hbudget : graphExcess g.graph ≤ ω)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (C : ℝ) (hC : 0 ≤ C)
    (hkernel : ∀ a b, ‖(g.delete T).extensionGreen q z a b‖ ≤ C) (y : T) :
    (∑ x : T, ‖((g.extensionGreen q z).submatrix
      (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ x y‖) ≤
      (d : ℝ) / Real.sqrt ((d : ℝ) - 1) + ‖z‖ + 2 * ‖q‖ +
        (d : ℝ) * C * ((ω : ℝ) + 1) / ((d : ℝ) - 1) := by
  have hrow := g.retained_extensionGreen_inverse_row_bound hd T hconn hT ω hbudget
    q z hz hq C hC hkernel y
  convert hrow using 1
  apply Finset.sum_congr rfl
  intro x _
  have hs := congrFun (congrFun (g.retained_extensionGreen_inverse_isSymm T q z) y) x
  exact congrArg norm hs

end DeficientGraph

end LocalLaw
