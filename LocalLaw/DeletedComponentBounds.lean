import LocalLaw.BoundarySchurRows

/-!
# Derived bounds for the actual deleted local components

For a connected zero-deficit source graph, deleting a connected set creates
the literal lost-neighbor deficit. Euler counting gives a positive deficit
and complexity at most one above the original excess. The constructed finite
reference threshold and boundary stability therefore bound the genuine
deleted inverse without assuming a kernel estimate.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance deletedComponentDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) deletedComponentMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

omit [DecidableEq V] in
theorem deleted_component_deficit_eq_cutDeficit (g : DeficientGraph V d)
    (hzero : ∀ v, g.deficit v = 0) (T : Set V) (c : CutComponent g.graph T)
    (v : c.supp) :
    ((g.delete T).restrict c.supp).deficit v = cutDeficit g.graph T c v := by
  change (g.delete T).deficit v.val = _
  rw [g.delete_deficit, hzero, zero_add, cutDeficit_degree_loss,
    cutComponent_degree_eq]
  rfl

omit [DecidableEq V] in
/-- The inherited deficient component satisfies the extra-deficit reference
budget, as a consequence of the original graph excess. -/
theorem deleted_component_complexity (g : DeficientGraph V d)
    (hzero : ∀ v, g.deficit v = 0) (T : Set V)
    (hconn : g.graph.Connected) (hT : (g.graph.induce T).Connected)
    (ω : ℕ) (hbudget : graphExcess g.graph ≤ ω) (c : CutComponent g.graph T) :
    (∃ v, 0 < ((g.delete T).restrict c.supp).deficit v) ∧
      (∑ v, ((g.delete T).restrict c.supp).deficit v) +
        graphExcess ((g.delete T).restrict c.supp).graph ≤ ω + 1 := by
  have hc := component_deficit_excess_bound g.graph T hconn hT ω hbudget c
  simp only [g.deleted_component_deficit_eq_cutDeficit hzero T c]
  change (∃ v : c.supp, 0 < cutDeficit g.graph T c v) ∧
    (∑ v : c.supp, cutDeficit g.graph T c v) + graphExcess (cutComponentGraph g.graph T c) ≤ ω + 1
  simp only [graphExcess, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
    ← finsum_eq_sum_of_fintype] at hc ⊢
  exact ⟨hc.1, by omega⟩

/-- A genuine extra-deficit model remains uniformly bounded under the
proved diameter-scale perturbation hypothesis. -/
theorem finiteOmega_extra_boundary_kernel_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hconn : g.graph.Connected)
    (hbudget : (∑ v, g.deficit v) + graphExcess g.graph ≤ finiteOmega d + 1)
    (hpositive : ∃ v, 0 < g.deficit v) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2)
    (i j : V) :
    ‖g.extensionGreen q z i j‖ ≤ 5 * finiteExtraReferenceConstant d := by
  let C := finiteExtraReferenceConstant d
  let C0 := coreConvolutionConstant (finiteOmega d + 1)
  let δ := ‖q - semicircleRoot z‖
  have hC : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have hC0 : 0 ≤ C0 := coreConvolutionConstant_nonnegative _
  have hδ : 0 ≤ δ := norm_nonneg _
  have hnorm := (g.finiteOmega_extra_reference_bounds hd hconn hbudget hpositive z hz).1 i j
  have ht : ‖-semicircleRoot z * treeEdgeWeight d‖ ≤ 1 :=
    (cycle_transfer_norm_le_three_quarters d hd _ (semicircleRoot_norm_le_one z)).trans (by norm_num)
  have href : ‖g.extensionGreen (semicircleRoot z) z i j‖ ≤ C := by
    exact hnorm.trans (mul_le_of_le_one_right hC (pow_le_one₀ (norm_nonneg _) ht))
  have hdiff := g.finiteOmega_extra_boundary_uniform_stability hd hconn hbudget hpositive
    z q hz hq R hR small i j
  have hsmall : (8 * C ^ 2 * C0 * δ) * ((R : ℝ) + 1) ≤ 4 * C := by
    have hh := mul_le_mul_of_nonneg_left small (show 0 ≤ 8 * C by positivity)
    convert hh using 1 <;> dsimp [C, C0, δ] <;> ring
  have hcorr : 8 * C ^ 2 * C0 * δ ≤ 4 * C := by
    have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    have hprod : 0 ≤ 8 * C ^ 2 * C0 * δ := by positivity
    nlinarith
  calc
    _ ≤ ‖g.extensionGreen q z i j - g.extensionGreen (semicircleRoot z) z i j‖ +
        ‖g.extensionGreen (semicircleRoot z) z i j‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (g.extensionGreen q z i j - g.extensionGreen (semicircleRoot z) z i j)
        (g.extensionGreen (semicircleRoot z) z i j)
    _ ≤ (8 * C ^ 2 * C0 * δ) + C := add_le_add hdiff href
    _ ≤ 5 * C := by linarith

/-- All entries of the actual deleted model are bounded by a degree-only
constant. Every component hypothesis is proved from the connected cut. -/
theorem deleted_extensionGreen_kernel_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hzero : ∀ v, g.deficit v = 0) (T : Set V)
    (hconn : g.graph.Connected) (hT : (g.graph.induce T).Connected)
    (hbudget : graphExcess g.graph ≤ finiteOmega d)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ a b, (outsideGraph g.graph T).dist a b ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2)
    (a b : (Tᶜ : Set V)) :
    ‖(g.delete T).extensionGreen q z a b‖ ≤ 5 * finiteExtraReferenceConstant d := by
  by_cases hab : (outsideGraph g.graph T).connectedComponentMk a =
      (outsideGraph g.graph T).connectedComponentMk b
  · let c := (outsideGraph g.graph T).connectedComponentMk a
    let aa : c.supp := ⟨a, rfl⟩
    let bb : c.supp := ⟨b, hab.symm⟩
    let gc := (g.delete T).restrict c.supp
    have hgc : gc.graph.Connected := SimpleGraph.ConnectedComponent.connected_induce_supp c
    have hcomp := g.deleted_component_complexity hzero T hconn hT (finiteOmega d) hbudget c
    have hdiam : ∀ i j, gc.graph.dist i j ≤ R := by
      intro i j
      change ((outsideGraph g.graph T).induce c.supp).dist i j ≤ R
      rw [isolated_induce_distance (outsideGraph g.graph T) c.supp
        ((g.delete T).component_cut c) i j]
      exact hR i.val j.val
    have hbound := gc.finiteOmega_extra_boundary_kernel_bound hd hgc hcomp.2 hcomp.1
      q z hz hq R hdiam small aa bb
    have heq := (g.delete T).component_extensionGreen hd c c.supp rfl q z hz hq
    change gc.extensionGreen q z = _ at heq
    rw [heq] at hbound
    exact hbound
  · rw [g.deleted_extensionGreen_component_zero hd T q z hz hq a b hab, norm_zero]
    exact mul_nonneg (by norm_num) ((by norm_num : (0 : ℝ) ≤ 1).trans
      (finiteExtraReferenceConstant_ge_one d hd))

/-- A fixed degree-only Schur constant on a bounded spectral domain. -/
def boundarySchurConstant (d : ℕ) (B : ℝ) : ℝ :=
  (d : ℝ) / Real.sqrt ((d : ℝ) - 1) + B + 4 +
    (d : ℝ) * (5 * finiteExtraReferenceConstant d) * ((finiteOmega d : ℝ) + 1) /
      ((d : ℝ) - 1)

/-- Source Claim 5.6 for an actual zero-deficit graph and a connected cut.
Every reference bound and every outside-component budget is a conclusion
of the finite-threshold theory, rather than an analytic premise. -/
theorem zero_deficit_retained_inverse_bounds (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hzero : ∀ v, g.deficit v = 0) (T : Set V)
    (hconn : g.graph.Connected) (hT : (g.graph.induce T).Connected)
    (hbudget : graphExcess g.graph ≤ finiteOmega d)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (B : ℝ) (hB : ‖z‖ ≤ B) (hqnear : ‖q - semicircleRoot z‖ ≤ 1)
    (R : ℕ) (hR : ∀ a b, (outsideGraph g.graph T).dist a b ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2) :
    (∀ x : T, (∑ y : T, ‖((g.extensionGreen q z).submatrix
      (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ x y‖) ≤ boundarySchurConstant d B) ∧
    (∀ y : T, (∑ x : T, ‖((g.extensionGreen q z).submatrix
      (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ x y‖) ≤ boundarySchurConstant d B) := by
  have hC : 0 ≤ 5 * finiteExtraReferenceConstant d := mul_nonneg (by norm_num)
    ((by norm_num : (0 : ℝ) ≤ 1).trans (finiteExtraReferenceConstant_ge_one d hd))
  have hkernel := g.deleted_extensionGreen_kernel_bound hd hzero T hconn hT hbudget
    q z hz hq R hR small
  have hqnorm : ‖q‖ ≤ 2 := by
    have hh : ‖q‖ ≤ ‖q - semicircleRoot z‖ + ‖semicircleRoot z‖ := by
      simpa only [sub_add_cancel] using norm_add_le (q - semicircleRoot z) (semicircleRoot z)
    linarith [semicircleRoot_norm_le_one z]
  have hnumeric : (d : ℝ) / Real.sqrt ((d : ℝ) - 1) + ‖z‖ + 2 * ‖q‖ +
      (d : ℝ) * (5 * finiteExtraReferenceConstant d) * ((finiteOmega d : ℝ) + 1) /
        ((d : ℝ) - 1) ≤ boundarySchurConstant d B := by
    unfold boundarySchurConstant
    linarith
  constructor
  · intro x
    exact (g.retained_extensionGreen_inverse_row_bound hd T hconn hT (finiteOmega d) hbudget
      q z hz hq _ hC hkernel x).trans hnumeric
  · intro y
    exact (g.retained_extensionGreen_inverse_column_bound hd T hconn hT (finiteOmega d) hbudget
      q z hz hq _ hC hkernel y).trans hnumeric

end DeficientGraph
end LocalLaw
