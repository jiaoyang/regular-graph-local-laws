import LocalLaw.DeficientBudgetIso
import LocalLaw.ComponentDeletionBudget
import LocalLaw.DeficientMinorComparison

/-!
# Actual source deletion on the literal one-vertex minor index

The vertex type is exactly `{i // i != b}`, matching the matrix minor. Its
deficit records actual lost degree. The graph/deficit isomorphism to the
general set-deletion model transports the proved component reference budget.
-/

noncomputable section
namespace LocalLaw
local instance vertexDeletionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) vertexDeletionSingletonMemDecidable {A : Type*} (b : A) :
    DecidablePred (fun a => a ∈ ({b} : Set A)) := fun _ => Classical.propDecidable _
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

def deleteVertex (g : DeficientGraph V d) (b : V) : DeficientGraph {v : V // v ≠ b} d where
  graph := g.graph.induce {v | v ≠ b}
  deficit := fun v => g.deficit v.val + (g.graph.degree v.val - (g.graph.induce {v | v ≠ b}).degree v)
  degree_deficit_le := by
    intro v
    have hdeg := induced_degree_le g.graph {v | v ≠ b} v
    have hbudget := g.degree_deficit_le v.val
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hdeg hbudget ⊢
    omega

def deleteVertexIso (g : DeficientGraph V d) (b : V) :
    (g.deleteVertex b).graph ≃g (g.delete ({b} : Set V)).graph where
  toFun v := ⟨v.val, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using v.property⟩
  invFun v := ⟨v.val, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem deleteVertex_deficit_iso (g : DeficientGraph V d) (b : V) (v : {v : V // v ≠ b}) :
    (g.deleteVertex b).deficit v = (g.delete ({b} : Set V)).deficit (g.deleteVertexIso b v) := by
  have hdeg : (g.deleteVertex b).graph.degree v =
      (g.delete ({b} : Set V)).graph.degree (g.deleteVertexIso b v) := by
    have hh := Nat.card_congr ((g.deleteVertexIso b).mapNeighborSet v)
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    exact hh
  rw [g.delete_deficit]
  change g.deficit v.val + (g.graph.degree v.val - (g.deleteVertex b).graph.degree v) =
    g.deficit v.val + (g.graph.degree v.val - (g.delete ({b} : Set V)).graph.degree (g.deleteVertexIso b v))
  rw [hdeg]

theorem deleteVertex_extensionMatrix (g : DeficientGraph V d) (b : V) (q z : ℂ) :
    (g.deleteVertex b).extensionMatrix q z = (g.extensionMatrix q z).submatrix
      (Subtype.val : {v : V // v ≠ b} → V) (Subtype.val : {v : V // v ≠ b} → V) := by
  have hh := (g.delete ({b} : Set V)).extensionMatrix_iso (g.deleteVertex b) (g.deleteVertexIso b)
    (g.deleteVertex_deficit_iso b) q z
  rw [g.extensionMatrix_delete] at hh
  exact hh.symm

theorem deleteVertex_extensionGreen (g : DeficientGraph V d) (b : V) (q z : ℂ) :
    (g.deleteVertex b).extensionGreen q z = ((g.extensionMatrix q z).submatrix
      (Subtype.val : {v : V // v ≠ b} → V) (Subtype.val : {v : V // v ≠ b} → V))⁻¹ := by
  change ((g.deleteVertex b).extensionMatrix q z)⁻¹ = _
  rw [g.deleteVertex_extensionMatrix]

theorem deleteVertex_component_budget (g : DeficientGraph V d) (b : V)
    (hzero : ∀ v, g.deficit v = 0) (hbudget : g.ComponentReferenceBudget) :
    (g.deleteVertex b).ComponentFiniteReferenceBudget := by
  have hconn : (g.graph.induce ({b} : Set V)).Connected := by
    apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
    refine ⟨⟨b, rfl⟩, ?_⟩
    intro v
    have hv : v = (⟨b, rfl⟩ : ({b} : Set V)) := Subtype.ext v.property
    subst v
    exact SimpleGraph.Reachable.refl _
  exact (g.delete ({b} : Set V)).componentFiniteReferenceBudget_of_iso (g.deleteVertex b)
    (g.deleteVertexIso b) (g.deleteVertex_deficit_iso b)
    (g.componentwise_connected_deletion_budget hzero hbudget ({b} : Set V) hconn)

/-- The literal deleted matrix kernel cap is derived from a structural
reference class and finite feedback, without assuming any Green bound. -/
theorem deleteVertex_kernel_bound (g : DeficientGraph V d) (hd : 3 ≤ d) (b : V)
    (hzero : ∀ v, g.deficit v = 0) (hbudget : g.ComponentReferenceBudget)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ i j, (g.deleteVertex b).graph.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2)
    (i j : {v : V // v ≠ b}) :
    ‖((g.extensionMatrix q z).submatrix (Subtype.val : {v : V // v ≠ b} → V)
      (Subtype.val : {v : V // v ≠ b} → V))⁻¹ i j‖ ≤ 2 * finiteExtraReferenceConstant d := by
  have hh := (g.deleteVertex b).componentwise_finite_kernel_decay hd
    (g.deleteVertex_component_budget b hzero hbudget) q z hz hq R hR small i j
  rw [g.deleteVertex_extensionGreen] at hh
  have ht : physicalTransfer d z ≤ 1 := by
    nlinarith [physicalTransfer_sq_le_half d hd z, (physicalTransfer_pos d hd z)]
  have hC : 0 ≤ 2 * finiteExtraReferenceConstant d := mul_nonneg (by norm_num)
    ((by norm_num : (0 : ℝ) ≤ 1).trans (finiteExtraReferenceConstant_ge_one d hd))
  exact hh.trans (mul_le_of_le_one_right hC (pow_le_one₀ (physicalTransfer_pos d hd z).le ht))

/-- Singleton physical observation comparison with the deleted kernel bound
fully discharged by the actual finite reference class and degree geometry. -/
theorem embedded_singleton_minor_comparison_of_budget {W : Type} [Fintype W] [DecidableEq W]
    (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hzero : ∀ v, g.deficit v = 0) (hbudget : g.ComponentReferenceBudget)
    (H : Matrix W W ℂ) (hH : H.IsHermitian) (e : V ↪ W)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (b : V) (i : {v : V // v ≠ b})
    (R : ℕ) (hR : ∀ k l, (g.deleteVertex b).graph.dist k l ≤ R)
    (smallRef : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hcc : ‖green H z (e i.val) (e i.val) - g.extensionGreen q z i.val i.val‖ ≤ δ)
    (hcb : ‖green H z (e i.val) (e b) - g.extensionGreen q z i.val b‖ ≤ δ)
    (hbc : ‖green H z (e b) (e i.val) - g.extensionGreen q z b i.val‖ ≤ δ)
    (hbb : ‖green H z (e b) (e b) - g.extensionGreen q z b b‖ ≤ δ)
    (smallPivot : singletonPivotBudget d q z (2 * finiteExtraReferenceConstant d) * δ ≤ 1 / 2) :
    ‖green (deletedMatrix H (e b)) z
        ⟨e i.val, fun hh => i.property (e.injective hh)⟩
        ⟨e i.val, fun hh => i.property (e.injective hh)⟩ -
      (g.deleteVertex b).extensionGreen q z i i‖ ≤
        2 * (2 * finiteExtraReferenceConstant d * (d : ℝ) + 1) ^ 2 * δ := by
  have hC : 0 ≤ 2 * finiteExtraReferenceConstant d := mul_nonneg (by norm_num)
    ((by norm_num : (0 : ℝ) ≤ 1).trans (finiteExtraReferenceConstant_ge_one d hd))
  have hh := g.embedded_singleton_minor_comparison hd H hH e q z hz hq b i
    (2 * finiteExtraReferenceConstant d) δ hC hδ
    (g.deleteVertex_kernel_bound hd b hzero hbudget q z hz hq R hR smallRef)
    hcc hcb hbc hbb smallPivot
  rw [← g.deleteVertex_extensionGreen] at hh
  exact hh

end DeficientGraph
end LocalLaw
