import LocalLaw.OrdinaryComponentFeedback
import LocalLaw.FiniteReferenceModelBounds

/-!
# Actual deleted-component bounds when only exterior deficits vanish

This is the convention after clearing deficits outside the localization set;
interior deficits need not vanish. Euler charges and finite reference bounds
derive the actual deleted Green cap used for exceptional Schur terms.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance exteriorComponentsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) exteriorComponentMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

omit [DecidableEq V] in
theorem FiniteReferenceBudget.excess_le {g : DeficientGraph V d} (h : g.FiniteReferenceBudget) :
    graphExcess g.graph ≤ finiteOmega d := by
  rcases h with h | ⟨h, ⟨v, hv⟩⟩
  · omega
  · have hsum : 0 < ∑ x, g.deficit x := hv.trans_le
      (Finset.single_le_sum (fun x _ => Nat.zero_le _) (Finset.mem_univ v))
    omega

omit [DecidableEq V] in
theorem exterior_zero_component_complexity (g : DeficientGraph V d)
    (S : Set V) (hzero : ∀ v ∉ S, g.deficit v = 0)
    (hG : g.graph.Connected) (hS : (g.graph.induce S).Connected)
    (hbudget : g.FiniteReferenceBudget) (c : CutComponent g.graph S) :
    (∃ v, 0 < ((g.delete S).restrict c.supp).deficit v) ∧
      (∑ v, ((g.delete S).restrict c.supp).deficit v) +
        graphExcess ((g.delete S).restrict c.supp).graph ≤ finiteOmega d + 1 := by
  have hc := component_deficit_excess_bound g.graph S hG hS (finiteOmega d) hbudget.excess_le c
  simp only [g.deleted_component_deficit_of_exterior_zero S hzero c]
  change (∃ v : c.supp, 0 < cutDeficit g.graph S c v) ∧
    (∑ v : c.supp, cutDeficit g.graph S c v) + graphExcess (cutComponentGraph g.graph S c) ≤ finiteOmega d + 1
  simp only [graphExcess, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
    ← finsum_eq_sum_of_fintype] at hc ⊢
  exact ⟨hc.1, by omega⟩

/-- The cap is derived for actual deleted Green entries; only the actual
outside intrinsic diameter and the finite feedback budget remain explicit. -/
theorem exterior_zero_deleted_kernel_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (hzero : ∀ v ∉ S, g.deficit v = 0)
    (hG : g.graph.Connected) (hS : (g.graph.induce S).Connected) (hbudget : g.FiniteReferenceBudget)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ a b, (outsideGraph g.graph S).dist a b ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2)
    (a b : (Sᶜ : Set V)) :
    ‖(g.delete S).extensionGreen q z a b‖ ≤ 5 * finiteExtraReferenceConstant d := by
  by_cases hab : (outsideGraph g.graph S).connectedComponentMk a =
      (outsideGraph g.graph S).connectedComponentMk b
  · let c := (outsideGraph g.graph S).connectedComponentMk a
    let aa : c.supp := ⟨a, rfl⟩
    let bb : c.supp := ⟨b, hab.symm⟩
    let gc := (g.delete S).restrict c.supp
    have hgc : gc.graph.Connected := c.connected_induce_supp
    have hcomp := g.exterior_zero_component_complexity S hzero hG hS hbudget c
    have hdiam : ∀ i j, gc.graph.dist i j ≤ R := by
      intro i j
      change ((outsideGraph g.graph S).induce c.supp).dist i j ≤ R
      rw [isolated_induce_distance (outsideGraph g.graph S) c.supp ((g.delete S).component_cut c) i j]
      exact hR i.val j.val
    have hbound := gc.finiteOmega_extra_boundary_kernel_bound hd hgc hcomp.2 hcomp.1
      q z hz hq R hdiam small aa bb
    have heq := (g.delete S).component_extensionGreen hd c c.supp rfl q z hz hq
    change gc.extensionGreen q z = _ at heq
    rw [heq] at hbound
    exact hbound
  · rw [g.deleted_extensionGreen_component_zero hd S q z hz hq a b hab, norm_zero]
    exact mul_nonneg (by norm_num) ((by norm_num : (0 : ℝ) ≤ 1).trans
      (finiteExtraReferenceConstant_ge_one d hd))

end DeficientGraph
end LocalLaw
