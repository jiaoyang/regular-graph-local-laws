import LocalLaw.PendantDiameter
import LocalLaw.DeletedComponentBounds

/-!
# Actual ordinary deleted-component feedback in the full Green matrix

Exterior deficits vanish after the source clearing operation. Charge-zero
components therefore carry precisely the one-root cavity deficit, with actual
intrinsic diameter at most twice the ambient cap. The resulting feedback is
transferred through the genuine component inverse block.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance ordinaryComponentDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) ordinaryComponentMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

omit [DecidableEq V] in
theorem deleted_component_deficit_of_exterior_zero (g : DeficientGraph V d) (S : Set V)
    (hzero : ∀ v ∉ S, g.deficit v = 0) (c : CutComponent g.graph S) (v : c.supp) :
    ((g.delete S).restrict c.supp).deficit v = cutDeficit g.graph S c v := by
  change (g.delete S).deficit v.val = _
  rw [g.delete_deficit, hzero v.val.val v.val.property, zero_add, cutDeficit_degree_loss,
    cutComponent_degree_eq]
  rfl

/-- Ordinary outside components have the refined cavity self-energy error
in the actual full deleted Green matrix, without a residual hypothesis. -/
theorem ordinary_deleted_component_feedback (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (hzero : ∀ v ∉ S, g.deficit v = 0)
    (hG : g.graph.Connected) (hS : S.Nonempty)
    (c : CutComponent g.graph S) (hcharge : cutExcessCharge g.graph S c = 0)
    (e : CutBoundaryEdge g.graph S c)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (B : ℝ) (hB : ‖z‖ ≤ B)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * 3 * (3 / 2 : ℝ) * ((2 * R : ℕ) + 1 : ℝ) ≤ 1 / 2) :
    ‖(g.delete S).extensionGreen q z ⟨e.val.val.2, e.val.property.2.2⟩
        ⟨e.val.val.2, e.val.property.2.2⟩ - q‖ ≤
      ((2 * R : ℕ) + 1 : ℝ) * (Real.sqrt (B + 2) * Real.sqrt (spectralScale z) *
        ‖q - semicircleRoot z‖ + 128 * ‖q - semicircleRoot z‖ ^ 2) := by
  let gc := (g.delete S).restrict c.supp
  let root := cutAttachmentRoot g.graph S c e
  have htree : gc.graph.IsTree := (ordinary_cut_component_isTree g.graph S hG hS c hcharge).1
  have hdeficit : ∀ v, gc.deficit v = if v = root then 1 else 0 := by
    intro v
    rw [g.deleted_component_deficit_of_exterior_zero S hzero c v]
    exact ordinary_cut_root_deficit g.graph S hG hS c hcharge e v
  have hdiam : ∀ a b, gc.graph.dist a b ≤ 2 * R := by
    exact ordinary_cut_component_diameter g.graph hG S hS c hcharge R hR
  have hfeedback := gc.one_root_tree_spectral_feedback hd htree root hdeficit z q hz hq B hB
    (2 * R) hdiam small
  have heq := (g.delete S).component_extensionGreen hd c c.supp rfl q z hz hq
  change gc.extensionGreen q z = _ at heq
  rw [heq] at hfeedback
  exact hfeedback

end DeficientGraph
end LocalLaw
