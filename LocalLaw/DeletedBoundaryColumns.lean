import LocalLaw.ComponentCutGeometry

/-! # Constant model columns over the actual cut boundary

A fixed deleted target sees only its own actual outside component. The
boundary-label count is its cut multiplicity, bounded by the finite class.
The deleted kernel bound and its diameter hypothesis are derived.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance deletedBoundaryColumnsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) deletedBoundaryColumnsComponentDecidable {V : Type*}
    (G : SimpleGraph V) (C : G.ConnectedComponent) : DecidablePred (fun x => x∈C.supp) :=
  fun _ => Classical.propDecidable _
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d:ℕ}

theorem componentwise_deleted_boundary_column (g:DeficientGraph V d) (hd:3≤d)
    (hzero:∀v,g.deficit v=0) (hbase:g.ComponentReferenceBudget)
    (T:Set V) (hT:(g.graph.induce T).Connected) (R:ℕ) (hR:∀x y,g.graph.dist x y≤R)
    (q z:ℂ) (hz:0<z.im) (hq:0≤q.im)
    (small:‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*coreConvolutionConstant (finiteOmega d+1)*
      (((finiteOmega d+1)*(2*R+1):ℕ)+1:ℝ)≤1/2) (j:(Tᶜ:Set V)) :
    (∑α:BoundaryOrientedEdge g.graph T,‖(g.delete T).extensionGreen q z (boundaryOutsideVertex g.graph T α) j‖)≤
      2*finiteExtraReferenceConstant d*(finiteOmega d+1) := by
  let D := g.delete T
  let C := D.graph.connectedComponentMk j
  let f : BoundaryOrientedEdge g.graph T → ℝ := fun α => ‖D.extensionGreen q z (boundaryOutsideVertex g.graph T α) j‖
  have hC : 0≤finiteExtraReferenceConstant d := (by norm_num : (0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have hbudget := g.componentwise_connected_deletion_budget hzero hbase T hT
  have hdiam := g.componentwise_connected_deletion_diameter hzero hbase T hT R hR
  have ht : physicalTransfer d z≤1 := by
    have hh := physicalTransfer_sq_le_half d hd z
    have hp := (physicalTransfer_pos d hd z).le
    nlinarith
  have hkernel (a b:(Tᶜ:Set V)) : ‖D.extensionGreen q z a b‖≤2*finiteExtraReferenceConstant d :=
    (D.componentwise_finite_kernel_decay hd hbudget q z hz hq ((finiteOmega d+1)*(2*R+1)) hdiam small a b).trans
      (mul_le_of_le_one_right (by positivity) (pow_le_one₀ (physicalTransfer_pos d hd z).le ht))
  have hother (α:BoundaryOrientedEdge g.graph T) (hα:boundaryOutsideVertex g.graph T α∉C.supp) : f α=0 := by
    have hh := D.extensionGreen_zero_across_cut hd C.supp (D.component_cut C) q z hz hq j rfl
      (boundaryOutsideVertex g.graph T α) hα
    change ‖D.extensionGreen q z (boundaryOutsideVertex g.graph T α) j‖=0
    rw [(D.extensionGreen_isSymm q z).apply j (boundaryOutsideVertex g.graph T α),hh,norm_zero]
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun α:BoundaryOrientedEdge g.graph T => boundaryOutsideVertex g.graph T α∈C.supp) f
  have hzsum : (∑α:{α:BoundaryOrientedEdge g.graph T // boundaryOutsideVertex g.graph T α∉C.supp},f α.val)=0 :=
    Finset.sum_eq_zero (fun α _ => hother α.val α.property)
  rw [hzsum,add_zero] at hsplit
  calc
    _ = ∑α:CutBoundaryEdge g.graph T C,f α.val := hsplit.symm
    _ ≤ ∑_:CutBoundaryEdge g.graph T C,2*finiteExtraReferenceConstant d :=
      Finset.sum_le_sum (fun α _ => hkernel _ _)
    _ = (2*finiteExtraReferenceConstant d)*(cutMultiplicity g.graph T C:ℝ) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,cutMultiplicity,Nat.card_eq_fintype_card]
      ring
    _ ≤ _ := by
      simpa only [Nat.cast_add,Nat.cast_one] using
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (g.componentwise_cutMultiplicity_bound hzero hbase T hT C))
          (show 0≤2*finiteExtraReferenceConstant d by positivity)

end DeficientGraph
end LocalLaw
