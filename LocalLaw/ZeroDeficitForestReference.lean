import LocalLaw.DetachedEndpointModel
import LocalLaw.RootDeficitTreeKernel

/-! # The zero-deficit finite forest reference, independent of truncation shape -/

noncomputable section
namespace LocalLaw
local instance zeroDeficitForestDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

theorem extensionMatrix_zero_deficit_forest_form (g : DeficientGraph V d)
    (hzero : ∀ v,g.deficit v=0) (root : V) (m z : ℂ) :
    g.extensionMatrix m z=forestReferenceMatrix g.graph d root 0 m z := by
  ext i j
  simp only [extensionMatrix,forestReferenceMatrix,H,boundaryDiagonal,forestBoundaryCoefficient,
    boundaryCoefficient,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply,hzero,
    Nat.cast_zero,ite_self,sub_zero]

theorem extensionGreen_zero_deficit_forest_column (g : DeficientGraph V d) (hd : 3≤d)
    (hzero : ∀ v,g.deficit v=0) (hforest : g.graph.IsAcyclic)
    (root : V) (m z : ℂ) (hm : m^2+z*m+1=0) (hz : 0<z.im) (hmim : 0 ≤ m.im) (v : V) :
    g.extensionGreen m z v root=
      forestKernelColumn g.graph root (kestenMcKayTransform d m z) (-m*treeEdgeWeight d) v := by
  change (g.extensionMatrix m z)⁻¹ v root=_
  rw [g.extensionMatrix_zero_deficit_forest_form hzero root m z]
  exact forestReference_full_column g.graph hforest d hd root g.degree_le m z hm hz hmim v

theorem extensionGreen_zero_deficit_forest_diagonal (g : DeficientGraph V d) (hd : 3≤d)
    (hzero : ∀ v,g.deficit v=0) (hforest : g.graph.IsAcyclic)
    (root : V) (m z : ℂ) (hm : m^2+z*m+1=0) (hz : 0<z.im) (hmim : 0 ≤ m.im) :
    g.extensionGreen m z root root=kestenMcKayTransform d m z := by
  rw [g.extensionGreen_zero_deficit_forest_column hd hzero hforest root m z hm hz hmim,forestKernelColumn_root]

theorem extensionGreen_zero_deficit_forest_adjacent (g : DeficientGraph V d) (hd : 3≤d)
    (hzero : ∀ v,g.deficit v=0) (hforest : g.graph.IsAcyclic)
    (u v : V) (huv : g.graph.Adj u v)
    (m z : ℂ) (hm : m^2+z*m+1=0) (hz : 0<z.im) (hmim : 0 ≤ m.im) :
    g.extensionGreen m z u v=kestenMcKayTransform d m z*(-m*treeEdgeWeight d) := by
  rw [g.extensionGreen_zero_deficit_forest_column hd hzero hforest v m z hm hz hmim]
  simp only [forestKernelColumn,if_pos huv.reachable,SimpleGraph.dist_eq_one_iff_adj.mpr huv,pow_one]

end DeficientGraph
end LocalLaw
