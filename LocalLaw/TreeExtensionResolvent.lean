import LocalLaw.TreeExtensionTruncations
import LocalLaw.FiniteDirichletGreen
import LocalLaw.NeighborhoodDeletionComparison

/-! # The actual infinite tree-extension resolvent compresses to Ext(g,msc)

Both limits are genuine ordinary Dirichlet exhaustions: finite graph Schur
compression gives the algebraic reference, and the bounded self-adjoint ell2
operator gives its actual nonreal resolvent. Uniqueness of limits identifies
their complete core Green block.
-/

open scoped Topology
open Filter
noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
namespace LocalLaw
local instance treeExtensionResolventDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem normalizedAdjacency_reindex_iso {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (G : SimpleGraph I) (H : SimpleGraph J) (e : G ≃g H) (d : ℕ) :
    (normalizedAdjacency H d).submatrix e e=normalizedAdjacency G d := by
  ext i j
  simp only [normalizedAdjacency,Matrix.submatrix_apply,Matrix.smul_apply,SimpleGraph.adjMatrix_apply]
  rw [show H.Adj (e i) (e j)↔G.Adj i j from e.map_rel_iff']

namespace DeficientGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

def treeExtensionGreen (g : DeficientGraph V d) (hd : 1≤d) (z : ℂ) (i j : V) : ℂ :=
  g.treeExtension.infiniteGreen d (g.treeExtension_degree_le hd) z (Sum.inl i) (Sum.inl j)

theorem treeExtension_truncatedGreen_eq_graft (g : DeficientGraph V d) (hd : 3≤d)
    (n : ℕ) (z : ℂ) (hz : 0<z.im) (i j : V) :
    (g.treeExtension.finiteDirichletRestriction (g.treeExtensionTruncation n)).infiniteGreen d
      (fun v => (g.treeExtension.finiteDirichletRestriction_degree_le (g.treeExtensionTruncation n) v).trans
        (g.treeExtension_degree_le (by omega) v)) z (Sum.inl i) (Sum.inl j)=
      ((g.dirichletGraftMatrix n z)⁻¹).toBlocks₁₁ i j := by
  let S := g.treeExtensionTruncation n
  let e := g.treeExtensionTruncationIso n
  let G := g.treeExtension
  have hfinite := G.finiteDirichletRestriction_Green_eq_matrix S d (g.treeExtension_degree_le (by omega)) z hz
    (e (Sum.inl i)) (e (Sum.inl j))
  have hmatrix := normalizedAdjacency_reindex_iso (g.dirichletGraftGraph n) (G.induce (S:Set _)) e d
  have hgreen : (green (normalizedAdjacency (G.induce (S:Set _)) d) z).submatrix e e=
      green (normalizedAdjacency (g.dirichletGraftGraph n) d) z := by
    have h := green_reindex_equiv (normalizedAdjacency (G.induce (S:Set _)) d) e.toEquiv z
    change green ((normalizedAdjacency (G.induce (S:Set _)) d).submatrix e e) z=
      (green (normalizedAdjacency (G.induce (S:Set _)) d) z).submatrix e e at h
    exact h.symm.trans (congrArg (fun M => green M z) hmatrix)
  have hentry := congrFun (congrFun hgreen (Sum.inl i)) (Sum.inl j)
  have hphysical : green (normalizedAdjacency (g.dirichletGraftGraph n) d) z=(g.dirichletGraftMatrix n z)⁻¹ := by
    rw [g.dirichletGraftMatrix_eq_graph_spectral hd n z]
    rfl
  have hentry' : green (normalizedAdjacency (G.induce (S:Set _)) d) z (e (Sum.inl i)) (e (Sum.inl j))=
      ((g.dirichletGraftMatrix n z)⁻¹).toBlocks₁₁ i j := by
    rw [hphysical] at hentry
    exact hentry
  exact hfinite.trans hentry'

/-- Equation (2.11)'s asserted tree-extension identity, now for the actual
infinite graph and its bounded self-adjoint ell2 resolvent. -/
theorem treeExtensionGreen_eq_extensionGreen (g : DeficientGraph V d) (hd : 3≤d)
    (z : ℂ) (hz : 0<z.im) (i j : V) :
    g.treeExtensionGreen (by omega) z i j=g.extensionGreen (semicircleRoot z) z i j := by
  have hstrong := g.treeExtension.finiteDirichletRestriction_Green_tendsto g.treeExtensionTruncation
    g.treeExtensionTruncation_monotone g.treeExtensionTruncation_cover d (g.treeExtension_degree_le (by omega))
    z hz (Sum.inl i) (Sum.inl j)
  have hstrong' : Tendsto (fun n => ((g.dirichletGraftMatrix n z)⁻¹).toBlocks₁₁ i j) atTop
      (𝓝 (g.treeExtensionGreen (by omega) z i j)) :=
    hstrong.congr' (Filter.Eventually.of_forall (fun n => g.treeExtension_truncatedGreen_eq_graft hd n z hz i j))
  have heval : Continuous (fun M : Matrix V V ℂ => M i j) := by fun_prop
  have hfinite := heval.continuousAt.tendsto.comp (g.dirichletGraftMatrix_core_tendsto hd z hz)
  exact tendsto_nhds_unique hstrong' hfinite

end DeficientGraph
end LocalLaw
