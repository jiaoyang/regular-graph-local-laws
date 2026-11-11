import LocalLaw.FiniteDirichletGrafting

/-! # Literal simple graphs for the finite Dirichlet tree exhaustions -/

open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance dirichletGraftGraphDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def cavityTreeGraph (k : ℕ) : (n : ℕ) → SimpleGraph (CavityTreeIndex k n)
  | 0 => ⊥
  | n+1 =>
    { Adj := fun x y => match x,y with
        | Sum.inl _,Sum.inl _ => False
        | Sum.inl _,Sum.inr p => p.1=cavityTreeRoot k n
        | Sum.inr p,Sum.inl _ => p.1=cavityTreeRoot k n
        | Sum.inr p,Sum.inr q => p.2=q.2 ∧ (cavityTreeGraph k n).Adj p.1 q.1
      symm := by
        intro x y
        cases x with
        | inl x => cases y <;> simp only <;> tauto
        | inr p =>
          cases y with
          | inl y => simp only; tauto
          | inr q => exact fun h => ⟨h.1.symm,(cavityTreeGraph k n).symm h.2⟩
      loopless := by
        intro x
        cases x with
        | inl x => simp only; exact not_false
        | inr p => exact fun h => (cavityTreeGraph k n).loopless p.1 h.2 }

theorem cavityTreeMatrix_eq_spectral_adjacency (k n : ℕ) (α z : ℂ) :
    cavityTreeMatrix k α z 0 n=α • (cavityTreeGraph k n).adjMatrix ℂ-z • 1 := by
  induction n with
  | zero =>
    ext x y
    cases x
    cases y
    simp [cavityTreeMatrix,singletonScalarMatrix,cavityTreeGraph,SimpleGraph.adjMatrix_apply,
      Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
  | succ n ih =>
    ext x y
    cases x with
    | inl x =>
      cases x
      cases y with
      | inl y =>
        cases y
        simp [cavityTreeMatrix,rootBlockMatrix,singletonScalarMatrix,cavityTreeGraph,
          SimpleGraph.adjMatrix_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
      | inr p =>
        simp [cavityTreeMatrix,rootBlockMatrix,rootCouplingRow,branchRootCoupling,cavityTreeGraph,
          SimpleGraph.adjMatrix_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
    | inr p =>
      cases y with
      | inl y =>
        cases y
        simp [cavityTreeMatrix,rootBlockMatrix,rootCouplingColumn,branchRootCoupling,cavityTreeGraph,
          SimpleGraph.adjMatrix_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
      | inr q =>
        rcases p with ⟨p,s⟩
        rcases q with ⟨q,t⟩
        by_cases hst : s=t
        · subst t
          have hh := congrFun (congrFun ih p) q
          simpa only [cavityTreeMatrix,rootBlockMatrix,Matrix.fromBlocks_apply₂₂,identicalBranches,
            Matrix.blockDiagonal_apply,if_true,Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply,
            smul_eq_mul,Sum.inr.injEq,Prod.mk.injEq,and_true,true_and,cavityTreeGraph,SimpleGraph.adjMatrix_apply] using hh
        · simp [cavityTreeMatrix,rootBlockMatrix,identicalBranches,Matrix.blockDiagonal_apply,hst,
            cavityTreeGraph,SimpleGraph.adjMatrix_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]

namespace DeficientGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

def dirichletGraftGraph (g : DeficientGraph V d) (n : ℕ) :
    SimpleGraph (V ⊕ (CavityTreeIndex (d-1) n × g.treeExtensionSlots)) where
  Adj x y := match x,y with
    | Sum.inl v,Sum.inl w => g.graph.Adj v w
    | Sum.inl v,Sum.inr p => p.1=cavityTreeRoot (d-1) n ∧ p.2.1=v
    | Sum.inr p,Sum.inl v => p.1=cavityTreeRoot (d-1) n ∧ p.2.1=v
    | Sum.inr p,Sum.inr q => p.2=q.2 ∧ (cavityTreeGraph (d-1) n).Adj p.1 q.1
  symm := by
    intro x y
    cases x with
    | inl v =>
      cases y with
      | inl w => exact fun h => g.graph.symm h
      | inr p => exact id
    | inr p =>
      cases y with
      | inl v => exact id
      | inr q => exact fun h => ⟨h.1.symm,(cavityTreeGraph (d-1) n).symm h.2⟩
  loopless := by
    intro x
    cases x with
    | inl v => exact g.graph.loopless v
    | inr p => exact fun h => (cavityTreeGraph (d-1) n).loopless p.1 h.2

theorem dirichletGraftMatrix_eq_graph_spectral (g : DeficientGraph V d) (hd : 3≤d) (n : ℕ) (z : ℂ) :
    g.dirichletGraftMatrix n z=spectralMatrix (normalizedAdjacency (g.dirichletGraftGraph n) d) z := by
  have hα : normalizedCavityEdge (d-1)=(↑((Real.sqrt ((d:ℝ)-1))⁻¹):ℂ) := by
    unfold normalizedCavityEdge
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hnorm : normalizedAdjacency (g.dirichletGraftGraph n) d=
      normalizedCavityEdge (d-1) • (g.dirichletGraftGraph n).adjMatrix ℂ := by
    unfold normalizedAdjacency
    rw [hα]
  rw [hnorm]
  ext x y
  cases x with
  | inl v =>
    cases y with
    | inl w =>
      simp [dirichletGraftMatrix,dirichletGraftGraph,spectralMatrix,H,normalizedAdjacency,hα,
        SimpleGraph.adjMatrix_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
    | inr p =>
      simp [dirichletGraftMatrix,dirichletTailCoupling,dirichletGraftGraph,spectralMatrix,
        SimpleGraph.adjMatrix_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,mul_ite]
  | inr p =>
    cases y with
    | inl v =>
      simp [dirichletGraftMatrix,dirichletTailCoupling,dirichletGraftGraph,spectralMatrix,
        SimpleGraph.adjMatrix_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,mul_ite]
    | inr q =>
      rcases p with ⟨p,s⟩
      rcases q with ⟨q,t⟩
      by_cases hst : s=t
      · subst t
        have hh := congrFun (congrFun (cavityTreeMatrix_eq_spectral_adjacency (d-1) n
          (normalizedCavityEdge (d-1)) z) p) q
        simpa only [dirichletGraftMatrix,Matrix.fromBlocks_apply₂₂,dirichletTailMatrix,
          Matrix.blockDiagonal_apply,if_true,spectralMatrix,Matrix.sub_apply,Matrix.smul_apply,
          Matrix.one_apply,smul_eq_mul,dirichletGraftGraph,SimpleGraph.adjMatrix_apply,
          true_and,Sum.inr.injEq,Prod.mk.injEq,and_true] using hh
      · simp [dirichletGraftMatrix,dirichletTailMatrix,Matrix.blockDiagonal_apply,hst,
          dirichletGraftGraph,spectralMatrix,SimpleGraph.adjMatrix_apply,Matrix.smul_apply,
          smul_eq_mul,Matrix.one_apply]

/-- The reference is the limit of compressed resolvents of literal finite
simple graphs with ordinary Dirichlet boundary, on the actual core vertices. -/
theorem dirichletGraftGraph_core_resolvent_tendsto (g : DeficientGraph V d) (hd : 3≤d)
    (z : ℂ) (hz : 0<z.im) :
    Filter.Tendsto (fun n : ℕ => (green (normalizedAdjacency (g.dirichletGraftGraph n) d) z).toBlocks₁₁)
      Filter.atTop (𝓝 (g.extensionGreen (semicircleRoot z) z)) := by
  have h := g.dirichletGraftMatrix_core_tendsto hd z hz
  exact h.congr' (Filter.Eventually.of_forall (fun n => by
    rw [g.dirichletGraftMatrix_eq_graph_spectral hd n z]
    rfl))

end DeficientGraph
end LocalLaw
