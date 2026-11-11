import LocalLaw.RestrictedTreePatchReference
import LocalLaw.ForestVacuumSquareSum
import LocalLaw.ComponentRestrictionBudget

/-! # Tree-patch values at an approximate self-consistent boundary parameter -/

noncomputable section
namespace LocalLaw
local instance restrictedTreePatchResidualDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem restrict_P_formal_forest_error (g : DeficientGraph V d) (hd : 3≤d)
    (S : Set V) (hbudget : (g.restrict S).ComponentFiniteReferenceBudget)
    (u v : S) (r k : ℕ) (hcenters : g.graph.edist u.val v.val≤(k:ℕ∞))
    (htree : (graphBall g.graph u.val (r+k)).IsTree)
    (hzero : ∀ w∈graphBallVertices g.graph u.val (r+k),g.deficit w=0)
    (q p z : ℂ) (hq : q≠0) (hp : p*(q⁻¹-q/((d:ℂ)-1))=1)
    (hz : 0<z.im) (hqim : 0 ≤ q.im)
    (small : ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((4*r+1:ℕ)+1:ℝ)≤1/2)
    (P Q : ℝ) (hP : 0≤P) (hQ : 0≤Q) (hpbound : ‖p‖≤P)
    (hqpow : ∀ n≤4*r+1,‖q‖^n≤Q) :
    let M := g.restrict S
    let K := M.restrict (pairBallVertices M.graph u v r)
    ‖M.P r z q u v-formalForestKernel K.graph d q p
      (pairBallLeft M.graph u v r) (pairBallRight M.graph u v r)‖≤
      ‖(1+z*q+q^2)/q‖*(8*finiteExtraReferenceConstant d^2+2*(P*Q)^2)*((4*r+1:ℕ)+1:ℝ) := by
  dsimp only
  let M := g.restrict S
  let A := pairBallVertices M.graph u v r
  let K := M.restrict A
  let f := inducedPairBallAmbientMap g.graph S u v r k hcenters
  have hforest : K.graph.IsAcyclic :=
    induced_pairBall_acyclic_of_ambient_tree g.graph S u v r k hcenters htree
  have hKzero : ∀ w,K.deficit w=0 := fun w => hzero w.val.val (f w).property
  have hKbudget := M.restrict_componentFiniteReferenceBudget A hbudget
  exact K.formal_forest_error_of_finite_class hd hKbudget hKzero hforest q p z hq hp hz hqim
    (4*r+1) (pairBall_distance_bound M.graph u v r) small P Q hP hQ hpbound hqpow
    (pairBallLeft M.graph u v r) (pairBallRight M.graph u v r)

theorem restrict_P_diagonal_formal_residual (g : DeficientGraph V d) (hd : 3≤d)
    (S : Set V) (hbudget : (g.restrict S).ComponentFiniteReferenceBudget)
    (u : S) (r : ℕ) (htree : (graphBall g.graph u.val r).IsTree)
    (hzero : ∀ w∈graphBallVertices g.graph u.val r,g.deficit w=0)
    (q p z : ℂ) (hq : q≠0) (hp : p*(q⁻¹-q/((d:ℂ)-1))=1)
    (hz : 0<z.im) (hqim : 0 ≤ q.im)
    (small : ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((4*r+1:ℕ)+1:ℝ)≤1/2)
    (P Q : ℝ) (hP : 0≤P) (hQ : 0≤Q) (hpbound : ‖p‖≤P)
    (hqpow : ∀ n≤4*r+1,‖q‖^n≤Q) :
    ‖(g.restrict S).P r z q u u-p‖≤
      ‖(1+z*q+q^2)/q‖*(8*finiteExtraReferenceConstant d^2+2*(P*Q)^2)*((4*r+1:ℕ)+1:ℝ) := by
  have hh := g.restrict_P_formal_forest_error hd S hbudget u u r 0 (by simp)
    (by simpa only [Nat.add_zero] using htree) (by simpa only [Nat.add_zero] using hzero)
    q p z hq hp hz hqim small P Q hP hQ hpbound hqpow
  dsimp only at hh
  have he : pairBallLeft (g.restrict S).graph u u r=pairBallRight (g.restrict S).graph u u r := Subtype.ext rfl
  dsimp only [formalForestKernel] at hh
  rw [he,forestKernelColumn_root] at hh
  exact hh

theorem restrict_P_adjacent_formal_residual (g : DeficientGraph V d) (hd : 3≤d)
    (S : Set V) (hbudget : (g.restrict S).ComponentFiniteReferenceBudget)
    (u v : S) (huv : g.graph.Adj u.val v.val) (r : ℕ)
    (htree : (graphBall g.graph u.val (r+1)).IsTree)
    (hzero : ∀ w∈graphBallVertices g.graph u.val (r+1),g.deficit w=0)
    (q p z : ℂ) (hq : q≠0) (hp : p*(q⁻¹-q/((d:ℂ)-1))=1)
    (hz : 0<z.im) (hqim : 0 ≤ q.im)
    (small : ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((4*r+1:ℕ)+1:ℝ)≤1/2)
    (P Q : ℝ) (hP : 0≤P) (hQ : 0≤Q) (hpbound : ‖p‖≤P)
    (hqpow : ∀ n≤4*r+1,‖q‖^n≤Q) :
    ‖(g.restrict S).P r z q u v-p*(-q*treeEdgeWeight d)‖≤
      ‖(1+z*q+q^2)/q‖*(8*finiteExtraReferenceConstant d^2+2*(P*Q)^2)*((4*r+1:ℕ)+1:ℝ) := by
  have hcenters : g.graph.edist u.val v.val≤(1:ℕ∞) := (SimpleGraph.edist_eq_one_iff_adj.mpr huv).le
  have hh := g.restrict_P_formal_forest_error hd S hbudget u v r 1 hcenters htree hzero
    q p z hq hp hz hqim small P Q hP hQ hpbound hqpow
  dsimp only at hh
  let K := (g.restrict S).restrict (pairBallVertices (g.restrict S).graph u v r)
  have ha : K.graph.Adj (pairBallLeft (g.restrict S).graph u v r) (pairBallRight (g.restrict S).graph u v r) := huv
  change ‖(g.restrict S).P r z q u v-formalForestKernel K.graph d q p _ _‖≤_ at hh
  simpa only [formalForestKernel,forestKernelColumn,if_pos ha.reachable,
    SimpleGraph.dist_eq_one_iff_adj.mpr ha,pow_one] using hh

end DeficientGraph
end LocalLaw
