import LocalLaw.TreePatchWeakResidual

/-! # Actual diagonal and adjacent tree values under a weak scalar prior -/
noncomputable section
set_option maxHeartbeats 1000000
namespace LocalLaw
local instance treePatchWeakValuesDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem restrict_tree_diagonal_weak_residual (g : DeficientGraph V d) (hd : 3≤d)
    (S : Set V) (hbudget : (g.restrict S).ComponentFiniteReferenceBudget)
    (u : S) (r R : ℕ) (htree : (graphBall g.graph u.val r).IsTree)
    (hzero : ∀ w∈graphBallVertices g.graph u.val r,g.deficit w=0)
    (q p z : ℂ) (hq : q≠0) (hp : p*(q⁻¹-q/((d:ℂ)-1))=1)
    (hz : 0<z.im) (hqim : 0 ≤ q.im)
    (B C ε L A : ℝ) (hzB : ‖z‖≤B)
    (num : SourceObservationBounds d r z B C ε L A)
    (hprior : ‖q-semicircleRoot z‖≤C*scalarScale (spectralScale z) ε)
    (hR : ∀ a b,(g.restrict S).graph.dist a b≤R) (hRlog : (R:ℝ)+1≤A*L)
    (hpbound : ‖p‖≤4) (hqinv : ‖q⁻¹‖≤2*(B+1))
    (hqpow : ∀ n≤4*r+1,‖q‖^n≤2) :
    ‖(g.restrict S).extensionGreen q z u u-p‖≤
      treePatchWeakConstant d B A*C^2*L*ε := by
  have hh := g.restrict_tree_pair_weak_residual hd S hbudget u u r 0 R (by simp)
    (by simpa only [Nat.add_zero] using htree) (by simpa only [Nat.add_zero] using hzero)
    q p z hq hp hz hqim B C ε L A hzB num hprior hR hRlog hpbound hqinv hqpow
  dsimp only at hh
  have he : pairBallLeft (g.restrict S).graph u u r=pairBallRight (g.restrict S).graph u u r := Subtype.ext rfl
  dsimp only [formalForestKernel] at hh
  rw [he,forestKernelColumn_root] at hh
  exact hh

theorem restrict_tree_adjacent_weak_residual (g : DeficientGraph V d) (hd : 3≤d)
    (S : Set V) (hbudget : (g.restrict S).ComponentFiniteReferenceBudget)
    (u v : S) (huv : g.graph.Adj u.val v.val) (r R : ℕ)
    (htree : (graphBall g.graph u.val (r+1)).IsTree)
    (hzero : ∀ w∈graphBallVertices g.graph u.val (r+1),g.deficit w=0)
    (q p z : ℂ) (hq : q≠0) (hp : p*(q⁻¹-q/((d:ℂ)-1))=1)
    (hz : 0<z.im) (hqim : 0 ≤ q.im)
    (B C ε L A : ℝ) (hzB : ‖z‖≤B)
    (num : SourceObservationBounds d r z B C ε L A)
    (hprior : ‖q-semicircleRoot z‖≤C*scalarScale (spectralScale z) ε)
    (hR : ∀ a b,(g.restrict S).graph.dist a b≤R) (hRlog : (R:ℝ)+1≤A*L)
    (hpbound : ‖p‖≤4) (hqinv : ‖q⁻¹‖≤2*(B+1))
    (hqpow : ∀ n≤4*r+1,‖q‖^n≤2) :
    ‖(g.restrict S).extensionGreen q z u v-p*(-q*treeEdgeWeight d)‖≤
      treePatchWeakConstant d B A*C^2*L*ε := by
  have hcenters : g.graph.edist u.val v.val≤(1:ℕ∞) := (SimpleGraph.edist_eq_one_iff_adj.mpr huv).le
  have hh := g.restrict_tree_pair_weak_residual hd S hbudget u v r 1 R hcenters htree hzero
    q p z hq hp hz hqim B C ε L A hzB num hprior hR hRlog hpbound hqinv hqpow
  dsimp only at hh
  let K := (g.restrict S).restrict (pairBallVertices (g.restrict S).graph u v r)
  have ha : K.graph.Adj (pairBallLeft (g.restrict S).graph u v r) (pairBallRight (g.restrict S).graph u v r) := huv
  change ‖(g.restrict S).extensionGreen q z u v-formalForestKernel K.graph d q p _ _‖≤_ at hh
  simpa only [formalForestKernel,forestKernelColumn,if_pos ha.reachable,
    SimpleGraph.dist_eq_one_iff_adj.mpr ha,pow_one] using hh

end DeficientGraph
end LocalLaw
