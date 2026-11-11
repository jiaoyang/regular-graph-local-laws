import LocalLaw.LeafLocalizationBounds

/-! # Captured leaf neighborhoods from two independently captured target balls -/

noncomputable section
namespace LocalLaw
local instance twoRadiusLeafDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def twoRadiusLeafRadius (ri rj di dj : ℕ) : ℕ :=
  max (ri-min ri di) (rj-min rj dj)

theorem captured_balls_shift_two_radii {V : Type*} (G : SimpleGraph V) (S : Set V)
    (i j leaf : V) (ri rj : ℕ) (hi : G.Reachable i leaf) (hj : G.Reachable j leaf)
    (hI : graphBallVertices G i ri⊆S) (hJ : graphBallVertices G j rj⊆S) (hleaf : leaf∈S) :
    graphBallVertices G leaf (twoRadiusLeafRadius ri rj (G.dist i leaf) (G.dist j leaf))⊆S := by
  by_cases h : ri-min ri (G.dist i leaf)≤rj-min rj (G.dist j leaf)
  · rw [twoRadiusLeafRadius,max_eq_right h]
    exact captured_ball_shift G S j leaf rj hj hJ hleaf
  · rw [twoRadiusLeafRadius,max_eq_left (by omega)]
    exact captured_ball_shift G S i leaf ri hi hI hleaf

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem leaf_localization_factors_two_radii (g : DeficientGraph V d) (hd : 3≤d)
    (hbudget : g.ComponentFiniteReferenceBudget) (S : Set V)
    (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) (B : ℝ) (hzB : ‖z‖≤B)
    (ε L A : ℝ) (hε : 0≤ε) (hεOne : ε≤1) (hL : 1≤L) (hA : 0≤A) (hcap : ε*L^4≤1)
    (hprior : ‖q-semicircleRoot z‖≤scalarScale (spectralScale z) ε)
    (R Rs : ℕ) (hR : ∀a b,g.graph.dist a b≤R) (hRs : ∀a b,(g.restrict S).graph.dist a b≤Rs)
    (hRlog : (R:ℝ)+1≤A*L) (hRslog : (Rs:ℝ)+1≤A*L)
    (hlarge : localizationBudgetConstant d B A≤L) (i j leaf : S) (ri rj : ℕ)
    (hi : g.graph.Reachable i.val leaf.val) (hj : g.graph.Reachable j.val leaf.val)
    (hI : graphBallVertices g.graph i.val ri⊆S) (hJ : graphBallVertices g.graph j.val rj⊆S) :
    let rl:=twoRadiusLeafRadius ri rj (g.graph.dist i.val leaf.val) (g.graph.dist j.val leaf.val)
    let u:=2*localizationFeedbackConstant d B A*L*ε
    let v:=localizationTailConstant d
    let ρ:=physicalTransfer d z
    let P:=g.extensionGreen q z
    let Q:=(g.restrict S).extensionGreen q z
    (‖P i.val leaf.val-Q i leaf‖≤u+v*ρ^(ri+rl)) ∧
    (‖P leaf.val j.val-Q leaf j‖≤u+v*ρ^(rj+rl)) ∧
    (‖P leaf.val j.val‖≤2*finiteExtraReferenceConstant d*ρ^(g.graph.dist j.val leaf.val)) ∧
    (‖Q i leaf‖≤2*finiteExtraReferenceConstant d*ρ^(g.graph.dist i.val leaf.val)) := by
  dsimp only
  let rl:=twoRadiusLeafRadius ri rj (g.graph.dist i.val leaf.val) (g.graph.dist j.val leaf.val)
  have hcapture : graphBallVertices g.graph leaf.val rl⊆S :=
    captured_balls_shift_two_radii g.graph S i.val j.val leaf.val ri rj hi hj hI hJ leaf.property
  have hlocI:=g.componentwise_weak_restriction_localization_asymmetric hd hbudget S q z hz hq B hzB
    ε L A hε hεOne hL hA hcap hprior R Rs hR hRs hRlog hRslog hlarge i leaf ri rl hI hcapture
  have hlocJ:=g.componentwise_weak_restriction_localization_asymmetric hd hbudget S q z hz hq B hzB
    ε L A hε hεOne hL hA hcap hprior R Rs hR hRs hRlog hRslog hlarge j leaf rj rl hJ hcapture
  obtain ⟨sG,sS,_⟩:=weak_localization_feedback_budgets d hd z q hz B ε L A hε hL hA hcap hprior
    R Rs hRlog hRslog hlarge
  have hkG:=g.componentwise_finite_kernel_decay hd hbudget q z hz hq R hR sG j.val leaf.val
  have hsG:=g.extensionGreen_isSymm q z
  have hsS:=(g.restrict S).extensionGreen_isSymm q z
  have hfar : (g.graph.dist i.val leaf.val:ℕ∞)≤(g.restrict S).graph.edist i leaf := by
    have heq : (g.graph.dist i.val leaf.val:ℕ∞)=g.graph.edist i.val leaf.val :=
      ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr hi)
    exact heq.le.trans (ambient_edist_le_induced_edist g.graph S i leaf)
  have hkS:=(g.restrict S).perturbed_green_edist_bound hd (g.restrict_componentFiniteReferenceBudget S hbudget)
    z q hz hq Rs hRs sS i leaf (g.graph.dist i.val leaf.val) hfar
  refine ⟨hlocI,?_,?_,hkS⟩
  · simpa only [hsG.apply leaf.val j.val,hsS.apply leaf j] using hlocJ
  · simpa only [hsG.apply leaf.val j.val] using hkG

end DeficientGraph
end LocalLaw
