import LocalLaw.ComponentFiniteLocalization

/-! Uniform rows at separated roots of an actual physical-boundary model. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance separatedPhysicalRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] {d : ℕ}

theorem separated_physical_endpoint_rows (g : DeficientGraph V d) (hd : 3≤d)
    (hbudget : g.ComponentFiniteReferenceBudget) (e : I↪V) (h : ℕ)
    (hsep : ∀ i j,i≠j→(h:ℕ∞)≤g.graph.edist (e i) (e j))
    (z : ℂ) (hz : 0<z.im) (hsmall : (Fintype.card I:ℝ)*physicalTransfer d z^h≤1) :
    (∀ i,∑ j,‖g.extensionGreen (semicircleRoot z) z (e i) (e j)‖≤4*finiteExtraReferenceConstant d) ∧
      (∀ j,∑ i,‖g.extensionGreen (semicircleRoot z) z (e i) (e j)‖≤4*finiteExtraReferenceConstant d) := by
  let R:=Finset.univ.sup (fun ij:V×V=>g.graph.dist ij.1 ij.2)
  have hR (i j:V) : g.graph.dist i j≤R:=Finset.le_sup (f:=fun ij:V×V=>g.graph.dist ij.1 ij.2) (Finset.mem_univ (i,j))
  let C:=2*finiteExtraReferenceConstant d
  let t:=physicalTransfer d z
  have hC : 0≤C:=by dsimp only [C]; have hh:=finiteExtraReferenceConstant_ge_one d hd; positivity
  have ht : 0≤t:=(physicalTransfer_pos d hd z).le
  have htOne : t≤1:=by dsimp only [t]; nlinarith [physicalTransfer_sq_le_half d hd z]
  have hk:=g.componentwise_finite_kernel_decay hd hbudget (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le R hR (by simp)
  have hcap (i j:I) : ‖g.extensionGreen (semicircleRoot z) z (e i) (e j)‖≤C :=
    (hk (e i) (e j)).trans (mul_le_of_le_one_right hC (pow_le_one₀ ht htOne))
  have hfar (i j:I) (hij:i≠j) : ‖g.extensionGreen (semicircleRoot z) z (e i) (e j)‖≤C*t^h := by
    by_cases hr:g.graph.Reachable (e i) (e j)
    · have heq : (g.graph.dist (e i) (e j):ℕ∞)=g.graph.edist (e i) (e j):=
        ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr hr)
      have hdist : h≤g.graph.dist (e i) (e j):=ENat.coe_le_coe.mp ((hsep i j hij).trans_eq heq.symm)
      exact (hk (e i) (e j)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht htOne hdist) hC)
    · let c:=g.graph.connectedComponentMk (e i)
      have hj:e j∉c.supp:=fun hh=>hr (SimpleGraph.ConnectedComponent.exact hh.symm)
      rw [g.extensionGreen_zero_across_cut hd c.supp (g.component_cut c) _ z hz (semicircleRoot_im_pos hz).le _ rfl _ hj,norm_zero]
      positivity
  have hrow (i:I) : ∑ j,‖g.extensionGreen (semicircleRoot z) z (e i) (e j)‖≤4*finiteExtraReferenceConstant d := by
    have hp (j:I) : ‖g.extensionGreen (semicircleRoot z) z (e i) (e j)‖≤(if j=i then C else 0)+C*t^h := by
      by_cases hij:j=i
      · simpa only [hij,if_true] using (hcap i i).trans (le_add_of_nonneg_right (mul_nonneg hC (pow_nonneg ht _)))
      · simpa only [hij,if_false,zero_add] using hfar i j (Ne.symm hij)
    have hh : (∑ j,‖g.extensionGreen (semicircleRoot z) z (e i) (e j)‖)≤C+(Fintype.card I:ℝ)*(C*t^h) := by
      exact (Finset.sum_le_sum (fun j _=>hp j)).trans_eq (by simp [Finset.sum_add_distrib])
    have hs:=mul_le_mul_of_nonneg_left hsmall hC
    dsimp only [C] at hh hs
    nlinarith only [hh,hs]
  refine ⟨hrow,fun j=>?_⟩
  have hs:=g.extensionGreen_isSymm (semicircleRoot z) z
  have heq : (∑ i,‖g.extensionGreen (semicircleRoot z) z (e i) (e j)‖)=
      ∑ i,‖g.extensionGreen (semicircleRoot z) z (e j) (e i)‖:=
    Finset.sum_congr rfl (fun i _=>congrArg norm (hs.apply (e j) (e i)))
  rw [heq]
  exact hrow j

end DeficientGraph
end LocalLaw
