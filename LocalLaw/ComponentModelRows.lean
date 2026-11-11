import LocalLaw.ComponentBallGeometry
import LocalLaw.OutsideBallReferenceRows
import LocalLaw.ComponentwiseReferenceBounds

/-!
# Source cross-sum bounds for disconnected finite models

Only the component containing the removed root ball can contribute to its
cross sums. The actual inverse block identity and isolated-ball equivalence
transfer the connected-model estimates to the original disconnected model.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance componentRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) canonicalComponentRowsMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

/-- Claim 5.5 in a possibly disconnected model, with a genuine componentwise
reference budget and an outside target. No total-excess bound is imposed. -/
theorem componentwise_outside_ball_row_sum (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hbudget : g.ComponentReferenceBudget) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ a b, g.graph.dist a b ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * ((R : ℝ) + 1) ≤ 1 / 2)
    (o i : V) (ell : ℕ) (hout : i ∉ graphBallVertices g.graph o ell) :
    (∑ y : graphBallVertices g.graph o ell, ‖g.extensionGreen q z i y.val‖) ≤
      2 * finiteReferenceConstant d * outsideBallKernelConstant d (finiteOmega d) * ((ell : ℝ) + 1) := by
  let c := g.graph.connectedComponentMk o
  let root : c.supp := ⟨o, rfl⟩
  have hyc (y : graphBallVertices g.graph o ell) : y.val ∈ c.supp := by
    have hfinite := ne_top_of_le_ne_top (ENat.coe_ne_top ell) y.property
    exact (SimpleGraph.ConnectedComponent.sound (SimpleGraph.reachable_of_edist_ne_top hfinite)).symm
  by_cases hi : i ∈ c.supp
  · let gc := g.restrict c.supp
    let ii : c.supp := ⟨i, hi⟩
    have hgc : gc.graph.Connected := c.connected_induce_supp
    have hdiam : ∀ a b, gc.graph.dist a b ≤ R := by
      intro a b
      change (g.graph.induce c.supp).dist a b ≤ R
      rw [isolated_induce_distance g.graph c.supp (g.component_cut c)]
      exact hR a.val b.val
    have hnot : ii ∉ graphBallVertices gc.graph root ell := by
      intro hh
      exact hout ((isolated_graphBall_mem g.graph c.supp (g.component_cut c) root ell ii).mp hh)
    have hdist : ell < gc.graph.dist root ii := by
      have hh : ¬gc.graph.dist root ii ≤ ell := fun hh => hnot
        ((connected_mem_graphBall_iff_dist gc.graph hgc root ii ell).mpr hh)
      omega
    have hrow := gc.finiteOmega_outside_ball_row_sum hd hgc (hbudget c)
      q z hz hq R hdiam small root ii ell hdist
    let φ := isolatedBallEquiv g.graph c.supp (g.component_cut c) root ell
    have hmodel := g.restrict_extensionGreen_of_isolated hd c.supp (g.component_cut c) q z hz hq
    have hsum : (∑ y : graphBallVertices gc.graph root ell, ‖gc.extensionGreen q z ii y.val‖) =
        ∑ y : graphBallVertices g.graph o ell, ‖g.extensionGreen q z i y.val‖ := by
      apply Fintype.sum_equiv φ
      intro y
      rw [hmodel]
      rfl
    simp only [← finsum_eq_sum_of_fintype] at hsum hrow ⊢
    exact hsum.symm.trans_le hrow
  · have hzero : (∑ y : graphBallVertices g.graph o ell, ‖g.extensionGreen q z i y.val‖) = 0 := by
      apply Finset.sum_eq_zero
      intro y _
      rw [(g.extensionGreen_isSymm q z).apply y.val i,
        g.extensionGreen_zero_across_cut hd c.supp (g.component_cut c) q z hz hq y.val (hyc y) i hi,
        norm_zero]
    rw [hzero]
    have hC := (by norm_num : (0 : ℝ) ≤ 1).trans (finiteReferenceConstant_ge_one d hd)
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC)
      (outsideBallKernelConstant_nonnegative _ _)) (by positivity)

theorem componentwise_outside_ball_column_sum (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hbudget : g.ComponentReferenceBudget) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ a b, g.graph.dist a b ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * ((R : ℝ) + 1) ≤ 1 / 2)
    (o i : V) (ell : ℕ) (hout : i ∉ graphBallVertices g.graph o ell) :
    (∑ y : graphBallVertices g.graph o ell, ‖g.extensionGreen q z y.val i‖) ≤
      2 * finiteReferenceConstant d * outsideBallKernelConstant d (finiteOmega d) * ((ell : ℝ) + 1) := by
  have hrow := g.componentwise_outside_ball_row_sum hd hbudget q z hz hq R hR small o i ell hout
  convert hrow using 1
  apply Finset.sum_congr rfl
  intro y _
  exact congrArg norm ((g.extensionGreen_isSymm q z).apply i y.val)

/-- Claim 5.6 for a possibly disconnected zero-deficit model. Only the
actual center component is used, and its deleted intrinsic diameter is
derived from the same global deleted-graph cap. -/
theorem componentwise_ball_retained_inverse_bounds (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hzero : ∀ v, g.deficit v = 0) (hbudget : g.ComponentReferenceBudget)
    (o : V) (ell : ℕ) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (B : ℝ) (hB : ‖z‖ ≤ B) (hqnear : ‖q - semicircleRoot z‖ ≤ 1)
    (Rdel : ℕ)
    (hRdel : ∀ a b, (outsideGraph g.graph (graphBallVertices g.graph o ell)).dist a b ≤ Rdel)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((Rdel : ℝ) + 1) ≤ 1 / 2) :
    (∀ x : graphBallVertices g.graph o ell,
      (∑ y : graphBallVertices g.graph o ell, ‖((g.extensionGreen q z).submatrix
        (Subtype.val : graphBallVertices g.graph o ell → V)
        (Subtype.val : graphBallVertices g.graph o ell → V))⁻¹ x y‖) ≤ boundarySchurConstant d B) ∧
    (∀ y : graphBallVertices g.graph o ell,
      (∑ x : graphBallVertices g.graph o ell, ‖((g.extensionGreen q z).submatrix
        (Subtype.val : graphBallVertices g.graph o ell → V)
        (Subtype.val : graphBallVertices g.graph o ell → V))⁻¹ x y‖) ≤ boundarySchurConstant d B) := by
  let c := g.graph.connectedComponentMk o
  let root : c.supp := ⟨o, rfl⟩
  let gc := g.restrict c.supp
  let T := graphBallVertices g.graph o ell
  let Tc := graphBallVertices gc.graph root ell
  let φ := isolatedBallEquiv g.graph c.supp (g.component_cut c) root ell
  have hgc : gc.graph.Connected := c.connected_induce_supp
  have hgcZero (v : c.supp) : gc.deficit v = 0 := hzero v.val
  have hgcBudget : graphExcess gc.graph ≤ finiteOmega d := by
    have hh := hbudget c
    change (∑ v, gc.deficit v) + graphExcess gc.graph ≤ finiteOmega d at hh
    omega
  have hgcDelDiam : ∀ a b, (outsideGraph gc.graph Tc).dist a b ≤ Rdel := by
    intro a b
    have hh := isolated_graphBall_deleted_distance g.graph c.supp (g.component_cut c) root ell a b
    exact hh.trans_le (hRdel _ _)
  have hbounds := gc.zero_deficit_retained_inverse_bounds hd hgcZero Tc hgc
    (graphBall_connected gc.graph root ell) hgcBudget q z hz hq B hB hqnear Rdel hgcDelDiam small
  have hmodel := g.restrict_extensionGreen_of_isolated hd c.supp (g.component_cut c) q z hz hq
  let Pc := (gc.extensionGreen q z).submatrix (Subtype.val : Tc → c.supp) (Subtype.val : Tc → c.supp)
  let P := (g.extensionGreen q z).submatrix (Subtype.val : T → V) (Subtype.val : T → V)
  have hprincipal : Pc = P.submatrix φ φ := by
    ext x y
    have hh := congrFun (congrFun hmodel x.val) y.val
    exact hh
  have hinv : Pc⁻¹ = P⁻¹.submatrix φ φ := by rw [hprincipal, Matrix.inv_submatrix_equiv]
  have hrows (x : T) : (∑ y : T, ‖P⁻¹ x y‖) ≤ boundarySchurConstant d B := by
    have hlocal := hbounds.1 (φ.symm x)
    have hsum : (∑ y : Tc, ‖Pc⁻¹ (φ.symm x) y‖) = ∑ y : T, ‖P⁻¹ x y‖ := by
      apply Fintype.sum_equiv φ
      intro y
      rw [hinv]
      simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]
    simp only [← finsum_eq_sum_of_fintype] at hsum hlocal ⊢
    exact hsum.symm.trans_le hlocal
  refine ⟨hrows, ?_⟩
  intro y
  convert hrows y using 1
  apply Finset.sum_congr rfl
  intro x _
  exact congrArg norm ((g.retained_extensionGreen_inverse_isSymm T q z).apply y x)

end DeficientGraph
end LocalLaw
