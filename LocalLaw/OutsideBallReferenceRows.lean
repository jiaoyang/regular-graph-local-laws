import LocalLaw.OutsideBallKernelSum
import LocalLaw.DeletedComponentBounds

/-!
# The actual reference-model row sum needed by Claim 5.5

The target lies outside the removed ball. Finite-threshold reference decay,
the proved boundary stability, and the actual bounded-excess ball count give
the norm row bound. No kernel bound or final row estimate is assumed.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance outsideReferenceRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def outsideBallKernelConstant (d ω : ℕ) : ℝ :=
  (1 + 8 * (d : ℝ)) * (2 * (2 * (ω : ℝ) + 2) * (2 * (ω : ℝ) + 1))

theorem outsideBallKernelConstant_nonnegative (d ω : ℕ) : 0 ≤ outsideBallKernelConstant d ω := by
  unfold outsideBallKernelConstant
  positivity

theorem physicalTransfer_le_critical (d : ℕ) (z : ℂ) :
    physicalTransfer d z ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹ := by
  have hs : 0 ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  simp only [physicalTransfer, norm_mul, norm_neg, treeEdgeWeight, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hs]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (semicircleRoot_norm_le_one z) hs

section ConnectedBalls
variable {V : Type*} (G : SimpleGraph V) (hG : G.Connected)
include hG

theorem connected_mem_graphBall_iff_dist (o v : V) (ell : ℕ) :
    v ∈ graphBallVertices G o ell ↔ G.dist o v ≤ ell := by
  have heq : ((G.dist o v : ℕ) : ℕ∞) = G.edist o v :=
    ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr (hG o v))
  change G.edist o v ≤ (ell : ℕ∞) ↔ _
  rw [← heq]
  exact ENat.coe_le_coe

variable [Fintype V]

theorem sum_graphBall_eq_if_dist (o : V) (ell : ℕ) (f : V → ℝ) :
    (∑ v : graphBallVertices G o ell, f v.val) =
      ∑ v : V, if G.dist o v ≤ ell then f v else 0 := by
  have hh := Finset.sum_subtype (p := fun v => v ∈ graphBallVertices G o ell)
    (F := (inferInstance : Fintype (graphBallVertices G o ell)))
    (Finset.univ.filter (fun v => G.dist o v ≤ ell))
    (fun v => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                 exact (connected_mem_graphBall_iff_dist G hG o v ell).symm) f
  rw [Finset.sum_filter] at hh
  exact hh.symm

end ConnectedBalls

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

/-- The actual perturbed model satisfies the outside-target norm row bound
with a constant depending only on d and its constructed reference threshold. -/
theorem finiteOmega_outside_ball_row_sum (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.Connected)
    (hbudget : (∑ v, g.deficit v) + graphExcess g.graph ≤ finiteOmega d)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ a b, g.graph.dist a b ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * ((R : ℝ) + 1) ≤ 1 / 2)
    (o i : V) (ell : ℕ) (hout : ell < g.graph.dist o i) :
    (∑ y : graphBallVertices g.graph o ell, ‖g.extensionGreen q z i y.val‖) ≤
      2 * finiteReferenceConstant d * outsideBallKernelConstant d (finiteOmega d) * ((ell : ℝ) + 1) := by
  have hω : graphExcess g.graph ≤ finiteOmega d := by omega
  have hC : 0 ≤ finiteReferenceConstant d := (by norm_num : (0 : ℝ) ≤ 1).trans
    (finiteReferenceConstant_ge_one d hd)
  have href := (finiteOmega_reference_bounds d hd g hG hbudget z hz).1
  have hpoint (y : V) : ‖g.extensionGreen q z i y‖ ≤
      2 * finiteReferenceConstant d * physicalTransfer d z ^ g.graph.dist i y :=
    (g.reference_boundary_stability hd hG (finiteOmega d) hω z q hz hq _ hC R hR href small i y).2
  have hgeom := outside_ball_kernel_sum g.graph hG d hd g.degree_le (finiteOmega d) hω o i ell hout
    (physicalTransfer d z) (physicalTransfer_pos d hd z).le (physicalTransfer_le_critical d z)
  have hkernel : (∑ y : graphBallVertices g.graph o ell,
      physicalTransfer d z ^ g.graph.dist i y.val) ≤
        outsideBallKernelConstant d (finiteOmega d) * ((ell : ℝ) + 1) := by
    have heq := sum_graphBall_eq_if_dist g.graph hG o ell
      (fun y => physicalTransfer d z ^ g.graph.dist i y)
    simp only [← finsum_eq_sum_of_fintype] at heq hgeom ⊢
    exact heq.trans_le hgeom
  calc
    _ ≤ ∑ y : graphBallVertices g.graph o ell,
        2 * finiteReferenceConstant d * physicalTransfer d z ^ g.graph.dist i y.val :=
      Finset.sum_le_sum (fun y _ => hpoint y.val)
    _ = (2 * finiteReferenceConstant d) * ∑ y : graphBallVertices g.graph o ell,
        physicalTransfer d z ^ g.graph.dist i y.val := (Finset.mul_sum ..).symm
    _ ≤ (2 * finiteReferenceConstant d) *
        (outsideBallKernelConstant d (finiteOmega d) * ((ell : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hkernel (by positivity)
    _ = _ := by ring

/-- Symmetry supplies the corresponding actual outside-target column sum. -/
theorem finiteOmega_outside_ball_column_sum (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.Connected)
    (hbudget : (∑ v, g.deficit v) + graphExcess g.graph ≤ finiteOmega d)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ a b, g.graph.dist a b ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * ((R : ℝ) + 1) ≤ 1 / 2)
    (o i : V) (ell : ℕ) (hout : ell < g.graph.dist o i) :
    (∑ y : graphBallVertices g.graph o ell, ‖g.extensionGreen q z y.val i‖) ≤
      2 * finiteReferenceConstant d * outsideBallKernelConstant d (finiteOmega d) * ((ell : ℝ) + 1) := by
  have hrow := g.finiteOmega_outside_ball_row_sum hd hG hbudget q z hz hq R hR small o i ell hout
  convert hrow using 1
  apply Finset.sum_congr rfl
  intro y _
  exact congrArg norm (congrFun (congrFun (g.extensionGreen_isSymm q z) i) y.val)

end DeficientGraph
end LocalLaw
