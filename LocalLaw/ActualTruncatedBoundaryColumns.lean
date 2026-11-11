import LocalLaw.ActualBoundaryColumnBudgets
import LocalLaw.TreeCavityBoundaryDefect
import LocalLaw.SourceCavityResidual

/-! # Derived column bounds for the actual truncated-tree boundary defect -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance actualTruncatedBoundaryColumnsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem matrix_add_scalar_identity_column {I : Type*} [Fintype I] [DecidableEq I]
    (D : Matrix I I ℂ) (w : ℂ) (j : I) :
    ∑ i, ‖(D + w • 1) i j‖ ≤ (∑ i, ‖D i j‖) + ‖w‖ := by
  calc
    _ ≤ ∑ i, (‖D i j‖ + ‖(w • (1 : Matrix I I ℂ)) i j‖) :=
      Finset.sum_le_sum (fun i _ => norm_add_le _ _)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        mul_ite, mul_one, mul_zero, apply_ite norm, norm_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]

def sourceTruncatedColumnBudgetConstant (d J : ℕ) (C1 : ℝ) : ℝ :=
  sourceBoundaryColumnBudgetConstant d J C1 + 1

namespace RegularGraph

theorem eventually_actual_truncated_boundary_column_budget (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25*a ≤ b) (hd : 3 ≤ d) (hc : 0<c)
    (hβ : 0<β) (hβc : β ≤ c/32) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ) ≤ z.im → ‖z‖ ≤ B → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      (graphBall g.graph o (logarithmicRadius (c/4) d N/8)).IsTree →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell := actualCavityDepth a d N z-1
      let R := logarithmicRadius (c/4) d N
      let T := graphBallVertices g.graph o ell
      let L := Real.log (N:ℝ)
      let ε := graphPaperError a d N (logarithmicRadius β d N) z
      let φ := correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
      ¬g.sourceGreenIsolationBad T z φ (R/4) (Nat.ceil L) S → ∀ J : ℕ,
      (rejectedResamplingIndices g.graph T (R/4) S).card ≤ J → ∀ j,
      ∑ i, ‖g.sourceTruncatedBoundaryDefect T labels S (R/4) (g.Q z) z i j‖ ≤
        sourceTruncatedColumnBudgetConstant d J C1*L^5*ε := by
  filter_upwards [eventually_actual_boundary_column_budget a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_cavity_residual_le_sourcePrime a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    eventually_log_ge_nat 1,Filter.eventually_ge_atTop 1] with N hcolumns hres hrad hmargin hlog hN
  intro g o z hz hfloor hzB Cq badCount hplus hTree ι _ labels S
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let R := logarithmicRadius (c/4) d N
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  have hL : 1≤L := hlog
  have hε : 0≤ε := graphPaperError_nonnegative a d N _ z hN hz.le
  have hsep : 2*r+2≤R/4 := by dsimp only [r,R]; omega
  have hr : r+2≤R/4 := by dsimp only [r,R] at *; omega
  have hroom : ell+r+1≤R/8 := by
    have hh := hrad.2.2.2 z
    change r+ell+1≤R/8 at hh
    omega
  have hdecomp := g.sourceTruncatedBoundaryDefect_tree_decomposition hd o ell (R/4) r (R/8)
    hsep hr hroom hTree labels S (g.Q z) z hz (g.Q_im_nonnegative z hz)
  have hscalar := hres z (g.Q z) hz hzB hfloor hplus.cavity
  have hscalar' : ‖cavityIterate z (g.Q z) (r+1)-g.Q z‖≤L^5*ε := by
    rw [norm_sub_rev]
    exact hscalar.trans (by
      change L^3*ε≤L^5*ε
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL (by omega)) hε)
  intro hisolation J hrejected j
  rw [hdecomp]
  have hc := hcolumns g o z hz hfloor hzB Cq badCount hplus labels S hisolation J hrejected j
  exact (matrix_add_scalar_identity_column _ _ j).trans ((add_le_add hc hscalar').trans_eq (by
    dsimp only [sourceTruncatedColumnBudgetConstant]
    ring))

end RegularGraph
end LocalLaw
