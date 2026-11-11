import SpectralConsequences.SourceBoundaryConditionalMeans
import SpectralConsequences.SourceTruncatedRootRemainder
import SpectralConsequences.BoundaryMeanAggregation
import SpectralConsequences.FullBoundaryWeights

/-! Actual full-root conditional drift under the original source event.
The q-dependent correction is retained until after finite averaging. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceTraceConditionalDriftDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ}

def traceBoundaryCorrectionCoefficient (g:LocalLaw.RegularGraph N d) (o:Fin N) (ell:ℕ) (q z:ℂ):ℂ:=
  (treeEdgeWeight d)^2*(1+treeEdgeWeight d*q)^2*
    (∑e:BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell),
      ∑f:BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell),
        if e=f then 0 else fullBoundaryWeight g o ell q z e*fullBoundaryWeight g o ell q z f)

theorem eventually_source_trace_conditional_drift (a b d:ℕ) (c β B:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c)
    (hβ:0<β) (hβc:β≤c/32) (hB:0≤B):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      (graphBall g.graph o (logarithmicRadius (c/4) d N)).IsTree→
      let ell:=actualCavityDepth a d N z-1
      let T:=graphBallVertices g.graph o ell
      let selector:=logarithmicRadius (c/4) d N/4
      ‖finiteComplexMean (fun S:LocalSamplingFiber g.graph T=>
          (g.labelledResampledGraph T (Equiv.refl (BoundaryOrientedEdge g.graph T)) S selector).G z o o)-
        regularRootValue d ell (g.Q z) z-
        traceBoundaryCorrectionCoefficient g o ell (g.Q z) z*trivialPole N d z‖≤
        ‖(treeEdgeWeight d)^2‖*sourceConditionalCellError g a β B (Equiv.refl (BoundaryOrientedEdge g.graph T)) selector
          (logarithmicRadius β d N) z*
          (∑e:BoundaryOrientedEdge g.graph T,‖fullBoundaryWeight g o ell (g.Q z) z e‖)^2+
        traceRootQuadraticConstant d β (sourceMinorEnlargementConstant d β B)*
          Real.log (N:ℝ)^(6*a+7)*(graphPaperError a d N (logarithmicRadius β d N) z)^2:=by
  let C1:=sourceMinorEnlargementConstant d β B
  have hC1:1≤C1:=by
    dsimp only [C1,sourceMinorEnlargementConstant]
    linarith [abs_nonneg (sourceDeletionConstant d β B)]
  have hCdel:sourceDeletionConstant d β B≤C1:=by
    dsimp only [C1,sourceMinorEnlargementConstant]
    linarith [le_abs_self (sourceDeletionConstant d β B)]
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_source_boundary_conditional_means a b d c β B ha hb hd hc hβ hβc hB,
    eventually_source_truncated_root_remainder a b d c β B C1 ha hb hd hc hβ hβc hC1,
    LocalLaw.RegularGraph.eventually_sourceOmegaWithRadii_subset_sourceOmegaPlusWithRadii a b d c β B C1
      (finiteOmega d) ha hb hd hc hβ hβc hB hC1 hCdel le_rfl,
    eventually_resampling_ball_budget a d hd,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,hdepth,
    Filter.eventually_ge_atTop 1] with N hcell hrem hplus hball hmargin hdepth hN
  intro g o z hz hfloor hzB badCount hold hTree
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let F:=BoundaryOrientedEdge g.graph T
  let labels:F≃BoundaryOrientedEdge g.graph T:=Equiv.refl _
  let selector:=logarithmicRadius (c/4) d N/4
  let P:=(g.deficient.restrict T).extensionGreen (g.Q z) z
  let root:=cavityBallRoot g.graph o ell
  let l:=truncatedBoundaryInner g T labels
  let R:LocalSamplingFiber g.graph T→Matrix T T ℂ:=fun S=>
    ((g.labelledResampledGraph T labels S selector).G z).submatrix Subtype.val Subtype.val
  let D:LocalSamplingFiber g.graph T→Matrix F F ℂ:=fun S=>
    g.sourceTruncatedBoundaryDefect T labels S selector (g.Q z) z
  let w:F→ℂ:=fun i=>P root (l i)
  let err:=sourceConditionalCellError g a β B labels selector (logarithmicRadius β d N) z
  let rem:=traceRootQuadraticConstant d β C1*Real.log (N:ℝ)^(6*a+7)*
    (graphPaperError a d N (logarithmicRadius β d N) z)^2
  let r:LocalSamplingFiber g.graph T→ℂ:=fun S=>(treeEdgeWeight d)^2*
    (∑i,∑j,(R S root (l i)-P root (l i))*D S i j*P (l j) root)
  have hell:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepth).2
  have hell1:1≤ell:=by
    have hh:(1:ℝ)≤(ell:ℝ):=by
      have hp:=(actualCavityDepth_radius_bounds a d N z hdepth).1
      dsimp only [ell]
      linarith
    exact_mod_cast hh
  have htreeT:(graphBall g.graph o ell).IsTree:=
    graphBall_tree_mono g.graph o (by dsimp only [ell];omega) hTree
  have hsmall:4*Nat.card T≤N:=g.ball_small o ell
    ((Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by omega:0<d+1) hell)).trans hball)
  letI:Nonempty (OutsideOrientedEdge g.graph T):=g.outside_edge_nonempty T (by omega) (by omega) hsmall
  letI:Nonempty (LocalSamplingFiber g.graph T):=⟨fun _=>Classical.choice inferInstance⟩
  have hcell':=hcell g o z hz hfloor hzB badCount hold hTree labels
  have hplus':=hplus g o z badCount hz hzB hfloor hold
  have hDdiag:∀i,‖finiteComplexMean (fun S=>D S i i)‖≤err:=by
    intro i
    simpa only [D,LocalLaw.RegularGraph.sourceTruncatedBoundaryDefect,Matrix.sub_apply,
      Matrix.submatrix_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,if_true,mul_one,
      switchedBoundaryEntry] using hcell'.1 i
  have hDoff:∀i j,i≠j→‖finiteComplexMean (fun S=>D S i j)-
      (1+treeEdgeWeight d*g.Q z)^2*trivialPole N d z‖≤err:=by
    intro i j hij
    simpa only [D,LocalLaw.RegularGraph.sourceTruncatedBoundaryDefect,Matrix.sub_apply,
      Matrix.submatrix_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,hij,if_false,mul_zero,
      sub_zero,switchedBoundaryEntry,trivialPole,mul_comm (treeEdgeWeight d) (d:ℂ)] using hcell'.2 i j hij
  have hsym:∀j,P (l j) root=w j:=fun j=>((g.deficient.restrict T).extensionGreen_isSymm (g.Q z) z).apply _ _
  have hidentity:∀S,R S root root-P root root=
      (treeEdgeWeight d)^2*(∑i,∑j,w i*w j*D S i j)+r S:=by
    intro S
    have hh:=truncated_root_row_identity g hd T labels S selector (g.Q z) z hz
      (g.Q_im_nonnegative z hz) root root
    change R S root root-P root root=_ at hh
    rw [hh]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change P root (l i)*D S i j*P (l j) root=w i*w j*D S i j
    rw [hsym]
    dsimp only [w]
    ring
  have hrem':∀S,‖r S‖≤rem:=fun S=>
    hrem g o z hz hfloor hzB (finiteOmega d) badCount hplus' hTree labels S root
  have hh:=finite_boundary_mean_aggregation (fun S=>R S root root) r D w (P root root)
    ((treeEdgeWeight d)^2) ((1+treeEdgeWeight d*g.Q z)^2*trivialPole N d z)
    err rem hidentity hDdiag hDoff hrem'
  have hdiag:P root root=regularRootValue d ell (g.Q z) z:=
    full_ball_extension_diagonal g hd o ell hell1 htreeT (g.Q z) z hz (g.Q_im_nonnegative z hz)
  rw [hdiag] at hh
  have heq:traceBoundaryCorrectionCoefficient g o ell (g.Q z) z*trivialPole N d z=
      (treeEdgeWeight d)^2*((1+treeEdgeWeight d*g.Q z)^2*trivialPole N d z)*
        (∑i:F,∑j:F,if i=j then 0 else w i*w j):=by
    change ((treeEdgeWeight d)^2*(1+treeEdgeWeight d*g.Q z)^2*
      (∑i:F,∑j:F,if i=j then 0 else w i*w j))*trivialPole N d z=_
    ring
  change ‖finiteComplexMean (fun S=>R S root root)-regularRootValue d ell (g.Q z) z-
    traceBoundaryCorrectionCoefficient g o ell (g.Q z) z*trivialPole N d z‖≤
    ‖(treeEdgeWeight d)^2‖*err*(∑i:F,‖w i‖)^2+rem
  rw [heq]
  exact hh

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.eventually_source_trace_conditional_drift
