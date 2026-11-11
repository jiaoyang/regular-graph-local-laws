import SpectralConsequences.SourceBoundaryConditionalMeans
import SpectralConsequences.SourceCavityQuadraticRemainder
import SpectralConsequences.BoundaryMeanAggregation
import SpectralConsequences.CavityBoundaryWeights

/-! # Actual conditional drift of a neighbor-deleted root

The weights are the literal old truncated-minor Green entries. Their
q-dependent off-diagonal correction is kept exact at this stage.
-/
open scoped BigOperators
open Filter
noncomputable section
set_option maxHeartbeats 2400000
namespace SpectralConsequences
open LocalLaw
local instance sourceCavityConditionalDriftDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ}

def cavityMeanCorrection (g:LocalLaw.RegularGraph N d) (o:Fin N) (ell:ℕ) (hell:2≤ell)
    (j:graphBallVertices g.graph o ell) (hjo:g.graph.Adj j.val o) (q z:ℂ):ℂ:=
  (treeEdgeWeight d)^2*(1+treeEdgeWeight d*q)^2*
    ((N:ℂ)⁻¹*(treeEdgeWeight d*(d:ℂ)-z)⁻¹)*
    (∑i:BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell),
      ∑k:BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell),
        if i=k then 0 else cavityBoundaryWeight g o ell hell j hjo q z i*
          cavityBoundaryWeight g o ell hell j hjo q z k)

theorem eventually_source_cavity_conditional_drift (a b d:ℕ) (c β B:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hβ:0<β) (hβc:β≤c/32) (hB:0≤B):
    ∀ᶠ N:ℕ in atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      (graphBall g.graph o (logarithmicRadius (c/4) d N)).IsTree→
      let ell:=actualCavityDepth a d N z-1
      let T:=graphBallVertices g.graph o ell
      let selector:=logarithmicRadius (c/4) d N/4
      ∃hell:2≤ell,∀(j:T)(hjo:g.graph.Adj j.val o),
      ‖finiteComplexMean (fun samples:LocalSamplingFiber g.graph T=>
        let new:=g.labelledResampledGraph T (Equiv.refl _) samples selector
        new.retainedPhysicalMinor T j z (g.truncatedCavityRoot o ell j hjo)
          (g.truncatedCavityRoot o ell j hjo))-
        cavityIterate z (g.Q z) (ell+1)-cavityMeanCorrection g o ell hell j hjo (g.Q z) z‖≤
        sourceConditionalCellError g a β B (Equiv.refl (BoundaryOrientedEdge g.graph T)) selector (logarithmicRadius β d N) z*
          (∑i:BoundaryOrientedEdge g.graph T,‖cavityBoundaryWeight g o ell hell j hjo (g.Q z) z i‖)^2+
        cavityRootQuadraticConstant d β (sourceMinorEnlargementConstant d β B)*Real.log (N:ℝ)^(6*a+7)*
          (graphPaperError a d N (logarithmicRadius β d N) z)^2:=by
  let C1:=sourceMinorEnlargementConstant d β B
  have hC1:1≤C1:=by
    dsimp only [C1,sourceMinorEnlargementConstant]
    linarith [abs_nonneg (sourceDeletionConstant d β B)]
  have hCdel:sourceDeletionConstant d β B≤C1:=by
    dsimp only [C1,sourceMinorEnlargementConstant]
    linarith [le_abs_self (sourceDeletionConstant d β B)]
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_source_boundary_conditional_means a b d c β B ha hb hd hc hβ hβc hB,
    eventually_source_cavity_quadratic_remainder a b d c β B C1 ha hb hd hc hβ hβc hC1,
    LocalLaw.RegularGraph.eventually_sourceOmegaWithRadii_subset_sourceOmegaPlusWithRadii a b d c β B C1
      (finiteOmega d) ha hb hd hc hβ hβc hB hC1 hCdel le_rfl,
    eventually_resampling_ball_budget a d hd,hdepth,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    Filter.eventually_ge_atTop 1]
    with N hcell hquad hplus hbudget hdepthN hmargin hN
  intro g o z hz hfloor hzB badCount hold htree
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let q:=g.Q z
  have hplus':=hplus g o z badCount hz hzB hfloor hold
  obtain ⟨hell,hremainder⟩:=hquad g o z hz hfloor hzB (finiteOmega d) badCount hplus' htree
  refine ⟨hell,?_⟩
  intro j hjo
  let I:=BoundaryOrientedEdge g.graph T
  let labels:I≃BoundaryOrientedEdge g.graph T:=Equiv.refl _
  let P:=((g.deficient.restrict T).deleteVertex j).extensionGreen q z
  let root:=g.truncatedCavityRoot o ell j hjo
  let l:=g.truncatedCavityBoundaryInner o ell hell j hjo
  let w:I→ℂ:=cavityBoundaryWeight g o ell hell j hjo q z
  let R:=fun S:LocalSamplingFiber g.graph T=>
    (g.labelledResampledGraph T labels S selector).retainedPhysicalMinor T j z
  let D:=fun S:LocalSamplingFiber g.graph T=>g.sourceTruncatedBoundaryDefect T labels S selector q z
  let coeff:ℂ:=(treeEdgeWeight d)^2
  let θ:=(1+treeEdgeWeight d*q)^2*((N:ℂ)⁻¹*(treeEdgeWeight d*(d:ℂ)-z)⁻¹)
  let rem:=fun S:LocalSamplingFiber g.graph T=>
    coeff*(∑i:I,∑k:I,(R S root (l i)-P root (l i))*D S i k*P (l k) root)
  let e:=sourceConditionalCellError g a β B labels selector (logarithmicRadius β d N) z
  let Qrem:=cavityRootQuadraticConstant d β C1*L^(6*a+7)*ε^2
  have hellBound:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepthN).2
  have hT:4*Nat.card T≤N:=g.ball_small o ell
    ((Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by omega:0<d+1) hellBound)).trans hbudget)
  letI : Nonempty (OutsideOrientedEdge g.graph T):=g.outside_edge_nonempty T (by omega) (by omega) hT
  letI : Nonempty (LocalSamplingFiber g.graph T):=⟨fun _=>Classical.choice inferInstance⟩
  have htreeSucc:=(graphBall_tree_mono g.graph o (show ell+1≤logarithmicRadius (c/4) d N by omega) htree)
  have hP:P root root=cavityIterate z q (ell+1):=
    g.truncated_neighbor_cavity_diagonal hd o ell j hjo htreeSucc q z hz (g.Q_im_nonnegative z hz)
  have hsym:P.IsSymm:=((g.deficient.restrict T).deleteVertex j).extensionGreen_isSymm q z
  have hc':‖coeff‖≤1:=by convert cut_coefficient_norm_le_one d hd using 1
  have hid (S:LocalSamplingFiber g.graph T):
      R S root root-cavityIterate z q (ell+1)=coeff*(∑i:I,∑k:I,w i*w k*D S i k)+rem S:=by
    rw [←hP]
    have hh:=g.cavity_minor_row_identity hd o ell hell j hjo labels S selector q z hz
      (g.Q_im_nonnegative z hz) root
    change R S root root-P root root=coeff*(∑i:I,∑k:I,P root (l i)*D S i k*P (l k) root)+rem S at hh
    rw [hh]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    have hs:P (l k) root=P root (l k):=hsym.apply root (l k)
    rw [hs]
    change P root (l i)*D S i k*P root (l k)=P root (l i)*P root (l k)*D S i k
    ring
  have hmeans:=hcell g o z hz hfloor hzB badCount hold htree labels
  have hdg (i:I):‖finiteComplexMean (fun S=>D S i i)‖≤e:=by
    simpa only [D,LocalLaw.RegularGraph.sourceTruncatedBoundaryDefect,Matrix.sub_apply,
      Matrix.submatrix_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,
      if_true,mul_one,switchedBoundaryEntry] using hmeans.1 i
  have hof (i k:I) (hik:i≠k):‖finiteComplexMean (fun S=>D S i k)-θ‖≤e:=by
    simpa only [D,LocalLaw.RegularGraph.sourceTruncatedBoundaryDefect,Matrix.sub_apply,
      Matrix.submatrix_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,
      hik,if_false,mul_zero,sub_zero,switchedBoundaryEntry] using hmeans.2 i k hik
  have hr (S:LocalSamplingFiber g.graph T):‖rem S‖≤Qrem:=
    hremainder j hjo labels S root
  have hm:=finite_boundary_mean_aggregation (fun S:LocalSamplingFiber g.graph T=>R S root root)
    rem (fun S i k=>D S i k) w (cavityIterate z q (ell+1)) coeff θ e Qrem hid hdg hof hr
  have he:0≤e:=by
    dsimp only [e,sourceConditionalCellError,sourceCellBadCap,sourceCellEntryCap,
      sourceSelectedMinorConstant,sourceMinorEnlargementConstant,sourceGreenEntryCap,
      sourceGreenPivotCap,eventMass,localSamplingWeight,finiteUniformWeight]
    have hC:=finiteReferenceConstant_ge_one d hd
    positivity
  have hcorr:cavityMeanCorrection g o ell hell j hjo q z=
      coeff*θ*(∑i:I,∑k:I,if i=k then 0 else w i*w k):=by
    dsimp only [cavityMeanCorrection,coeff,θ,w]
    ring
  rw [hcorr]
  apply hm.trans
  change ‖coeff‖*e*(∑i:I,‖w i‖)^2+Qrem≤e*(∑i:I,‖w i‖)^2+Qrem
  apply add_le_add_right _ Qrem
  calc
    _=‖coeff‖*(e*(∑i:I,‖w i‖)^2):=by ring
    _≤_:=mul_le_of_le_one_left (mul_nonneg he (sq_nonneg _)) hc'

end RegularGraph
end SpectralConsequences
