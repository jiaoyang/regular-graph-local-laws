import LocalLaw.SourceOutsideRowFromColumn
import LocalLaw.SourceInsideRow
import LocalLaw.SourceCavityAverageCertificate
import LocalLaw.SourceAnalyticGood
import LocalLaw.StrongSourceClosureInputs

/-! # Actual source improvements supply the strong local certificate

All inside-row and cavity estimates are proved source conclusions. This
assembly theorem takes the named outside-column good event as an explicit
hypothesis. `SourceOutsideCompleteColumn` supplies that event from the proved
sampling conditions, and `CompleteStrongCertificate` combines the results.
-/

noncomputable section
namespace LocalLaw
local instance strongSourceCertificateDecidable (p:Prop) : Decidable p:=Classical.propDecidable p

def sourceStrongRowU (d J:ℕ)(β C1 Eout:ℝ):ℝ:=
  |sourceInsideBaseConstant d J β C1|+|sourceOutsideRowBaseConstant d J β C1 Eout|+1

def sourceStrongRowV (d:ℕ)(β B:ℝ):ℝ:=
  |sourceInsideFeedbackConstant d β B|+|sourceOutsideRowFeedbackConstant d β B|+1

def sourceStrongResidualM (d J:ℕ)(β C1:ℝ):ℝ:=2*(|sourceCavityAverageConstant d J β C1|+1)

namespace RegularGraph

theorem eventually_source_strong_certificate_of_column (a b d qReject Cq:ℕ)(c β γ B C1 Eout:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)
    (hγ:c/4<γ)(hgap:γ+β<1)(hB:0≤B)(hC1:1≤C1)(hEout:0≤Eout)
    (hCdel:sourceDeletionConstant d β B≤C1)(hCq:finiteOmega d≤Cq):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀badCount:ℕ,badCount≤⌊(N:ℝ)^γ⌋₊ →
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell:=actualCavityDepth a d N z-1
      let R:=logarithmicRadius (c/4) d N
      let T:=graphBallVertices g.graph o ell
      let r:=effectiveModelRadius a d N β
      let ε:=graphPaperError a d N (logarithmicRadius β d N) z
      let L:=Real.log (N:ℝ)
      let J:=sourceRejectionConstant Cq qReject
      let gnew:=g.labelledResampledGraph T labels samples (R/4)
      gnew.SourceOmegaWithRadii a r (logarithmicRadius β d N) R (finiteOmega d) badCount z →
      g.SourceAnalyticGood a qReject Cq c β C1 o z samples →
      g.SourceOutsideColumnGood a c β Eout o z labels samples →
      ∀D:StrongClosureBudget z (semicircleRoot z) (spectralScale z) ε,
      D.depth=actualCavityDepth a d N z → D.L=L → D.U=sourceStrongRowU d J β C1 Eout →
      D.V=sourceStrongRowV d β B → D.residualConstant=sourceStrongResidualM d J β C1 →
      D.rowBase=D.U*ε/D.L → D.rowFeedback=D.V*D.L^2 → D.cavityError=D.residualConstant*ε/(2*D.L^4) →
      StrongCavityRowCertificate (gnew.Q z) (semicircleRoot z) z (spectralScale z) ε D
        (gnew.G z) (fun w=>gnew.P r z w) (cavityAtVertex gnew.graph d z) (nonTreeCenters gnew.graph R) o:=by
  let J:=sourceRejectionConstant Cq qReject
  filter_upwards [eventually_source_inside_row a b d J c β γ B C1 Cq ha hb hd hc hβ hβc hγ hgap hB hC1 hCdel hCq,
    eventually_source_cavity_average_certificate a b d J c β γ B C1 Cq ha hb hd hc hβ hβc hγ hgap hB hC1 hCdel hCq,
    eventually_source_outside_row_from_column a b d J c β B C1 Eout ha hb hd hc hβ hβc hC1 hB hEout,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc]
    with N hinside hcavity houtside hmargins
  intro g o z hz hzB hfloor badCount hbad hplus ι _ labels samples
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let R:=logarithmicRadius (c/4) d N
  let T:=graphBallVertices g.graph o ell
  let r:=effectiveModelRadius a d N β
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let L:=Real.log (N:ℝ)
  let gnew:=g.labelledResampledGraph T labels samples (R/4)
  intro htarget hgood hcolumn D hdepth hlog hU hV hM hbase hfeedback hcav
  have hLp:0<D.L:=by have hh:=D.large;linarith
  have hL1:1≤D.L:=by have hh:=D.large;linarith
  have hε:0≤ε:=D.errorPositive.le
  have hF:0≤gnew.sourceFeedback z:=by dsimp only [sourceFeedback];positivity
  have hUi:sourceInsideBaseConstant d J β C1≤D.U:=by
    rw [hU];unfold sourceStrongRowU
    linarith [le_abs_self (sourceInsideBaseConstant d J β C1),abs_nonneg (sourceOutsideRowBaseConstant d J β C1 Eout)]
  have hUo:sourceOutsideRowBaseConstant d J β C1 Eout≤D.U:=by
    rw [hU];unfold sourceStrongRowU
    linarith [le_abs_self (sourceOutsideRowBaseConstant d J β C1 Eout),abs_nonneg (sourceInsideBaseConstant d J β C1)]
  have hVi:sourceInsideFeedbackConstant d β B≤D.V:=by
    rw [hV];unfold sourceStrongRowV
    linarith [le_abs_self (sourceInsideFeedbackConstant d β B),abs_nonneg (sourceOutsideRowFeedbackConstant d β B)]
  have hVo:sourceOutsideRowFeedbackConstant d β B≤D.V:=by
    rw [hV];unfold sourceStrongRowV
    linarith [le_abs_self (sourceOutsideRowFeedbackConstant d β B),abs_nonneg (sourceInsideFeedbackConstant d β B)]
  have hMc:sourceCavityAverageConstant d J β C1≤D.residualConstant/2:=by
    rw [hM];unfold sourceStrongResidualM
    linarith [le_abs_self (sourceCavityAverageConstant d J β C1)]
  have hdepthPos:1≤D.depth:=by
    by_contra h
    have he:D.depth=0:=by omega
    have hh:=D.nonresonant
    simp only [he,cavitySum,Finset.range_zero,Finset.sum_empty,norm_zero] at hh
    linarith
  have hdepth':D.depth=ell+1:=by dsimp only [ell];omega
  constructor
  · intro hnotbad
    have htree:(graphBall gnew.graph o R).IsTree:=by
      by_contra ht
      exact hnotbad ((nonTreeCenters_membership gnew.graph R o).mpr ht)
    let s:=g.admissibleState T labels samples
    have hfit:ell+r+1≤R/8:=by have hh:=hmargins.2.2.2 z;change r+ell+1≤R/8 at hh;omega
    have hsTree:(graphBall g.graph o (R/8)).IsTree:=
      s.fullResample_tree_implies_source_eighth_tree R o ell rfl (by omega) htree
    have hellTree:=graphBall_tree_mono g.graph o (show ell≤R/8 by omega) hsTree
    have habs:=hcavity g o z hz hzB hfloor badCount hbad hplus labels samples htarget
      hgood.1 hgood.2.1 (hgood.2.2.2 hellTree) htree
    rw [←hlog] at habs
    rw [hdepth',hcav]
    exact (gnew.sourceCavityResidual_norm_bound (by omega) ell o z).trans
      (habs.trans ((mul_le_mul_of_nonneg_right hMc (div_nonneg hε (pow_nonneg hLp.le 4))).trans_eq (by ring)))
  · intro y
    change ‖gnew.G z o y-gnew.P r z (gnew.Q z) o y‖≤D.rowBase+D.rowFeedback*gnew.sourceFeedback z
    by_cases hy:y∈T
    · have hh:=hinside g o z hz hzB hfloor badCount hbad hplus labels samples htarget hgood.1 hgood.2.1 hgood.2.2.1 ⟨y,hy⟩
      rw [←hlog] at hh
      have hb:sourceInsideBaseConstant d J β C1*(ε/D.L^2)≤D.rowBase:=by
        calc
          _≤D.U*(ε/D.L^2):=mul_le_mul_of_nonneg_right hUi (div_nonneg hε (sq_nonneg _))
          _≤D.U*(ε/D.L):=mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hε hLp (by nlinarith only [sq_nonneg (D.L-1),hL1])) D.UNonnegative
          _=_:=by rw [hbase];ring
      have hv:sourceInsideFeedbackConstant d β B*D.L^2*gnew.sourceFeedback z≤D.rowFeedback*gnew.sourceFeedback z:=by
        rw [hfeedback]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hVi (sq_nonneg _)) hF
      exact hh.trans (add_le_add hb hv)
    · have hh:=houtside g o z hz hzB hfloor Cq badCount hplus labels samples htarget hgood.1 hgood.2.1 hcolumn y hy
      rw [←hlog] at hh
      have hb:sourceOutsideRowBaseConstant d J β C1 Eout*ε/D.L≤D.rowBase:=by
        rw [hbase]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hUo hε) hLp.le
      have hv:sourceOutsideRowFeedbackConstant d β B*D.L^2*gnew.sourceFeedback z≤D.rowFeedback*gnew.sourceFeedback z:=by
        rw [hfeedback]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hVo (sq_nonneg _)) hF
      exact hh.trans (add_le_add hb hv)

end RegularGraph
end LocalLaw
