import LocalLaw.SourceObservationParameters
import LocalLaw.CavityMinorModelBounds
import LocalLaw.FiniteBoundaryContinuity

/-! Uniform entry caps and boundary-parameter continuity for the actual
truncated tree model and every deleted-neighbor model. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceTruncatedParameterBoundsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def truncatedParameterContinuityConstant (d:ℕ) (β:ℝ):ℝ:=
  16*finiteExtraReferenceConstant d^2*sourceObservationLogCap d β

namespace RegularGraph

theorem eventually_source_truncated_parameter_bounds (a b d:ℕ) (c β B:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hβ:0<β) (hβc:β≤c/32):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z q:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→0≤q.im→
      ‖q-semicircleRoot z‖≤scalarScale (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z)→
      let ell:=actualCavityDepth a d N z-1
      let T:=graphBallVertices g.graph o ell
      (graphBall g.graph o ell).IsTree→
      let C:=2*finiteExtraReferenceConstant d
      let H:=truncatedParameterContinuityConstant d β*Real.log (N:ℝ)
      let P:=(g.deficient.restrict T).extensionGreen
      (∀x y,‖P q z x y‖≤C ∧ ‖P (semicircleRoot z) z x y‖≤C ∧
        ‖P q z x y-P (semicircleRoot z) z x y‖≤H*‖q-semicircleRoot z‖) ∧
      (∀j:T,let K:=((g.deficient.restrict T).deleteVertex j).extensionGreen
        ∀x y,‖K q z x y‖≤C ∧ ‖K (semicircleRoot z) z x y‖≤C ∧
          ‖K q z x y-K (semicircleRoot z) z x y‖≤H*‖q-semicircleRoot z‖):=by
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_sourceObservationBounds a b d c β B 1 ha hb hd hc hβ hβc (by norm_num),
    eventually_resampling_radius_margin a d 3 6 β hd hβ,hdepth] with N hnum hroom hdepth
  intro g o z q hz hfloor hq hprior
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let r:=effectiveModelRadius a d N β
  let Robs:=singletonObservationDiameter d r
  let L:=Real.log (N:ℝ)
  let A:=sourceObservationLogCap d β
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let C:=finiteExtraReferenceConstant d
  intro htree
  have num:=hnum z hz hfloor
  have hell:ell≤r:=by
    have hh:=(actualCavityDepth_radius_bounds a d N z hdepth).2
    dsimp only [ell,r,effectiveModelRadius,modelRadiusLoss]
    omega
  have hfeedback:= (DeficientGraph.weak_localization_feedback_budgets d hd z q hz B ε L A
    num.error_nonnegative num.log_one num.log_cap_nonnegative
    (by simpa only [one_pow,one_mul] using num.error_scaled) hprior Robs (4*r+1)
    num.diameter_log num.pair_log num.localization_large).1
  have hC:0≤C:=(by norm_num:(0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have ht:physicalTransfer d z≤1:=by
    have hh:=physicalTransfer_le_critical d z
    have hd':(3:ℝ)≤d:=by exact_mod_cast hd
    have hs:1≤Real.sqrt ((d:ℝ)-1):=Real.le_sqrt_of_sq_le (by norm_num;linarith)
    exact hh.trans (inv_le_one_of_one_le₀ hs)
  have happly {V:Type} [Fintype V] [DecidableEq V] (M:DeficientGraph V d)
      (hbudget:M.ComponentFiniteReferenceBudget) (hdiam:∀x y,M.graph.dist x y≤Robs) (x y:V):
      ‖M.extensionGreen q z x y‖≤2*C ∧ ‖M.extensionGreen (semicircleRoot z) z x y‖≤2*C ∧
        ‖M.extensionGreen q z x y-M.extensionGreen (semicircleRoot z) z x y‖≤
          truncatedParameterContinuityConstant d β*L*‖q-semicircleRoot z‖:=by
    have hm:‖semicircleRoot z-semicircleRoot z‖*C*coreConvolutionConstant (finiteOmega d+1)*((Robs:ℝ)+1)≤1/2:=by
      simp only [sub_self,norm_zero,zero_mul];norm_num
    have hkernel (u:ℂ) (hu:0≤u.im)
        (hs:‖u-semicircleRoot z‖*C*coreConvolutionConstant (finiteOmega d+1)*((Robs:ℝ)+1)≤1/2):
        ‖M.extensionGreen u z x y‖≤2*C:=by
      have hh:=M.componentwise_finite_kernel_decay hd hbudget u z hz hu Robs hdiam hs x y
      exact hh.trans (mul_le_of_le_one_right (by positivity) (pow_le_one₀ (physicalTransfer_pos d hd z).le ht))
    refine ⟨hkernel q hq hfeedback,hkernel _ (semicircleRoot_im_pos hz).le hm,?_⟩
    apply (M.componentwise_boundary_two_parameter hd hbudget q (semicircleRoot z) z hz hq
      (semicircleRoot_im_pos hz).le Robs hdiam hfeedback hm x y).trans
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left num.diameter_log
      (show 0≤16*C^2 by positivity)) (norm_nonneg _)).trans_eq
      (by dsimp only [truncatedParameterContinuityConstant,C];ring)
  have hdiam:∀x y,(g.deficient.restrict T).graph.dist x y≤Robs:=by
    intro x y
    apply (graphBall_distance_le_twice_radius g.graph o ell x y).trans
    dsimp only [Robs,singletonObservationDiameter]
    nlinarith only [hell,Nat.zero_le (finiteOmega d)]
  have hbudget:(g.deficient.restrict T).ComponentFiniteReferenceBudget:=
    ((g.deficient.restrict T).connected_zero_component_budget htree.isConnected (fun _=>rfl)
      (by change graphExcess (graphBall g.graph o ell)≤_;rw [tree_graphExcess_zero _ htree];exact Nat.zero_le _)).to_componentFinite
  refine ⟨happly _ hbudget hdiam,?_⟩
  intro j
  have hdiamj:∀x y,((g.deficient.restrict T).deleteVertex j).graph.dist x y≤Robs:=by
    intro x y
    apply (g.truncatedMinor_distance_bound o ell j htree x y).trans
    dsimp only [Robs,singletonObservationDiameter]
    exact Nat.mul_le_mul_left _ (by omega)
  exact happly _ (g.truncatedMinor_component_budget o ell j htree) hdiamj

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.eventually_source_truncated_parameter_bounds
