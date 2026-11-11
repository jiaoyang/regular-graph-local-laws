import SpectralConsequences.OldTreeFormalValues
import SpectralConsequences.OldTreeRootAlgebra
import SpectralConsequences.SourceRecursionSmallness
import LocalLaw.IndependentRadiusSourceCaps
import LocalLaw.FiniteCavityResidual

/-! On the original source event, both local residuals at every original
tree center have the genuine logarithmic epsilon scale. -/
open Filter
noncomputable section
set_option maxHeartbeats 2200000
namespace SpectralConsequences
open LocalLaw
local instance oldTreeRootCapsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def oldTreeRootErrorConstant (d:ℕ) (β B:ℝ):ℝ :=
  2*oldTreeFormalConstant d β B+
    |1+(sourceGreenEntryCap d+8)*sourceGreenPivotCap d B| * oldTreeFormalConstant d β B+
    4*(1+Real.sqrt (B+2))

namespace RegularGraph

theorem eventually_old_tree_root_caps (a b d:ℕ) (c β B:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hβ:0<β) (hβc:β≤c/32) (hB:0≤B) :
    ∀ᶠ N:ℕ in atTop, ∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z →
      (graphBall g.graph o (logarithmicRadius (c/4) d N)).IsTree →
      let ell:=actualCavityDepth a d N z-1
      let M:=oldTreeRootErrorConstant d β B*Real.log (N:ℝ)*
        graphPaperError a d N (logarithmicRadius β d N) z
      ‖g.G z o o-regularRootValue d ell (g.Q z) z‖≤M ∧
      ‖cavityAtVertex g.graph d z o-cavityIterate z (g.Q z) (ell+1)‖≤M := by
  filter_upwards [eventually_old_tree_formal_values a b d c β B ha hb hd hc hβ hβc,
    LocalLaw.RegularGraph.eventually_sourceOmegaWithRadii_green_caps a b d c β B ha hb hd hc hβ hβc hB,
    eventually_source_formal_kernel_bounds a b d c β B 1 1 ha hb hd hc hβ hβc (by norm_num) (by norm_num),
    eventually_source_formal_edge_bounds a b d c β B 1 ha hb hd hc hβ hβc (by norm_num),
    eventually_source_recursion_smallness a b d β ha hb hd hβ,
    eventually_actualCavityDepth_le_log a d hd,eventually_log_ge_nat 1,eventually_ge_atTop 1]
    with N hvalues hcaps hformal hedge hsmall hdepth hL hN
  intro g o z hz hzB hfloor badCount hold htree
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let q:=g.Q z
  let p:=rationalTreeReference (d-1) q
  let t:ℂ:=-q*treeEdgeWeight d
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let F:=oldTreeFormalConstant d β B
  let C:=sourceGreenEntryCap d
  let P:=sourceGreenPivotCap d B
  let H:=1+(C+8)*P
  let K:=oldTreeRootErrorConstant d β B
  have hε:0≤ε:=graphPaperError_nonnegative _ _ _ _ _ hN hz.le
  have hL':1≤L:=hL
  have hmul:0≤L*ε:=mul_nonneg (by linarith) hε
  have hF:0≤F:=by dsimp only [F,oldTreeFormalConstant];positivity
  have hC:0≤C:=by
    have hh:=finiteReferenceConstant_ge_one d hd
    dsimp only [C,sourceGreenEntryCap];linarith
  have hP:0≤P:=by
    have hh:=finiteReferenceConstant_ge_one d hd
    dsimp only [P,sourceGreenPivotCap];positivity
  have hH:0≤H:=by dsimp only [H];positivity
  have hprior:‖q-semicircleRoot z‖≤1*scalarScale (spectralScale z) ε:=by
    simpa only [one_mul] using hold.2.1
  have hf:=hformal z q hz hzB hfloor hprior
  have ht:‖t‖≤1:=by
    change ‖-q*treeEdgeWeight d‖≤1
    rw [neg_mul,norm_neg]
    simpa only [mul_comm] using (hedge z q hz hzB hfloor hprior).2
  have hq:q=p-p*t^2:=by
    have hprod:p*(q⁻¹-q*(treeEdgeWeight d)^2)=1:=by
      rw [←hf.2.2.2.1]
      exact mul_inv_cancel₀ hf.2.1
    have hi:q⁻¹*q=1:=inv_mul_cancel₀ hf.1
    dsimp only [t]
    linear_combination -q*hprod+p*hi
  have hv:=hvalues g o z hz hzB hfloor badCount hold htree
  have hg:=hcaps g z badCount hz hzB hfloor hold
  have hcav:‖cavityAtVertex g.graph d z o-q‖≤H*(F*L*ε):=
    cavityAtVertex_formal_error g (by omega) o z hz p t q C P (F*L*ε)
      hq hC hP (by positivity) hf.2.2.1 ht (fun v=>hg.1 v o) hg.2 hv.1 hv.2.1
  have hn:((ell+1:ℕ):ℝ)≤2*L:=by
    have hh:((actualCavityDepth a d N z:ℕ):ℝ)≤L:=hdepth z
    have hh':((ell+1:ℕ):ℝ)≤(actualCavityDepth a d N z:ℝ)+1:=by
      exact_mod_cast Nat.succ_le_succ (Nat.sub_le _ _)
    linarith
  have hsn:((ell+1:ℕ):ℝ)*‖q-semicircleRoot z‖≤1/2:=by
    have hp:=mul_le_mul_of_nonneg_left (show ‖q-semicircleRoot z‖≤scalarScale (spectralScale z) ε by
      simpa only [one_mul] using hprior) (show 0≤(ell:ℝ)+4 by positivity)
    have hh:=hsmall z hz hfloor
    have hn':((ell+1:ℕ):ℝ)≤(ell:ℝ)+4:=by push_cast;linarith
    exact (mul_le_mul_of_nonneg_right hn' (norm_nonneg _)).trans (hp.trans hh)
  have hres:=cavity_residual_of_weak_prior z q hz B ε 1 hzB hε (by norm_num) hprior (ell+1) hsn
  norm_num only [one_pow,mul_one] at hres
  have hres':‖q-cavityIterate z q (ell+1)‖≤4*(1+Real.sqrt (B+2))*L*ε:=by
    apply hres.trans
    have hh:=mul_le_mul_of_nonneg_right hn (show 0≤2*(1+Real.sqrt (B+2))*ε by positivity)
    convert hh using 1 <;> ring
  have htrace:‖g.G z o o-regularRootValue d ell q z‖≤2*F*L*ε:=by
    exact (norm_sub_le_norm_sub_add_norm_sub _ p _).trans
      ((add_le_add hv.1 (by simpa only [norm_sub_rev] using hv.2.2)).trans_eq (by ring))
  constructor
  · apply htrace.trans
    have hh:2*F≤K:=by
      dsimp only [K,oldTreeRootErrorConstant,F,H,C,P]
      have hh:0≤|1+(sourceGreenEntryCap d+8)*sourceGreenPivotCap d B| * oldTreeFormalConstant d β B+
          4*(1+Real.sqrt (B+2)):=by positivity
      linarith only [hh]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (by linarith)) hε
  · apply ((norm_sub_le_norm_sub_add_norm_sub _ q _).trans (add_le_add hcav hres')).trans
    have hHabs:H≤|H|:=le_abs_self _
    have hh:=mul_le_mul_of_nonneg_right hHabs (show 0≤F*L*ε by positivity)
    dsimp only [K,oldTreeRootErrorConstant,F,H,C,P] at *
    nlinarith only [hh,mul_nonneg hF hmul]

end RegularGraph
end SpectralConsequences
