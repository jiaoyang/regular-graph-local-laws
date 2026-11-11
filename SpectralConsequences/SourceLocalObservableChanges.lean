import SpectralConsequences.OldTreeRootCaps
import SpectralConsequences.SourceWardVarianceBound

/-! The genuine local cavity and diagonal observables change by O(log N
 epsilon) under the paired source/tree events. The Ward variance and both
 finite-recursion absorption conditions are derived, rather than supplied. -/
open Filter
noncomputable section
set_option maxHeartbeats 1800000
namespace SpectralConsequences
open LocalLaw
local instance sourceLocalObservableChangeDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceLocalObservableChangeConstant (d:ℕ)(β B:ℝ):ℝ :=
  2*oldTreeRootErrorConstant d β B+32

namespace RegularGraph

theorem eventually_source_local_observable_changes (a b d:ℕ)(c β B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hB:0≤B):
    ∀ᶠ N:ℕ in atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ‖z‖≤B → ∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z →
      (graphBall g.graph o (logarithmicRadius (c/4) d N)).IsTree →
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let new:=g.labelledResampledGraph T labels samples (logarithmicRadius (c/4) d N/4)
      new.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z →
      (graphBall new.graph o (logarithmicRadius (c/4) d N)).IsTree →
      let M:=sourceLocalObservableChangeConstant d β B*Real.log (N:ℝ)*
        graphPaperError a d N (logarithmicRadius β d N) z
      ‖cavityAtVertex g.graph d z o-cavityAtVertex new.graph d z o‖≤M ∧
      ‖g.G z o o-new.G z o o‖≤M := by
  filter_upwards [eventually_old_tree_root_caps a b d c β B ha hb hd hc hβ hβc hB,
    eventually_source_ward_variance_bound a b d c β B ha hb hd hc hβ hβc hB,
    eventually_source_moment_variance_small a b d β (sourceWardVarianceConstant d B)
      ha hb hd hβ (sourceWardVarianceConstant_nonnegative d B hd hB),
    eventually_source_recursion_smallness a b d β ha hb hd hβ,
    eventually_log_ge_nat 1,eventually_ge_atTop 1] with N hlocal hward hvariance hsmall hL hN
  intro g o z hz hfloor hzB badCount hold htree ι _ labels samples
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let new:=g.labelledResampledGraph T labels samples (logarithmicRadius (c/4) d N/4)
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let K:=oldTreeRootErrorConstant d β B
  intro hnew hnewtree
  have ho:=hlocal g o z hz hzB hfloor badCount hold htree
  have hn:=hlocal new o z hz hzB hfloor badCount hnew hnewtree
  have hΔ:‖g.Q z-new.Q z‖≤ε:=
    (hward g o z hz hfloor hzB badCount hold labels samples hnew).1.trans
      (hvariance z hz hfloor).1.2.2
  have hε:0≤ε:=graphPaperError_nonnegative _ _ _ _ _ hN hz.le
  have hL':1≤L:=hL
  have herr:ε≤L*ε:=le_mul_of_one_le_left hε hL'
  have hs:=hsmall z hz hfloor
  have hgo:((ell:ℝ)+4)*‖g.Q z-semicircleRoot z‖≤1/2:=
    (mul_le_mul_of_nonneg_left hold.2.1 (by positivity)).trans hs
  have hgn:((ell:ℝ)+4)*‖new.Q z-semicircleRoot z‖≤1/2:=
    (mul_le_mul_of_nonneg_left hnew.2.1 (by positivity)).trans hs
  have hco:((ell+1:ℕ):ℝ)*‖g.Q z-semicircleRoot z‖≤1/2:=by
    have hh:((ell+1:ℕ):ℝ)≤(ell:ℝ)+4:=by push_cast;linarith
    exact (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans hgo
  have hcn:((ell+1:ℕ):ℝ)*‖new.Q z-semicircleRoot z‖≤1/2:=by
    have hh:((ell+1:ℕ):ℝ)≤(ell:ℝ)+4:=by push_cast;linarith
    exact (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans hgn
  have hY:‖cavityIterate z (g.Q z) (ell+1)-cavityIterate z (new.Q z) (ell+1)‖≤4*ε:=
    (cavityIterate_lipschitz_of_small (semicircleRoot_equation z) (semicircleRoot_norm_le_one z)
      (ell+1) hco hcn).trans (mul_le_mul_of_nonneg_left hΔ (by norm_num))
  have hX:‖regularRootValue d ell (g.Q z) z-regularRootValue d ell (new.Q z) z‖≤32*ε:=
    (regularRootValue_lipschitz_of_small d ell hd (g.Q z) (new.Q z) z hz
      (g.Q_im_nonnegative z hz) (new.Q_im_nonnegative z hz) hgo hgn).trans
        (mul_le_mul_of_nonneg_left hΔ (by norm_num))
  have hthree (v w x y:ℂ):‖v-y‖≤‖v-w‖+‖w-x‖+‖x-y‖:=by
    exact (norm_sub_le_norm_sub_add_norm_sub v x y).trans
      (add_le_add_right (norm_sub_le_norm_sub_add_norm_sub v w x) _)
  constructor
  · have hh:‖cavityAtVertex g.graph d z o-cavityAtVertex new.graph d z o‖≤
        K*L*ε+4*ε+K*L*ε:=
      (hthree _ (cavityIterate z (g.Q z) (ell+1)) (cavityIterate z (new.Q z) (ell+1)) _).trans
        (add_le_add (add_le_add ho.2 hY) (by simpa only [norm_sub_rev] using hn.2))
    change ‖_‖≤(2*K+32)*L*ε
    nlinarith only [hh,herr,hε]
  · have hh:‖g.G z o o-new.G z o o‖≤K*L*ε+32*ε+K*L*ε:=
      (hthree _ (regularRootValue d ell (g.Q z) z) (regularRootValue d ell (new.Q z) z) _).trans
        (add_le_add (add_le_add ho.1 hX) (by simpa only [norm_sub_rev] using hn.1))
    change ‖_‖≤(2*K+32)*L*ε
    nlinarith only [hh,herr]

end RegularGraph
end SpectralConsequences
