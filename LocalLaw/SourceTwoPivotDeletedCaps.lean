import LocalLaw.PartialFirstDeletionCaps
import LocalLaw.SourcePartialCovarianceModels
import LocalLaw.SourceFormalEdgeBounds

/-! # Realized source caps after deleting the local retained first endpoints

Every graph, mask, pivot and error budget is instantiated from the original
weak source event and its structural radius budget. No new-pair reference
class or deleted-kernel bound is an input.
-/

open Filter
noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance sourceTwoPivotDeletedDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceTwoPivotInverseCap (B:ℝ):ℝ:=2*(|B|+2)
def sourceTwoPivotDeletedCap (d:ℕ)(B:ℝ):ℝ:=
  2*finiteExtraReferenceConstant d+4*sourceTwoPivotInverseCap B*(2*finiteExtraReferenceConstant d)^2

namespace RegularGraph

theorem eventually_source_two_pivot_deleted_caps (a b d:ℕ)(c β B C1:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hC1:1≤C1) :
    ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z:ℂ)(Cq badCount:ℕ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z →
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y:((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      let S:=pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
      let W:=s.partialFirstRemovedSet selector S
      ∀i j:(Wᶜ:Set S),
        ‖(((g.deficient.delete T).restrict S).delete W).extensionGreen (g.Q z) z i j‖≤
          sourceTwoPivotDeletedCap d B := by
  let P:=sourceTwoPivotInverseCap B
  let D:=|sourcePartialCovarianceConstant d β B C1|+1
  have hP:0≤P:=by dsimp only [P,sourceTwoPivotInverseCap];positivity
  have hD:0≤D:=by dsimp only [D];positivity
  filter_upwards [eventually_old_switched_pair_reference_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_partial_q_covariance_models a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_formal_kernel_bounds a b d c β B C1 0 ha hb hd hc hβ hβc hC1 (by norm_num),
    eventually_source_formal_kernel_inverse_bound a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_formal_edge_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    eventually_log_ge_nat (4*P*D)]
    with N href hcov hformal hinv hedge hnum hmargin hlarge
  intro g o z Cq badCount hz hzB hfloor hplus hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let S:=pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
  let W:=s.partialFirstRemovedSet selector S
  let q:=g.Q z
  let p:=rationalTreeReference (d-1) q
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let σ:=D*L*ε
  have num:=hnum z hz hfloor
  have hL:1≤L:=num.log_one
  have hL0:0≤L:=le_trans (by norm_num) hL
  have hε:0≤ε:=num.error_nonnegative
  have hσ:0≤σ:=by dsimp only [σ];positivity
  have hprior:‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z) ε:=hplus.cavity
  have hf:=hformal z q hz hzB hfloor hprior
  have hi:=hinv z q hz hzB hfloor hprior
  have he:=hedge z q hz hzB hfloor hprior
  have hpnorm:‖p⁻¹‖≤P:=by
    rw [hf.2.2.2.1]
    have hα:‖treeEdgeWeight d‖^2≤1:=by
      rw [treeEdgeWeight_norm_sq d hd]
      have hdR:(3:ℝ)≤d:=Nat.cast_le.mpr hd
      exact (div_le_one (by linarith)).mpr (by linarith)
    have hqα:‖q*treeEdgeWeight d^2‖≤2:=by
      rw [norm_mul,norm_pow]
      exact (mul_le_mul he.1 hα (sq_nonneg _) (by norm_num:(0:ℝ)≤2)).trans_eq (by ring)
    exact (norm_sub_le _ _).trans ((add_le_add hi.2 hqα).trans (by
      dsimp only [P,sourceTwoPivotInverseCap]
      linarith [le_abs_self B]))
  have hC:0≤2*finiteExtraReferenceConstant d:=by
    have hh:=finiteExtraReferenceConstant_ge_one d hd
    positivity
  have hreference:=href g o z Cq badCount hz hfloor hplus hballs labels samples x y
  have hcovariance: g.oldPartialQCovarianceBound T labels samples selector S z σ:=by
    have hh:=(hcov g o z Cq badCount hz hzB hfloor hplus hballs labels samples x y).1
    intro i j
    exact (hh i j).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by dsimp only [D];linarith [le_abs_self (sourcePartialCovarianceConstant d β B C1)]) hL0)
      hε)
  have hcard:Nat.card W≤2:=s.partialFirstRemovedSet_new_pair_card selector r (by
    dsimp only [selector,r]
    omega) x y
  have hεL : L^2*ε≤1:=by
    have hCsq:1≤C1^2:=by nlinarith
    have hεscale:ε≤C1^2*ε:=le_mul_of_one_le_left hε hCsq
    have hp:L^2≤L^4:=pow_le_pow_right₀ hL (by omega)
    exact (mul_le_mul hp hεscale hε (pow_nonneg hL0 _)).trans (by
      simpa only [mul_assoc,mul_comm,mul_left_comm] using num.error_scaled)
  have hsmall:2*P*σ≤1/2:=by
    have hh:=mul_le_mul_of_nonneg_right hlarge (mul_nonneg hL0 hε)
    have hh' : 4*P*D*(L*ε)≤L^2*ε:=by
      change 4*P*D*(L*ε)≤L*(L*ε) at hh
      nlinarith only [hh]
    calc
      _=(4*P*D*(L*ε))/2:=by dsimp only [σ];ring
      _≤(L^2*ε)/2:=div_le_div_of_nonneg_right hh' (by norm_num)
      _≤1/2:=div_le_div_of_nonneg_right hεL (by norm_num)
  have hblock:=s.partialFirst_covariance_block selector S
    (((g.deficient.delete T).restrict S).extensionGreen q z) q p (treeEdgeWeight d) σ hcovariance
  have hblock' : ∀i j:W,‖((((g.deficient.delete T).restrict S).extensionGreen q z).submatrix
      (Subtype.val:W→S) (Subtype.val:W→S)-p•1) i j‖≤σ := by
    intro i j
    by_cases hij:i=j
    · subst j
      simpa only [Matrix.sub_apply,Matrix.submatrix_apply,Matrix.smul_apply,smul_eq_mul,
        Matrix.one_apply,if_pos rfl,mul_one] using hblock i i
    · simpa only [Matrix.sub_apply,Matrix.submatrix_apply,Matrix.smul_apply,smul_eq_mul,
        Matrix.one_apply,if_neg hij,mul_zero,sub_zero] using hblock i j
  exact ((g.deficient.delete T).restrict S).two_pivot_deleted_kernel_bound hd W hcard q z p hz
    (g.Q_im_nonnegative z hz) hf.2.1 (2*finiteExtraReferenceConstant d) P σ hC hP hσ
    hreference.2.2.2.2.1 hpnorm hblock' hsmall

end RegularGraph
end LocalLaw
