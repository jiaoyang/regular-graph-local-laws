import LocalLaw.SourcePartialInnerMappedRows
import LocalLaw.PartialInnerChargeSupport
import LocalLaw.PartialInnerDiagonalChange
import LocalLaw.OmittedInnerWholeParameters
import LocalLaw.SourceFullUpperKernelDecay

/-! Source-realized omitted-T normalization with charged-column sums. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceOmittedInnerRowsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
set_option maxHeartbeats 3000000

def omittedInnerRowConstant (d:ℕ)(β B C1:ℝ):ℝ:=
  (|sourceFullUpperKernelCap d β B C1|+1)*(d:ℝ)*partialInnerMappedRowCoefficient d β

namespace RegularGraph

theorem eventually_source_omitted_inner_rows (a b d:ℕ)(c β B C1:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hC1:1≤C1):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:RegularGraph N d)(o:Fin N)(z q:ℂ),
      0<z.im→‖z‖≤B→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→0≤q.im→
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z)→
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d)→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y:Fin N),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      ∀(_hx:x∉T)(_hy:y∉T),
      let selector:=logarithmicRadius (c/4) d N/4
      let h:=g.labelledResampledGraph T labels samples selector
      let r:=effectiveModelRadius a d N β
      let S:=pairBallVertices h.graph x y r
      let K:Set (Tᶜ:Set (Fin N)):={v|v.val∈S}
      let upper:=(h.deficient.delete T).restrict K
      let lower:=(h.deficient.partialInnerAmbient T S).restrict K
      ∀u:K,u.val.val=x∨u.val.val=y→∀v:K,
      ‖upper.extensionGreen q z u v-lower.extensionGreen q z u v‖≤
        omittedInnerRowConstant d β B C1*(Real.log (N:ℝ)^(2*a)*physicalTransfer d z^(r/2-1)+
          Real.log (N:ℝ)^(2*a+1)*graphPaperError a d N (logarithmicRadius β d N) z):=by
  let Cup:=|sourceFullUpperKernelCap d β B C1|+1
  let C:=partialInnerMappedRowCoefficient d β
  let Count:ℝ:=(d:ℝ)*((d:ℝ)+1)
  let Total:=Cup*(d:ℝ)*C
  have hCup:0≤Cup:=by dsimp only [Cup];positivity
  have hC:0≤C:=by
    have hc:=finiteExtraReferenceConstant_ge_one d hd
    have hA:0≤fullRestrictionLogCap d β:=(fullRestrictionLogCap_properties d β).1
    unfold C partialInnerMappedRowCoefficient partialInnerOldRowCoefficient sourcePartialEndpointRowCap
    positivity
  filter_upwards [eventually_source_partial_inner_mapped_rows a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_full_upper_kernel_decay a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_formal_edge_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_selected_counts a d ha hd,
    eventually_resampling_radius_margin a d 2 6 β hd hβ,
    eventually_log_ge_nat 1,Filter.eventually_ge_atTop 1]
    with N hmapped hupper hedge hcount hradius hlog hN
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let s:=g.admissibleState T labels samples
  let h:=g.labelledResampledGraph T labels samples selector
  let r:=effectiveModelRadius a d N β
  let S:=pairBallVertices h.graph x y r
  let K:Set (Tᶜ:Set (Fin N)):={v|v.val∈S}
  let Tm:Set S:={v|v.val∈T}
  let M:=(h.deficient.restrict S).delete Tm
  let lower:=(h.deficient.partialInnerAmbient T S).restrict K
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  intro hx hy
  let J:Type:={v:K//h.deficient.partialInnerOmittedCharge T S v.val≠0}
  let φ:=restrictionDeletionGraphIso h.graph S T Tm (fun _=>Iff.rfl)
  let f:J↪↥(Tmᶜ:Set S):=
    { toFun:=fun j=>φ.symm j.val
      inj':=fun i j hh=>Subtype.ext (φ.symm.injective hh) }
  let F:=Cup*(L^2*physicalTransfer d z^(r/2-1)+L^3*ε)
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hL0:0≤L:=by dsimp only [L];linarith
  have ht:0≤physicalTransfer d z^(r/2-1):=pow_nonneg (physicalTransfer_pos d hd z).le _
  have hF:0≤F:=by dsimp only [F];positivity
  have hr2:2≤r:=by dsimp only [r,effectiveModelRadius,modelRadiusLoss];omega
  have hS:S⊆s.fullTwoTargetVertices selector r x y:=s.switched_full_pair_subset_old_augmentation selector r x y
  have hg:=h.deficient.partialInnerAmbient_restrict_green T S Tm (fun _=>Iff.rfl) q z
  have hboundary:Nat.card (BoundaryOrientedEdge h.graph T)=Nat.card (BoundaryOrientedEdge g.graph T):=by
    calc
      _=Nat.card ι:=Nat.card_congr (s.fullResample selector).boundary.symm
      _=Nat.card (BoundaryOrientedEdge g.graph T):=Nat.card_congr s.boundary
  have hmu:(Nat.card (BoundaryOrientedEdge h.graph T):ℝ)≤Count*L^(2*a-4):=by
    rw [hboundary]
    exact (hcount g o z).2
  have hq2:‖q‖≤2:=(hedge z q hz hzB hfloor hprior).1
  have hdR:(3:ℝ)≤d:=Nat.cast_le.mpr hd
  have hk:0<(d:ℝ)-1:=by linarith
  have hratio:‖q‖/((d:ℝ)-1)≤1:=(div_le_one hk).mpr (hq2.trans (by linarith))
  have hJ:(Fintype.card J:ℝ)≤(3*(d:ℝ)*((d:ℝ)+1))*L^(2*a-4):=by
    have hn:Nat.card J≤Nat.card (BoundaryOrientedEdge h.graph T):=
      h.deficient.partialInnerOmittedCharge_support_card T S K
    have hj:(Fintype.card J:ℝ)≤(Nat.card (BoundaryOrientedEdge h.graph T):ℝ):=by
      simpa only [Nat.card_eq_fintype_card] using (Nat.cast_le (α:=ℝ).mpr hn)
    have hnonneg:0≤Count*L^(2*a-4):=by dsimp only [Count];positivity
    have htriple:Count*L^(2*a-4)≤3*(Count*L^(2*a-4)):=by linarith
    exact hj.trans (hmu.trans (htriple.trans_eq (by dsimp only [Count];ring)))
  have hlowSum (v:K):(∑j:J,‖lower.extensionGreen q z j.val v‖)≤C*L^(2*a-2):=by
    have hn:=(hmapped g o z q hz hzB hfloor hq hprior hballs labels samples x y S hS f hJ (φ.symm v)).2
    change (∑j:J,‖M.extensionGreen q z (f j) (φ.symm v)‖)≤C*L^(2*a-2) at hn
    have he (j:J):lower.extensionGreen q z j.val v=M.extensionGreen q z (f j) (φ.symm v):=by
      have hh:=congrArg (fun A:Matrix (Tmᶜ:Set S) (Tmᶜ:Set S) ℂ=>A (f j) (φ.symm v)) hg
      change lower.extensionGreen q z (φ (φ.symm j.val)) (φ (φ.symm v))=_ at hh
      simpa only [φ.apply_symm_apply] using hh
    simpa only [he] using hn
  intro u hu v
  have hcharged:∀j:K,h.deficient.partialInnerOmittedCharge T S j.val≠0→
      ‖((h.deficient.delete T).restrict K).extensionGreen q z u j‖≤F:=by
    intro j hj
    have hdpth:=h.deficient.partialInnerOmittedCharge_pair_depth T x y r j hj
    have hrad:2*(r/2-1)+2≤r:=by omega
    have hdist:(r:ℕ∞)≤h.graph.edist u.val.val j.val.val:=by
      rcases hu with hu|hu
      · rw [hu];exact hdpth.1
      · rw [hu];exact hdpth.2
    have hu':=hupper g o z q hz hzB hfloor hq hprior hballs labels samples ⟨x,hx⟩ ⟨y,hy⟩ u j (r/2-1)
      ((ENat.coe_le_coe.mpr hrad).trans hdist)
    have hCupLe:sourceFullUpperKernelCap d β B C1≤Cup:=by
      dsimp only [Cup]
      linarith [le_abs_self (sourceFullUpperKernelCap d β B C1)]
    have hnn:0≤L^2*physicalTransfer d z^(r/2-1)+L^3*ε:=by positivity
    have hbig:=mul_le_mul_of_nonneg_right hCupLe hnn
    exact hu'.trans (by dsimp only [F];nlinarith only [hbig])
  let diag:K→ℂ:=fun j=>-q*(((h.deficient.partialInnerOmittedCharge T S j.val:ℝ)/((d:ℝ)-1)):ℂ)
  have hweighted:(∑j:K,‖diag j‖*‖lower.extensionGreen q z j v‖)≤(d:ℝ)*(C*L^(2*a-2)):=by
    have hh:=weighted_sum_le_subtype_sum (fun j:K=>h.deficient.partialInnerOmittedCharge T S j.val≠0)
      (fun j=>‖diag j‖) (fun j=>‖lower.extensionGreen q z j v‖) (d:ℝ)
      (fun _=>norm_nonneg _) (fun _=>norm_nonneg _) (fun j hj=>by
        have hj':h.deficient.partialInnerOmittedCharge T S j.val=0:=not_ne_iff.mp hj
        simp only [diag,hj',Nat.cast_zero,zero_div,Complex.ofReal_zero,mul_zero,norm_zero])
      (fun j=>h.deficient.partialInnerOmittedCharge_norm_le hd T S q hq2 j.val)
    exact hh.trans (mul_le_mul_of_nonneg_left (hlowSum v) (Nat.cast_nonneg _))
  have hh:=inverse_diagonal_change_weighted_one_sided
    (((h.deficient.delete T).restrict K).extensionMatrix q z)
    (lower.extensionMatrix q z)
    (((h.deficient.delete T).restrict K).extensionMatrix_isUnit hd q z hz hq)
    (lower.extensionMatrix_isUnit hd q z hz hq)
    diag (h.deficient.partialInnerAmbient_restrict_matrix_difference T S K q z) u v F
    ((d:ℝ)*(C*L^(2*a-2))) hF (fun j hj=>hcharged j (by
      intro hz0
      apply hj
      simp only [diag,hz0,Nat.cast_zero,zero_div,Complex.ofReal_zero,mul_zero])) hweighted
  refine hh.trans_eq ?_
  have hp2:L^2*L^(2*a-2)=L^(2*a):=by rw [←pow_add];congr 1;omega
  have hp3:L^3*L^(2*a-2)=L^(2*a+1):=by rw [←pow_add];congr 1;omega
  change F*((d:ℝ)*(C*L^(2*a-2)))=
    Total*(L^(2*a)*physicalTransfer d z^(r/2-1)+L^(2*a+1)*ε)
  dsimp only [F,Total]
  calc
    _=(Cup*(d:ℝ)*C)*((L^2*L^(2*a-2))*physicalTransfer d z^(r/2-1)+(L^3*L^(2*a-2))*ε):=by ring
    _=_:=by rw [hp2,hp3]

end RegularGraph
end LocalLaw
