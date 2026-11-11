import LocalLaw.SourcePartialInnerPolynomialCaps
import LocalLaw.PartialInnerDiagonalChange
import LocalLaw.OmittedInnerWholeParameters
import LocalLaw.SourceFullUpperKernelDecay

/-! Source-realized omitted-T normalization on the actual new full pair. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceOmittedInnerComparisonDecidable (p:Prop):Decidable p:=Classical.propDecidable p
set_option maxHeartbeats 3000000

def omittedInnerComparisonConstant (d:ℕ)(β B C1:ℝ):ℝ:=
  (|sourceFullUpperKernelCap d β B C1|+1)*partialInnerGlobalCoefficient d β*((d:ℝ)*((d:ℝ)+1))

theorem partialInnerGlobalCoefficient_nonnegative (d:ℕ)(β:ℝ)(hd:3≤d):
    0≤partialInnerGlobalCoefficient d β:=by
  have hC:=finiteExtraReferenceConstant_ge_one d hd
  have hA:0≤fullRestrictionLogCap d β:=(fullRestrictionLogCap_properties d β).1
  unfold partialInnerGlobalCoefficient partialInnerOldRowCoefficient sourcePartialEndpointRowCap
  positivity

namespace RegularGraph

theorem eventually_source_omitted_inner_comparison (a b d:ℕ)(c β B C1:ℝ)
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
      ∀(hx:x∉T)(hy:y∉T),
      let selector:=logarithmicRadius (c/4) d N/4
      let h:=g.labelledResampledGraph T labels samples selector
      let r:=effectiveModelRadius a d N β
      let S:=pairBallVertices h.graph x y r
      let K:Set (Tᶜ:Set (Fin N)):={v|v.val∈S}
      let xl:K:=⟨⟨x,hx⟩,Or.inl (center_mem_graphBall _ _ _)⟩
      let yl:K:=⟨⟨y,hy⟩,Or.inr (center_mem_graphBall _ _ _)⟩
      let upper:=(h.deficient.delete T).restrict K
      let lower:=(h.deficient.partialInnerAmbient T S).restrict K
      let err:=‖upper.extensionGreen q z xl yl-lower.extensionGreen q z xl yl‖
      (err≤omittedInnerComparisonConstant d β B C1*(Real.log (N:ℝ)^(3*a-3)*physicalTransfer d z^(r/2-1)+
          Real.log (N:ℝ)^(3*a-2)*graphPaperError a d N (logarithmicRadius β d N) z))∧
        err≤1/Real.log (N:ℝ):=by
  let Cup:=|sourceFullUpperKernelCap d β B C1|+1
  let C:=partialInnerGlobalCoefficient d β
  let Count:ℝ:=(d:ℝ)*((d:ℝ)+1)
  let Total:=Cup*C*Count
  have hCup:0≤Cup:=by dsimp only [Cup];positivity
  have hC:=partialInnerGlobalCoefficient_nonnegative d β hd
  have hCount:0≤Count:=by dsimp only [Count];positivity
  have hTotal:0≤Total:=by dsimp only [Total];positivity
  filter_upwards [eventually_source_partial_inner_global_caps a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_full_upper_kernel_decay a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_formal_edge_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_selected_counts a d ha hd,
    eventually_omitted_inner_whole_error_budget a b d β Total ha hb hd hβ hTotal,
    eventually_resampling_radius_margin a d 2 6 β hd hβ,
    eventually_log_ge_nat 1,Filter.eventually_ge_atTop 1]
    with N hpoly hupper hedge hcount hbudget hradius hlog hN
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
  let xl:K:=⟨⟨x,hx⟩,Or.inl (center_mem_graphBall _ _ _)⟩
  let yl:K:=⟨⟨y,hy⟩,Or.inr (center_mem_graphBall _ _ _)⟩
  let F:=Cup*(L^2*physicalTransfer d z^(r/2-1)+L^3*ε)
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hL0:0≤L:=by dsimp only [L];linarith
  have ht:0≤physicalTransfer d z^(r/2-1):=pow_nonneg (physicalTransfer_pos d hd z).le _
  have hF:0≤F:=by dsimp only [F];positivity
  have hr2:2≤r:=by dsimp only [r,effectiveModelRadius,modelRadiusLoss];omega
  have hS:S⊆s.fullTwoTargetVertices selector r x y:=s.switched_full_pair_subset_old_augmentation selector r x y
  have hp:=hpoly g o z q hz hzB hfloor hq hprior hballs labels samples x y S hS
  let φ:=restrictionDeletionGraphIso h.graph S T Tm (fun _=>Iff.rfl)
  have hg:=h.deficient.partialInnerAmbient_restrict_green T S Tm (fun _=>Iff.rfl) q z
  have hlow:∀v:K,‖lower.extensionGreen q z v yl‖≤C*L^(a-1):=by
    intro v
    have he:=congrArg (fun A:Matrix (Tmᶜ:Set S) (Tmᶜ:Set S) ℂ=>A (φ.symm v) (φ.symm yl)) hg
    change lower.extensionGreen q z (φ (φ.symm v)) (φ (φ.symm yl))=M.extensionGreen q z (φ.symm v) (φ.symm yl) at he
    rw [φ.apply_symm_apply,φ.apply_symm_apply] at he
    rw [he]
    exact hp _ _
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
  have hcharged:∀v:K,h.deficient.partialInnerOmittedCharge T S v.val≠0→
      ‖((h.deficient.delete T).restrict K).extensionGreen q z xl v‖≤F:=by
    intro v hv
    have hdpth:=h.deficient.partialInnerOmittedCharge_pair_depth T x y r v hv
    have hrad:2*(r/2-1)+2≤r:=by omega
    have hdist:((2*(r/2-1)+2:ℕ):ℕ∞)≤(s.fullResample selector).graph.edist xl.val.val v.val.val:=
      (ENat.coe_le_coe.mpr hrad).trans hdpth.1
    have hu:=hupper g o z q hz hzB hfloor hq hprior hballs labels samples ⟨x,hx⟩ ⟨y,hy⟩ xl v (r/2-1) hdist
    have hCupLe:sourceFullUpperKernelCap d β B C1≤Cup:=by
      dsimp only [Cup]
      linarith [le_abs_self (sourceFullUpperKernelCap d β B C1)]
    have hnn:0≤L^2*physicalTransfer d z^(r/2-1)+L^3*ε:=by positivity
    have hbig:=mul_le_mul_of_nonneg_right hCupLe hnn
    exact hu.trans (by dsimp only [F];nlinarith only [hbig])
  have hh:=h.deficient.partialInnerAmbient_one_sided_change hd T S K q z hz hq xl yl F
    (C*L^(a-1)) hF (by positivity) hcharged hlow
  have hcoef:0≤F*(C*L^(a-1)):=by positivity
  have hr:F*(C*L^(a-1))*(‖q‖/((d:ℝ)-1))*(Nat.card (BoundaryOrientedEdge h.graph T):ℝ)≤
      F*(C*L^(a-1))*(Count*L^(2*a-4)):=by
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hcoef) (Nat.cast_nonneg _)).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hmu hcoef)
  have hp2:L^2*L^(a-1)*L^(2*a-4)=L^(3*a-3):=by rw [←pow_add,←pow_add];congr 1;omega
  have hp3:L^3*L^(a-1)*L^(2*a-4)=L^(3*a-2):=by rw [←pow_add,←pow_add];congr 1;omega
  have he:F*(C*L^(a-1))*(Count*L^(2*a-4))=
      Total*(L^(3*a-3)*physicalTransfer d z^(r/2-1)+L^(3*a-2)*ε):=by
    dsimp only [F,Total]
    calc
      _=(Cup*C*Count)*((L^2*L^(a-1)*L^(2*a-4))*physicalTransfer d z^(r/2-1)+
          (L^3*L^(a-1)*L^(2*a-4))*ε):=by ring
      _=_:=by rw [hp2,hp3]
  have herr:= (hh.trans hr).trans_eq he
  exact ⟨herr,herr.trans (hbudget z hz hfloor)⟩

end RegularGraph
end LocalLaw
