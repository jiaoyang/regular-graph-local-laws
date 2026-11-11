import LocalLaw.SourceOmittedInnerRows
import LocalLaw.SourceFullNewTargetRows
import LocalLaw.FarInnerRestoration
import LocalLaw.FarInnerLogBudget
import LocalLaw.FullPairInnerRestorationContract

/-! The literal full pair and its retained-inner deletion agree at far roots.
All decay, endpoint rows, inner cardinalities and logarithmic absorption are derived. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceFullFarInnerDecidable (p:Prop):Decidable p:=Classical.propDecidable p
set_option maxHeartbeats 300000

def fullFarInnerKernelCoefficient (d:ℕ)(β B C1:ℝ):ℝ:=
  (|sourceFullUpperKernelCap d β B C1|+1)+omittedInnerRowConstant d β B C1

def fullFarInnerBudgetCoefficient (d:ℕ)(β B C1:ℝ):ℝ:=
  ((d:ℝ)+1)*(d:ℝ)^2*sourceFullEndpointRowConstant d β*(fullFarInnerKernelCoefficient d β B C1)^2

namespace RegularGraph

theorem eventually_source_full_far_inner_restoration (a b d:ℕ)(c β B C1:ℝ)
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
      h.FullPairQuarterFarInnerRestoredAt T r z q x y _hx _hy (1/Real.log (N:ℝ)) :=by
  let Cup:=|sourceFullUpperKernelCap d β B C1|+1
  let Cn:=omittedInnerRowConstant d β B C1
  let Cf:=fullFarInnerKernelCoefficient d β B C1
  let Ctt:=sourceFullEndpointRowConstant d β
  let Budget:=fullFarInnerBudgetCoefficient d β B C1
  have hCup:0≤Cup:=by dsimp only[Cup];positivity
  have hCn:0≤Cn:=by
    have hC:=finiteExtraReferenceConstant_ge_one d hd
    have hA:0≤fullRestrictionLogCap d β:=(fullRestrictionLogCap_properties d β).1
    unfold Cn omittedInnerRowConstant partialInnerMappedRowCoefficient partialInnerOldRowCoefficient sourcePartialEndpointRowCap
    positivity
  have hCf:0≤Cf:=by change 0≤Cup+Cn;positivity
  have hCtt:=sourceFullEndpointRowConstant_nonnegative d β
  have hBudget:0≤Budget:=by dsimp only[Budget,fullFarInnerBudgetCoefficient];positivity
  filter_upwards [eventually_source_omitted_inner_rows a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_full_upper_kernel_decay a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_full_partial_endpoint_caps a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_selected_counts a d ha hd,
    eventually_far_inner_log_budget a b d β Budget ha hb hd hβ hBudget,
    eventually_resampling_radius_margin a d 2 20 β hd hβ,
    eventually_resampling_radius_margin a d 0 4 (c/4) hd (by positivity),
    eventually_log_ge_nat 1,Filter.eventually_ge_atTop 1] with N hnorm hupper htt hcounts hbudget hradius hselector hlog hN
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let s:=g.admissibleState T labels samples
  let h:=g.labelledResampledGraph T labels samples selector
  let r:=effectiveModelRadius a d N β
  let S:=pairBallVertices h.graph x y r
  let K:Set (Tᶜ:Set (Fin N)):={v|v.val∈S}
  let Tm:Set S:={v|v.val∈T}
  let M:=h.deficient.restrict S
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let ρ:=physicalTransfer d z
  let t:=ρ^(r/8-1)
  let F:=Cf*(L^(2*a)*t+L^(2*a+1)*ε)
  intro hx hy
  change h.FullPairQuarterFarInnerRestoredAt T r z q x y hx hy (1/L)
  unfold FullPairQuarterFarInnerRestoredAt
  intro hfar
  unfold FullPairInnerRestoredAt
  dsimp only
  let xS:S:=⟨x,Or.inl (center_mem_graphBall _ _ _)⟩
  let yS:S:=⟨y,Or.inr (center_mem_graphBall _ _ _)⟩
  let xo:(Tmᶜ:Set S):=⟨xS,hx⟩
  let yo:(Tmᶜ:Set S):=⟨yS,hy⟩
  let xl:K:=⟨⟨x,hx⟩,xS.property⟩
  let yl:K:=⟨⟨y,hy⟩,yS.property⟩
  let upper:=(h.deficient.delete T).restrict K
  let lower:=(h.deficient.partialInnerAmbient T S).restrict K
  let φ:=restrictionDeletionGraphIso h.graph S T Tm (fun _=>Iff.rfl)
  have hg:=h.deficient.partialInnerAmbient_restrict_green T S Tm (fun _=>Iff.rfl) q z
  have hr8:8≤r:=by dsimp only[r,effectiveModelRadius,modelRadiusLoss];omega
  have hs:1≤selector:=by dsimp only[selector];omega
  have hL0:0≤L:=by dsimp only[L];linarith
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hρ0:0≤ρ:=(physicalTransfer_pos d hd z).le
  have hρ1:ρ≤1:=by dsimp only[ρ];nlinarith [physicalTransfer_sq_le_half d hd z]
  have ht0:0≤t:=pow_nonneg hρ0 _
  have hF:0≤F:=mul_nonneg hCf (add_nonneg
    (mul_nonneg (pow_nonneg hL0 _) ht0) (mul_nonneg (pow_nonneg hL0 _) hε))
  have hS:S⊆s.fullTwoTargetVertices selector r x y:=s.switched_full_pair_subset_old_augmentation selector r x y
  have hn:=hnorm g o z q hz hzB hfloor hq hprior hballs labels samples x y hx hy
  have hcaps:=htt g o z q hz hzB hfloor hq hprior hballs labels samples x y hs S hS
  have hroot (u:(Tmᶜ:Set S))(hu:u=xo∨u=yo)(b:Tm)(w:(Tmᶜ:Set S))(hwb:M.graph.Adj w.val b.val):
      ‖(M.delete Tm).extensionGreen q z u w‖≤F:=by
    let ul:K:=φ u
    let wl:K:=φ w
    have hdist:((r/4:ℕ):ℕ∞)≤h.graph.edist u.val.val w.val.val:=by
      have hfar':((r/4:ℕ):ℕ∞)<h.graph.edist u.val.val b.val.val:=by
        rcases hu with rfl|rfl
        · exact (hfar ⟨b.val.val,b.property⟩).1
        · exact (hfar ⟨b.val.val,b.property⟩).2
      have hnot:b.val.val∉pairBallVertices h.graph u.val.val u.val.val (r/4):=by
        intro hb
        exact not_lt_of_ge (hb.elim id id) hfar'
      exact (omitted_pair_neighbor_far h.graph u.val.val u.val.val b.val.val w.val.val (r/4) hnot
        hwb).1
    have hrad:2*(r/8-1)+2≤r/4:=by omega
    have hu':ul.val.val=x∨ul.val.val=y:=by
      rcases hu with rfl|rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hUp:=hupper g o z q hz hzB hfloor hq hprior hballs labels samples ⟨x,hx⟩ ⟨y,hy⟩ ul wl (r/8-1)
      ((ENat.coe_le_coe.mpr hrad).trans hdist)
    have hNorm:=hn ul hu' wl
    have hCupLe:sourceFullUpperKernelCap d β B C1≤Cup:=by
      dsimp only[Cup];linarith [le_abs_self (sourceFullUpperKernelCap d β B C1)]
    have hupper':‖upper.extensionGreen q z ul wl‖≤Cup*(L^2*t+L^3*ε):=by
      have hh:=mul_le_mul_of_nonneg_right hCupLe (add_nonneg (mul_nonneg (pow_nonneg hL0 2) ht0) (mul_nonneg (pow_nonneg hL0 3) hε))
      exact hUp.trans (by
        change sourceFullUpperKernelCap d β B C1*L^2*t+sourceFullUpperKernelCap d β B C1*L^3*ε≤_
        calc
          _=sourceFullUpperKernelCap d β B C1*(L^2*t+L^3*ε):=by ring
          _≤_:=hh)
    have hNorm':‖upper.extensionGreen q z ul wl-lower.extensionGreen q z ul wl‖≤
        Cn*(L^(2*a)*ρ^(r/2-1)+L^(2*a+1)*ε):=hNorm
    have hpow:ρ^(r/2-1)≤t:=pow_le_pow_of_le_one hρ0 hρ1 (by omega)
    have h2:L^2≤L^(2*a):=pow_le_pow_right₀ hlog (by omega)
    have h3:L^3≤L^(2*a+1):=pow_le_pow_right₀ hlog (by omega)
    have hUpScale:Cup*(L^2*t+L^3*ε)≤Cup*(L^(2*a)*t+L^(2*a+1)*ε):=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right h2 ht0)
        (mul_le_mul_of_nonneg_right h3 hε)) hCup
    have hNormScale:Cn*(L^(2*a)*ρ^(r/2-1)+L^(2*a+1)*ε)≤Cn*(L^(2*a)*t+L^(2*a+1)*ε):=
      mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hpow (pow_nonneg hL0 _)) _) hCn
    have hlow:‖lower.extensionGreen q z ul wl‖≤F:=by
      have hh:=norm_sub_le_norm_sub_add_norm_sub (lower.extensionGreen q z ul wl) (upper.extensionGreen q z ul wl) 0
      simp only[sub_zero] at hh
      have hrev:‖lower.extensionGreen q z ul wl-upper.extensionGreen q z ul wl‖≤
          Cn*(L^(2*a)*ρ^(r/2-1)+L^(2*a+1)*ε):=by
        calc
          _=‖upper.extensionGreen q z ul wl-lower.extensionGreen q z ul wl‖:=norm_sub_rev _ _
          _≤_:=hNorm'
      have hb:=(hh.trans (add_le_add hrev hupper')).trans (add_le_add hNormScale hUpScale)
      exact hb.trans_eq (by change Cn*_+Cup*_= (Cup+Cn)*_;ring)
    have he:=congrArg (fun A:Matrix (Tmᶜ:Set S) (Tmᶜ:Set S) ℂ=>A u w) hg
    change lower.extensionGreen q z (φ u) (φ w)=(M.delete Tm).extensionGreen q z u w at he
    rw[←he]
    exact hlow
  let ei:=s.fullPartialEmbedding selector S hs
  let j:Tm↪s.FullEndpointIndex selector S:=
    { toFun:=fun v=>Sum.inl ⟨v.val.val,v.val.property,Or.inl v.property⟩
      inj':=by
        intro u v huv
        have he:=congrArg (fun i=>ei i) huv
        exact Subtype.ext he }
  have heq (v:Tm):ei (j v)=v.val:=rfl
  have hTcol (b:Tm):(∑c:Tm,‖M.extensionGreen q z c.val b.val‖)≤Ctt*L^(a-1):=by
    calc
      _=(∑c:Tm,‖M.extensionGreen q z (ei (j c)) (ei (j b))‖):=by simp only[heq]
      _=(∑i∈Finset.univ.image j,‖M.extensionGreen q z (ei i) (ei (j b))‖):=by
        rw [Finset.sum_image]
        intro u _ v _ he
        exact j.injective he
      _≤∑i,‖M.extensionGreen q z (ei i) (ei (j b))‖:=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=>norm_nonneg _)
      _≤_:=hcaps.2 (j b)
  have hraw:=M.extensionGreen_far_inner_restoration hd Tm q z hz hq xo yo F (Ctt*L^(a-1)) hF
    (hroot xo (Or.inl rfl)) (hroot yo (Or.inr rfl)) hTcol
  have hTm:(Nat.card Tm:ℝ)≤((d:ℝ)+1)*L^(2*a-4):=by
    let f:Tm→T:=fun v=>⟨v.val.val,v.property⟩
    have hf:Function.Injective f:=by
      intro u v he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun w:T=>w.val) he
    have hh:Nat.card Tm≤Nat.card T:=Nat.card_le_card_of_injective f hf
    exact (Nat.cast_le (α:=ℝ).mpr hh).trans (hcounts g o z).1
  have hscaled:(Nat.card Tm:ℝ)*(d:ℝ)^2*F^2*(Ctt*L^(a-1))≤
      Budget*L^(3*a-5)*(L^(2*a)*t+L^(2*a+1)*ε)^2:=by
    have hh:=mul_le_mul_of_nonneg_right hTm (show 0≤(d:ℝ)^2*F^2*(Ctt*L^(a-1)) by positivity)
    have hp:L^(2*a-4)*L^(a-1)=L^(3*a-5):=by rw[←pow_add];congr 1;omega
    calc
      _=(Nat.card Tm:ℝ)*((d:ℝ)^2*F^2*(Ctt*L^(a-1))):=by ring
      _≤(((d:ℝ)+1)*L^(2*a-4))*((d:ℝ)^2*F^2*(Ctt*L^(a-1))):=hh
      _=(((d:ℝ)+1)*(d:ℝ)^2*Ctt*Cf^2)*(L^(2*a-4)*L^(a-1))*(L^(2*a)*t+L^(2*a+1)*ε)^2:=by dsimp only[F];ring
      _=Budget*L^(3*a-5)*(L^(2*a)*t+L^(2*a+1)*ε)^2:=by rw[hp];rfl
  have hfinal:‖M.extensionGreen q z xS yS-(M.delete Tm).extensionGreen q z xo yo‖≤1/L:=
    (hraw.trans hscaled).trans (hbudget z hz hfloor)
  have he:=congrArg (fun A:Matrix (Tmᶜ:Set S) (Tmᶜ:Set S) ℂ=>A xo yo) hg
  change lower.extensionGreen q z xl yl=(M.delete Tm).extensionGreen q z xo yo at he
  rw [←he] at hfinal
  rw [←h.deficient_P r z q x y]
  exact hfinal

end RegularGraph
end LocalLaw
