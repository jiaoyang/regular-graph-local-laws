import LocalLaw.SourceFullCommonOutsideDecay
import LocalLaw.SourceFullNewTargetRows
import LocalLaw.FarInnerRestoration
import LocalLaw.FarInnerLogBudget
import LocalLaw.FullCommonInnerRestorationContract

/-! The actual common full region and its inner deletion agree at far roots.
All decay, endpoint rows, inner cardinalities and logarithmic absorption are derived. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceFullCommonFarDecidable (p:Prop):Decidable p:=Classical.propDecidable p
set_option maxHeartbeats 300000

def fullCommonFarInnerKernelCoefficient (d:ℕ)(β B C1:ℝ):ℝ:=
  |sourceRegionalEntireLeading d β B C1|+|sourceRegionalEntireError d β B C1|+1

def fullCommonFarInnerBudgetCoefficient (d:ℕ)(β B C1:ℝ):ℝ:=
  ((d:ℝ)+1)*(d:ℝ)^2*sourceFullEndpointRowConstant d β*(fullCommonFarInnerKernelCoefficient d β B C1)^2

namespace RegularGraph

theorem eventually_source_full_common_far_inner_restoration (a b d:ℕ)(c β B C1:ℝ)
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
      let r:=effectiveModelRadius a d N β
      g.FullCommonQuarterFarInnerRestoredAt T labels samples selector r z q x y _hx _hy (1/Real.log (N:ℝ)) :=by
  let Af:=sourceRegionalEntireLeading d β B C1
  let Df:=sourceRegionalEntireError d β B C1
  let Cf:=fullCommonFarInnerKernelCoefficient d β B C1
  let Ctt:=sourceFullEndpointRowConstant d β
  let Budget:=fullCommonFarInnerBudgetCoefficient d β B C1
  have hCf:0≤Cf:=by dsimp only[Cf,fullCommonFarInnerKernelCoefficient];positivity
  have hAf:Af≤Cf:=by change Af≤|Af|+|Df|+1;linarith [le_abs_self Af,abs_nonneg Df]
  have hDf:Df≤Cf:=by change Df≤|Af|+|Df|+1;linarith [le_abs_self Df,abs_nonneg Af]
  have hCtt:=sourceFullEndpointRowConstant_nonnegative d β
  have hBudget:0≤Budget:=by dsimp only[Budget,fullCommonFarInnerBudgetCoefficient];positivity
  filter_upwards [eventually_source_full_common_outside_decay a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_full_partial_endpoint_caps a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_selected_counts a d ha hd,
    eventually_far_inner_log_budget a b d β Budget ha hb hd hβ hBudget,
    eventually_resampling_radius_margin a d 2 20 β hd hβ,
    eventually_resampling_radius_margin a d 0 4 (c/4) hd (by positivity),
    eventually_log_ge_nat 1,Filter.eventually_ge_atTop 1] with N hdecay htt hcounts hbudget hradius hselector hlog hN
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let s:=g.admissibleState T labels samples
  let h:=g.labelledResampledGraph T labels samples selector
  let r:=effectiveModelRadius a d N β
  let S:=s.fullTwoTargetVertices selector r x y
  let K:Set (Tᶜ:Set (Fin N)):={v|v.val∈S}
  let Tm:Set S:={v|v.val∈T}
  let M:=h.deficient.restrict S
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let ρ:=physicalTransfer d z
  let t:=ρ^(r/8-1)
  let F:=Cf*(L^(2*a)*t+L^(2*a+1)*ε)
  intro hx hy
  change g.FullCommonQuarterFarInnerRestoredAt T labels samples selector r z q x y hx hy (1/L)
  unfold FullCommonQuarterFarInnerRestoredAt
  intro hfar
  unfold FullCommonInnerRestoredAt
  dsimp only
  let xS:S:=twoBallLeft g.graph (filledExteriorVertices T (s.endpointModelVertices selector r)) x y r
  let yS:S:=twoBallRight g.graph (filledExteriorVertices T (s.endpointModelVertices selector r)) x y r
  let xo:(Tmᶜ:Set S):=⟨xS,hx⟩
  let yo:(Tmᶜ:Set S):=⟨yS,hy⟩
  let xl:K:=⟨⟨x,hx⟩,xS.property⟩
  let yl:K:=⟨⟨y,hy⟩,yS.property⟩
  let upper:=(h.deficient.delete T).restrict K
  let φ:=restrictionDeletionGraphIso h.graph S T Tm (fun _=>Iff.rfl)
  have hTS:T⊆S:=fun _ ht=>Or.inl (Or.inl ht)
  have hg:=h.deficient.restriction_delete_extensionGreen S T Tm (fun _=>Iff.rfl) hTS q z
  have hr8:8≤r:=by dsimp only[r,effectiveModelRadius,modelRadiusLoss];omega
  have hs:1≤selector:=by dsimp only[selector];omega
  have hL0:0≤L:=by dsimp only[L];linarith
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hρ0:0≤ρ:=(physicalTransfer_pos d hd z).le
  have hρ1:ρ≤1:=by dsimp only[ρ];nlinarith [physicalTransfer_sq_le_half d hd z]
  have ht0:0≤t:=pow_nonneg hρ0 _
  have hF:0≤F:=mul_nonneg hCf (add_nonneg
    (mul_nonneg (pow_nonneg hL0 _) ht0) (mul_nonneg (pow_nonneg hL0 _) hε))
  have hS:S⊆s.fullTwoTargetVertices selector r x y:=Set.Subset.rfl
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
    have hUp:=hdecay g o z q hz hzB hfloor hq hprior hballs labels samples x y ul wl (r/8-1)
      ((ENat.coe_le_coe.mpr hrad).trans hdist)
    change ‖upper.extensionGreen q z ul wl‖≤Af*L*t+Df*L*ε at hUp
    have h2:L≤L^(2*a):=by simpa only[pow_one] using pow_le_pow_right₀ hlog (by omega:1≤2*a)
    have h3:L≤L^(2*a+1):=by simpa only[pow_one] using pow_le_pow_right₀ hlog (by omega:1≤2*a+1)
    have hleft:Af*L*t≤Cf*L^(2*a)*t:=mul_le_mul_of_nonneg_right
      (mul_le_mul hAf h2 hL0 hCf) ht0
    have hright:Df*L*ε≤Cf*L^(2*a+1)*ε:=mul_le_mul_of_nonneg_right
      (mul_le_mul hDf h3 hL0 hCf) hε
    have hup:‖upper.extensionGreen q z ul wl‖≤F:=
      (hUp.trans (add_le_add hleft hright)).trans_eq (by dsimp only[F];ring)
    have he:=congrArg (fun A:Matrix (Tmᶜ:Set S) (Tmᶜ:Set S) ℂ=>A u w) hg
    change upper.extensionGreen q z (φ u) (φ w)=(M.delete Tm).extensionGreen q z u w at he
    rw[←he]
    exact hup
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
  change upper.extensionGreen q z xl yl=(M.delete Tm).extensionGreen q z xo yo at he
  rw [←he] at hfinal
  exact hfinal

end RegularGraph
end LocalLaw
