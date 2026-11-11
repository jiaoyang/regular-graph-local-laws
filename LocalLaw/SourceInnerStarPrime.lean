import LocalLaw.SourceInnerStarCoreBounds
import LocalLaw.InnerStarModelReductionNative
import LocalLaw.SourceGlobalStarHarmonic
import LocalLaw.SourceLocalStarHarmonic
import LocalLaw.SymmetricCoreLift
import LocalLaw.FiniteStarPrimeBounds
import LocalLaw.AsymmetricStarSourceRate

/-! # The actual restored inner star has nominal prime error

Every coefficient, count, core error, inverse and radius input is supplied
by the proved source factories. Targets in the sampled block are included.
-/

open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
namespace LocalLaw
local instance sourceInnerStarPrimeDecidable (p:Prop):Decidable p:=Classical.propDecidable p
local instance (priority := 2000) sourceInnerStarPrimeRangeDecidable {L W:Type}(a:L↪W) :
    DecidablePred (fun v:W=>v∈Set.range a):=fun _=>Classical.propDecidable _

def sourceInnerStarHarmonicRow (d:ℕ)(β B C1:ℝ):ℝ:=
  |sourceGlobalHarmonicRowConstant d β B C1|+|sourceLocalHarmonicRowConstant d β B C1|+1

def sourceInnerStarHarmonicLeading (d:ℕ)(β B C1:ℝ):ℝ:=
  |sourceGlobalHarmonicLeadingConstant d β B C1|+|sourceLocalHarmonicLeadingConstant d β B C1|+1

def sourceInnerStarHarmonicError (d:ℕ)(β B C1:ℝ):ℝ:=
  |sourceGlobalHarmonicErrorConstant d β B C1|+|sourceLocalHarmonicErrorConstant d β B C1|+1

def sourceInnerStarPrimeConstant (d:ℕ)(β B C1:ℝ):ℝ:=
  let H:=sourceInnerStarHarmonicRow d β B C1
  let D:=sourceInnerStarHarmonicError d β B C1
  sourceInnerStarCoreMain d β B C1*H^2+1+
    2*sourceInnerStarCoreCap d B C1*D*(4*(d:ℝ)+2)*H

namespace RegularGraph

theorem eventually_source_inner_star_prime (a b d:ℕ)(c β Bcap C1:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hC1:1≤C1) :
    ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z q:ℂ),
      0<z.im→‖z‖≤Bcap→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→0≤q.im→
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z)→
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d)→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y:((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      ∀hr:1≤r,
      let S₀:=s.twoTargetEndpointVertices selector r x y
      let S₁:=pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
      let O:=s.outerFirstSet selector r x y
      let I:=s.innerStarDeletedCore selector r x y
      let J:=s.innerFirstSet selector r x y
      let h:=s.innerStarLayout selector r hr x y
      let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
      let M₀:=(new.restrict S₀).delete {v:S₀|v.val∈O}
      let M₁:=(new.restrict S₁).delete {v:S₁|v.val∈O}
      let aJ:=restrictedStarInner S₀ O J h.inner_left h.inner_not_outer
      let bJ:=restrictedStarInner S₁ O J h.inner_right h.inner_not_outer
      let eI:=restrictedStarCore S₀ O I J h.core_left h.core_not_outer h.inner_left h.inner_not_outer h.core_not_inner
      let fI:=restrictedStarCore S₁ O I J h.core_right h.core_not_outer h.inner_right h.inner_not_outer h.core_not_inner
      let E:=embeddedStarEmbedding aJ eI
      let F:=embeddedStarEmbedding bJ fI
      let cover:=s.innerStarDeletedCore_targets selector r x y
      let tx:=starTargetIndex I J x cover.1
      let ty:=starTargetIndex I J y cover.2
      ‖M₀.extensionGreen q z (E tx) (E ty)-M₁.extensionGreen q z (F tx) (F ty)‖≤
        sourceInnerStarPrimeConstant d β Bcap C1*g.sourcePrime a (logarithmicRadius β d N) z := by
  let H:=sourceInnerStarHarmonicRow d β Bcap C1
  let K:=sourceInnerStarHarmonicLeading d β Bcap C1
  let D:=sourceInnerStarHarmonicError d β Bcap C1
  let KM:=sourceInnerStarCoreMain d β Bcap C1
  let C:=sourceInnerStarCoreCap d Bcap C1
  let V:=sourceInnerStarCoreTail d β Bcap
  let Count:=sourceInnerStarLeafCount d
  let m:ℝ:=4*(d:ℝ)+2
  have hH:0≤H:=by dsimp only [H,sourceInnerStarHarmonicRow];positivity
  have hK:0≤K:=by dsimp only [K,sourceInnerStarHarmonicLeading];positivity
  have hD:0≤D:=by dsimp only [D,sourceInnerStarHarmonicError];positivity
  have hKM:0≤KM:=by dsimp only [KM,sourceInnerStarCoreMain];positivity
  have hC:0≤C:=by dsimp only [C,sourceInnerStarCoreCap];positivity
  have hV:0≤V:=by dsimp only [V,sourceInnerStarCoreTail];positivity
  have hCount:0≤Count:=by dsimp only [Count,sourceInnerStarLeafCount];positivity
  have hm:0 ≤ m:=by dsimp only [m];positivity
  filter_upwards [eventually_source_global_star_harmonic a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_local_star_harmonic a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_inner_star_core_bounds a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_asymmetric_star_source_rate a d β Count KM K D C H m V ha hd hCount hKM hK hD hC hH hm hV,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,
    eventually_source_radius_hierarchy a d c β hd hc hβ hβc,
    eventually_log_ge_nat 1,eventually_ge_atTop 1] with N hglobal hlocal hcore hrate hradius hhierarchy hlog hN
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  intro hr
  let S₀:=s.twoTargetEndpointVertices selector r x y
  let S₁:=pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
  let O:=s.outerFirstSet selector r x y
  let I:=s.innerStarDeletedCore selector r x y
  let J:=s.innerFirstSet selector r x y
  let layout:=s.innerStarLayout selector r hr x y
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
  let M₀:=(new.restrict S₀).delete {v:S₀|v.val∈O}
  let M₁:=(new.restrict S₁).delete {v:S₁|v.val∈O}
  let aJ:=restrictedStarInner S₀ O J layout.inner_left layout.inner_not_outer
  let bJ:=restrictedStarInner S₁ O J layout.inner_right layout.inner_not_outer
  let eI:=restrictedStarCore S₀ O I J layout.core_left layout.core_not_outer layout.inner_left layout.inner_not_outer layout.core_not_inner
  let fI:=restrictedStarCore S₁ O I J layout.core_right layout.core_not_outer layout.inner_right layout.inner_not_outer layout.core_not_inner
  let E:=embeddedStarEmbedding aJ eI
  let F:=embeddedStarEmbedding bJ fI
  let R:=((M₀.delete (Set.range aJ)).extensionGreen q z).submatrix eI eI
  let P:=((M₁.delete (Set.range bJ)).extensionGreen q z).submatrix fI fI
  let GM:=(M₀.extensionGreen q z).submatrix E E
  let GN:=(M₁.extensionGreen q z).submatrix F F
  let cover:=s.innerStarDeletedCore_targets selector r x y
  let tx:=starTargetIndex I J x cover.1
  let ty:=starTargetIndex I J y cover.2
  let Γ:=outsideGraph (s.fullResample selector).graph T
  let ri:=fun i:I=>remainingPairRadius Γ r x y i.val
  let di:=fun i:I=>cappedGraphDistance Γ r x i.val
  let dj:=fun i:I=>cappedGraphDistance Γ r y i.val
  let oldAug:=(g.deficient.delete T).restrict S₀
  let Baug:=s.partialFirstRemovedSet selector S₀
  let n:=Nat.card (s.OmittedOrdinaryLeaves selector S₁⊕s.OmittedExtraLeaves selector S₁)+Nat.card (DeletedLeafIndex oldAug.graph Baug)
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let ρ:=physicalTransfer d z
  have hL0:0≤L:=by dsimp only [L];linarith
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hρ:0≤ρ:=(physicalTransfer_pos d hd z).le
  have hρone:ρ≤1:=by dsimp only [ρ];nlinarith [physicalTransfer_sq_le_half d hd z]
  have hsep:2*(r-2)≤selector:=
    (Nat.mul_le_mul_left 2 ((Nat.sub_le r 2).trans (Nat.sub_le _ _))).trans hhierarchy.2.2.1
  have hreduce:=s.inner_star_model_reduction_native new hd selector r rfl hr hsep x y q z hz hq
  have hcard:(Fintype.card I:ℝ)≤ m:=by
    have hh:Nat.card (I⊕J)≤4*d+2:=hreduce.1
    rw [Nat.card_sum] at hh
    have hi:Nat.card I≤4*d+2:=(Nat.le_add_right _ _).trans hh
    have hi':Fintype.card I≤4*d+2:=by simpa only [Nat.card_eq_fintype_card] using hi
    dsimp only [m]
    exact_mod_cast hi'
  have hG:=hglobal g o z q hz hzB hfloor hq hprior hballs labels samples x y hr tx
  have hP:=hlocal g o z q hz hzB hfloor hq hprior hballs labels samples x y hr ty
  have hcoreN:=hcore g o z q hz hzB hfloor hq hprior hballs labels samples x y hr
  have hE:(E tx).val.val=x:=restrictedStarTarget_value S₀ O I J layout.core_left layout.core_not_outer
    layout.inner_left layout.inner_not_outer layout.core_not_inner x cover.1
  have hF:(F ty).val.val=y:=restrictedStarTarget_value S₁ O I J layout.core_right layout.core_not_outer
    layout.inner_right layout.inner_not_outer layout.core_not_inner y cover.2
  have hGN:GN.IsSymm:=(M₁.extensionGreen_isSymm q z).submatrix F
  have hPsymm:P.IsSymm:=((M₁.delete (Set.range bJ)).extensionGreen_isSymm q z).submatrix fI
  have hRight (i:I):(P⁻¹*GN.submatrix Sum.inl id) i ty=(GN.submatrix id Sum.inl*P⁻¹) ty i:=
    symmetric_core_lift_entry GN P hGN hPsymm i ty
  have hHg:sourceGlobalHarmonicRowConstant d β Bcap C1≤H:=by
    dsimp only [H,sourceInnerStarHarmonicRow];linarith [le_abs_self (sourceGlobalHarmonicRowConstant d β Bcap C1),abs_nonneg (sourceLocalHarmonicRowConstant d β Bcap C1)]
  have hHl:sourceLocalHarmonicRowConstant d β Bcap C1≤H:=by
    dsimp only [H,sourceInnerStarHarmonicRow];linarith [le_abs_self (sourceLocalHarmonicRowConstant d β Bcap C1),abs_nonneg (sourceGlobalHarmonicRowConstant d β Bcap C1)]
  have hKg:sourceGlobalHarmonicLeadingConstant d β Bcap C1≤K:=by
    dsimp only [K,sourceInnerStarHarmonicLeading];linarith [le_abs_self (sourceGlobalHarmonicLeadingConstant d β Bcap C1),abs_nonneg (sourceLocalHarmonicLeadingConstant d β Bcap C1)]
  have hKl:sourceLocalHarmonicLeadingConstant d β Bcap C1≤K:=by
    dsimp only [K,sourceInnerStarHarmonicLeading];linarith [le_abs_self (sourceLocalHarmonicLeadingConstant d β Bcap C1),abs_nonneg (sourceGlobalHarmonicLeadingConstant d β Bcap C1)]
  have hDg:sourceGlobalHarmonicErrorConstant d β Bcap C1≤D:=by
    dsimp only [D,sourceInnerStarHarmonicError];linarith [le_abs_self (sourceGlobalHarmonicErrorConstant d β Bcap C1),abs_nonneg (sourceLocalHarmonicErrorConstant d β Bcap C1)]
  have hDl:sourceLocalHarmonicErrorConstant d β Bcap C1≤D:=by
    dsimp only [D,sourceInnerStarHarmonicError];linarith [le_abs_self (sourceLocalHarmonicErrorConstant d β Bcap C1),abs_nonneg (sourceGlobalHarmonicErrorConstant d β Bcap C1)]
  have hleft:(∑i:I,‖(GM.submatrix id Sum.inl*R⁻¹) tx i‖)≤H*L:=
    hG.1.trans (mul_le_mul_of_nonneg_right hHg hL0)
  have hright:(∑i:I,‖(P⁻¹*GN.submatrix Sum.inl id) i ty‖)≤H*L:=by
    simp_rw [hRight]
    exact hP.1.trans (mul_le_mul_of_nonneg_right hHl hL0)
  have haPoint:∀i:I,‖(GM.submatrix id Sum.inl*R⁻¹) tx i‖≤(K*L)*ρ^(di i)+D*L^2*ε:=by
    intro i
    have hh:=hG.2 i
    change ‖(GM.submatrix id Sum.inl*R⁻¹) tx i‖≤
      sourceGlobalHarmonicLeadingConstant d β Bcap C1*L*ρ^(cappedGraphDistance Γ r (E tx).val.val i.val)+
      sourceGlobalHarmonicErrorConstant d β Bcap C1*L*ε at hh
    rw [hE] at hh
    have hLpow:L≤L^2:=by simpa only [pow_one] using pow_le_pow_right₀ hlog (by omega:1≤2)
    exact hh.trans (add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKg hL0) (pow_nonneg hρ _))
      ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDg hL0) hε).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLpow hD) hε)))
  have hbPoint:∀i:I,‖(P⁻¹*GN.submatrix Sum.inl id) i ty‖≤(K*L)*ρ^(dj i)+D*L^2*ε:=by
    intro i
    rw [hRight]
    have hh:=hP.2 i
    change ‖(GN.submatrix id Sum.inl*P⁻¹) ty i‖≤
      sourceLocalHarmonicLeadingConstant d β Bcap C1*L*ρ^(cappedGraphDistance Γ r (F ty).val.val i.val)+
      sourceLocalHarmonicErrorConstant d β Bcap C1*L^2*ε at hh
    rw [hF] at hh
    exact hh.trans (add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKl hL0) (pow_nonneg hρ _))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDl (sq_nonneg L)) hε))
  have hrateN:=hrate z hz.le hradius.1 (n:ℝ) (Nat.cast_nonneg _) hcoreN.1
  exact finite_star_prime_bound GM GN R P hreduce.2.2.2 tx ty ρ KM K D C H V n m L ε
    (sourceInnerStarPrimeConstant d β Bcap C1) hρ hρone hKM hK hD hC hH hV
    (Nat.cast_nonneg _) hm hlog hε hcard r ri di dj
    (fun i=>(remainingPairRadius_recovery Γ r x y i.val).1)
    (fun i=>(remainingPairRadius_recovery Γ r x y i.val).2)
    haPoint hbPoint hcoreN.2.1 hcoreN.2.2 hleft hright hrateN

end RegularGraph
end LocalLaw
