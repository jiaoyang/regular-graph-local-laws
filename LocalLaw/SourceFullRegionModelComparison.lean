import LocalLaw.SourceFullStarCoreBounds
import LocalLaw.SourceRegionalStarHarmonic
import LocalLaw.FullRegionSupport
import LocalLaw.ShiftedRemainingRadius
import LocalLaw.SymmetricCoreLift
import LocalLaw.FiniteStarStructuredBound

/-! # Structured comparison after the far sampled vertices are deleted

Actual finite-star restoration retains the fixed harmonic L1 rows.
Only the spatial term pays the boundary count and logarithmic powers.
-/
open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 3500000
namespace LocalLaw
local instance sourceFullRegionModelDecidable (p:Prop):Decidable p:=Classical.propDecidable p
local instance (priority := 2000) sourceFullRegionModelRangeDecidable {L W:Type}(a:L↪W):
    DecidablePred (fun v:W=>v∈Set.range a):=fun _=>Classical.propDecidable _

def sourceFullRegionHarmonicRow (d:ℕ)(β B C1:ℝ):ℝ:=|sourceRegionalHarmonicRow d β B C1|+1
def sourceFullRegionHarmonicLeading (d:ℕ)(β B C1:ℝ):ℝ:=|sourceRegionalHarmonicLeading d β B C1|+1
def sourceFullRegionHarmonicError (d:ℕ)(β B C1:ℝ):ℝ:=|sourceRegionalHarmonicError d β B C1|+1

def sourceFullRegionModelMain (d:ℕ)(β B C1:ℝ):ℝ:=
  sourceFullRegionCoreMain d β B C1*(sourceFullRegionHarmonicRow d β B C1)^2+
    2*sourceFullRegionCoreCap d B C1*sourceFullRegionHarmonicError d β B C1*
      (4*(d:ℝ)+2)*sourceFullRegionHarmonicRow d β B C1

def sourceFullRegionModelTail (d:ℕ)(β B C1:ℝ):ℝ:=
  (4*(d:ℝ)+2)^2*(sourceFullRegionHarmonicLeading d β B C1)^2*sourceFullRegionCoreTail d β B

namespace RegularGraph

theorem eventually_source_full_region_model_comparison (a b d:ℕ)(c β Bcap C1:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hC1:1≤C1):
    ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z q:ℂ),
      0<z.im→‖z‖≤Bcap→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→0≤q.im→
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z)→
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d)→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y:Fin N),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      let S0:=s.fullSliceOutside (s.fullTwoTargetVertices selector r x y)
      let S1:=s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r)
      ∀hr:1≤r,∀(u v:(Tᶜ:Set (Fin N)))(hu:u∈S1)(hv:v∈S1)
        (hOu:u∉s.fullRegionOuterFirst selector r x y)(hOv:v∉s.fullRegionOuterFirst selector r x y)
        (loss:ℕ),
      (s.fullResample selector).graph.edist x u.val≤(loss:ℕ∞) ∨
        (s.fullResample selector).graph.edist y u.val≤(loss:ℕ∞)→
      (s.fullResample selector).graph.edist x v.val≤(loss:ℕ∞) ∨
        (s.fullResample selector).graph.edist y v.val≤(loss:ℕ∞)→
      let O:=s.fullRegionOuterFirst selector r x y
      let I:=s.fullRegionStarCore selector r x y u v
      let J:=s.fullRegionInnerFirst selector r x y
      let h:=s.fullRegionStarLayout selector r hr x y u v hu hv
      let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
      let M0:=(new.restrict S0).delete {v:S0|v.val∈O}
      let M1:=(new.restrict S1).delete {v:S1|v.val∈O}
      let aJ:=restrictedStarInner S0 O J h.inner_left h.inner_not_outer
      let bJ:=restrictedStarInner S1 O J h.inner_right h.inner_not_outer
      let eI:=restrictedStarCore S0 O I J h.core_left h.core_not_outer h.inner_left h.inner_not_outer h.core_not_inner
      let fI:=restrictedStarCore S1 O I J h.core_right h.core_not_outer h.inner_right h.inner_not_outer h.core_not_inner
      let E:=embeddedStarEmbedding aJ eI
      let F:=embeddedStarEmbedding bJ fI
      let cover:=s.fullRegionStarCore_targets selector r x y u v hOu hOv
      let tx:=starTargetIndex I J u cover.1
      let ty:=starTargetIndex I J v cover.2
      let μ:=Nat.card (BoundaryOrientedEdge g.graph T)
      let L:=Real.log (N:ℝ)
      let ε:=graphPaperError a d N (logarithmicRadius β d N) z
      ‖M0.extensionGreen q z (E tx) (E ty)-M1.extensionGreen q z (F tx) (F ty)‖≤
        sourceFullRegionModelMain d β Bcap C1*L*ε+
          sourceFullRegionModelTail d β Bcap C1*((μ:ℝ)+1)*L^4*physicalTransfer d z^(2*(r-loss)):=by
  let H:=sourceFullRegionHarmonicRow d β Bcap C1
  let K:=sourceFullRegionHarmonicLeading d β Bcap C1
  let D:=sourceFullRegionHarmonicError d β Bcap C1
  let KM:=sourceFullRegionCoreMain d β Bcap C1
  let C:=sourceFullRegionCoreCap d Bcap C1
  let V:=sourceFullRegionCoreTail d β Bcap
  let m:ℝ:=4*(d:ℝ)+2
  have hH:0≤H:=by dsimp only[H,sourceFullRegionHarmonicRow];positivity
  have hK:0≤K:=by dsimp only[K,sourceFullRegionHarmonicLeading];positivity
  have hD:0≤D:=by dsimp only[D,sourceFullRegionHarmonicError];positivity
  have hKM:0≤KM:=by dsimp only[KM,sourceFullRegionCoreMain];positivity
  have hC:0≤C:=by dsimp only[C,sourceFullRegionCoreCap];positivity
  have hV:0≤V:=by dsimp only[V,sourceFullRegionCoreTail];positivity
  have hm:0≤ m:=by dsimp only[m];positivity
  have hHs:sourceRegionalHarmonicRow d β Bcap C1≤H:=
    (le_abs_self _).trans (le_add_of_nonneg_right (by norm_num))
  have hKs:sourceRegionalHarmonicLeading d β Bcap C1≤K:=
    (le_abs_self _).trans (le_add_of_nonneg_right (by norm_num))
  have hDs:sourceRegionalHarmonicError d β Bcap C1≤D:=
    (le_abs_self _).trans (le_add_of_nonneg_right (by norm_num))
  filter_upwards [eventually_source_full_star_core_bounds a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_regional_star_harmonic a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_inner_complement_nonempty a d (by omega) hd,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    eventually_log_ge_nat 1,eventually_ge_atTop 1] with N hcore hharm hdummy hmargin hlog hN
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let S0:=s.fullSliceOutside (s.fullTwoTargetVertices selector r x y)
  let S1:=s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r)
  intro hr u v hu hv hOu hOv loss hnearU hnearV
  let O:=s.fullRegionOuterFirst selector r x y
  let I:=s.fullRegionStarCore selector r x y u v
  let J:=s.fullRegionInnerFirst selector r x y
  let layout:=s.fullRegionStarLayout selector r hr x y u v hu hv
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
  let M0:=(new.restrict S0).delete {v:S0|v.val∈O}
  let M1:=(new.restrict S1).delete {v:S1|v.val∈O}
  let aJ:=restrictedStarInner S0 O J layout.inner_left layout.inner_not_outer
  let bJ:=restrictedStarInner S1 O J layout.inner_right layout.inner_not_outer
  let eI:=restrictedStarCore S0 O I J layout.core_left layout.core_not_outer layout.inner_left layout.inner_not_outer layout.core_not_inner
  let fI:=restrictedStarCore S1 O I J layout.core_right layout.core_not_outer layout.inner_right layout.inner_not_outer layout.core_not_inner
  let E:=embeddedStarEmbedding aJ eI
  let F:=embeddedStarEmbedding bJ fI
  let R:=((M0.delete (Set.range aJ)).extensionGreen q z).submatrix eI eI
  let P:=((M1.delete (Set.range bJ)).extensionGreen q z).submatrix fI fI
  let GM:=(M0.extensionGreen q z).submatrix E E
  let GN:=(M1.extensionGreen q z).submatrix F F
  let cover:=s.fullRegionStarCore_targets selector r x y u v hOu hOv
  let tx:=starTargetIndex I J u cover.1
  let ty:=starTargetIndex I J v cover.2
  let Γ:=(s.fullResample selector).graph
  let ri:=fun i:I=>remainingPairRadius Γ r x y i.val.val
  let di:=fun i:I=>cappedGraphDistance Γ r u.val i.val.val
  let dj:=fun i:I=>cappedGraphDistance Γ r v.val i.val.val
  let μ:=Nat.card (BoundaryOrientedEdge g.graph T)
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let ρ:=physicalTransfer d z
  let w:(Tᶜ:Set (Fin N)):=Classical.choice (hdummy g o z)
  let px:=s.outsideReplacement w x
  let py:=s.outsideReplacement w y
  have hS0:S0⊆s.twoTargetEndpointVertices selector r px py:=s.fullTwoTarget_outside_subset_replacements selector r w x y
  have hS1:S1⊆s.twoTargetEndpointVertices selector r px py:=s.switched_full_pair_outside_subset_replacements selector r w x y
  have hsep:2*r≤selector:=by dsimp only[r,selector];omega
  have hsep':2*(r-2)≤selector:=(Nat.mul_le_mul_left 2 (Nat.sub_le r 2)).trans hsep
  have hreduce:=s.full_region_star_model_reduction new hd selector r rfl hr hsep' x y u v hu hv q z hz hq
  have hcard:(Fintype.card I:ℝ)≤ m:=by
    have hn:Nat.card (I⊕J)≤4*d+2:=hreduce.1
    rw[Nat.card_sum] at hn
    have hi:Nat.card I≤4*d+2:=by omega
    simpa only[Nat.card_eq_fintype_card,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,m] using (Nat.cast_le (α:=ℝ).mpr hi)
  have hJ:Nat.card J≤2:=s.fullRegionInnerFirst_card selector r x y hsep'
  have hregion0:(s.selectedFirstSet selector⊆S0 ∧ ∀i:s.AdmissibleSampleIndex selector,s.admissibleBoundaryVertex selector i∈S0) ∨
      Nat.card (s.partialFirstRemovedSet selector S0)≤2:=Or.inl
        ⟨s.selectedFirstSet_subset_fullRegion selector r x y,s.admissibleBoundaryVertex_mem_fullRegion selector r x y⟩
  have hregion1:(s.selectedFirstSet selector⊆S1 ∧ ∀i:s.AdmissibleSampleIndex selector,s.admissibleBoundaryVertex selector i∈S1) ∨
      Nat.card (s.partialFirstRemovedSet selector S1)≤2:=Or.inr (s.partialFirstRemovedSet_new_full_pair_card selector r hsep x y)
  have hO:O⊆s.selectedFirstSet selector:=fun _ ho=>ho.1
  have hng0:∀v j,M0.graph.Adj v.val (aJ j)→v∈Set.range eI:=by
    intro v j hadj
    have hj:v.val.val.val∉J:=by
      intro hj
      exact v.property ⟨⟨v.val.val.val,hj⟩,Subtype.ext (Subtype.ext rfl)⟩
    have hi:v.val.val.val∈I:=layout.neighbor_core j.val j.property v.val.val.val hadj.symm v.val.property hj
    exact ⟨⟨v.val.val.val,hi⟩,Subtype.ext (Subtype.ext (Subtype.ext rfl))⟩
  have hng1:∀v j,M1.graph.Adj v.val (bJ j)→v∈Set.range fI:=by
    intro v j hadj
    have hj:v.val.val.val∉J:=by
      intro hj
      exact v.property ⟨⟨v.val.val.val,hj⟩,Subtype.ext (Subtype.ext rfl)⟩
    have hi:v.val.val.val∈I:=layout.neighbor_core j.val j.property v.val.val.val hadj.symm v.val.property hj
    exact ⟨⟨v.val.val.val,hi⟩,Subtype.ext (Subtype.ext (Subtype.ext rfl))⟩
  have hG:=hharm g o z q hz hzB hfloor hq hprior hballs labels samples px py S0 hS0 hregion0 O hO
    aJ eI (fun j=>j.property.1) hng0 hJ tx
  have hQ:=hharm g o z q hz hzB hfloor hq hprior hballs labels samples px py S1 hS1 hregion1 O hO
    bJ fI (fun j=>j.property.1) hng1 hJ ty
  have hcoreN:=(hcore g o z q hz hzB hfloor hq hprior hballs labels samples x y u v hu hv).2 hr
  have hE:(E tx).val.val.val=u.val:=congrArg Subtype.val (restrictedStarTarget_value S0 O I J layout.core_left layout.core_not_outer
    layout.inner_left layout.inner_not_outer layout.core_not_inner u cover.1)
  have hF:(F ty).val.val.val=v.val:=congrArg Subtype.val (restrictedStarTarget_value S1 O I J layout.core_right layout.core_not_outer
    layout.inner_right layout.inner_not_outer layout.core_not_inner v cover.2)
  have hRight (i:I):(P⁻¹*GN.submatrix Sum.inl id) i ty=(GN.submatrix id Sum.inl*P⁻¹) ty i:=
    symmetric_core_lift_entry GN P ((M1.extensionGreen_isSymm q z).submatrix F)
      (((M1.delete (Set.range bJ)).extensionGreen_isSymm q z).submatrix fI) i ty
  have hL:0≤L:=by dsimp only[L];linarith
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hρ:0≤ρ:=(physicalTransfer_pos d hd z).le
  have hρone:ρ≤1:=by dsimp only[ρ];nlinarith[physicalTransfer_sq_le_half d hd z]
  have hleft:(∑i:I,‖(GM.submatrix id Sum.inl*R⁻¹) tx i‖)≤H:=hG.1.trans hHs
  have hright:(∑i:I,‖(P⁻¹*GN.submatrix Sum.inl id) i ty‖)≤H:=by
    simp_rw[hRight]
    exact hQ.1.trans hHs
  have haPoint:∀i:I,‖(GM.submatrix id Sum.inl*R⁻¹) tx i‖≤(K*L)*ρ^(di i)+D*L*ε:=by
    intro i
    have hh:=hG.2 i
    change ‖(GM.submatrix id Sum.inl*R⁻¹) tx i‖≤sourceRegionalHarmonicLeading d β Bcap C1*L*
      ρ^(cappedGraphDistance Γ r (E tx).val.val.val i.val.val)+sourceRegionalHarmonicError d β Bcap C1*L*ε at hh
    rw[hE] at hh
    exact hh.trans (add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKs hL) (pow_nonneg hρ _))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDs hL) hε))
  have hbPoint:∀i:I,‖(P⁻¹*GN.submatrix Sum.inl id) i ty‖≤(K*L)*ρ^(dj i)+D*L*ε:=by
    intro i
    rw[hRight]
    have hh:=hQ.2 i
    change ‖(GN.submatrix id Sum.inl*P⁻¹) ty i‖≤sourceRegionalHarmonicLeading d β Bcap C1*L*
      ρ^(cappedGraphDistance Γ r (F ty).val.val.val i.val.val)+sourceRegionalHarmonicError d β Bcap C1*L*ε at hh
    rw[hF] at hh
    exact hh.trans (add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKs hL) (pow_nonneg hρ _))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDs hL) hε))
  have hmain:∀i j:I,‖(R-P) i j‖≤KM*L*ε+(V*((μ:ℝ)+1)*L^2)*ρ^(ri i+ri j):=by
    intro i j
    exact (hcoreN.2.1 i j).trans_eq (by ring)
  exact finite_star_structured_bound GM GN R P hreduce.2.2.2 tx ty ρ KM K D C H V μ m L ε
    hρ hρone hKM hK hD hC hH hV (Nat.cast_nonneg _) hm hL hε hcard (r-loss) ri di dj
    (fun i=>remainingPairRadius_shifted_recovery Γ r loss x y u.val i.val.val hnearU)
    (fun i=>remainingPairRadius_shifted_recovery Γ r loss x y v.val i.val.val hnearV)
    haPoint hbPoint hmain hcoreN.2.2 hleft hright

end RegularGraph
end LocalLaw
