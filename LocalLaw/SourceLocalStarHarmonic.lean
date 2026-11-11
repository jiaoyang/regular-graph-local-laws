import LocalLaw.SourceLocalPostOuterColumns
import LocalLaw.ModelStarLogHarmonicBounds
import LocalLaw.FiniteStarTargets

/-! # Source-realized global harmonic weights of the captured inner star -/

open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
namespace LocalLaw
local instance sourceLocalStarHarmonicDecidable (p:Prop):Decidable p:=Classical.propDecidable p
local instance (priority := 2000) sourceLocalStarHarmonicRangeDecidable {L W:Type} (a:L↪W) :
    DecidablePred (fun v:W=>v∈Set.range a) := fun _=>Classical.propDecidable _

def sourceLocalHarmonicRowConstant (d:ℕ)(β B C1:ℝ):ℝ:=
  1+(2*sourceLocalPostOuterColumnCap d β B C1)*(d:ℝ)

def sourceLocalHarmonicLeadingConstant (d:ℕ)(β B C1:ℝ):ℝ:=
  1+2*(d:ℝ)*(2*sourceLocalPostOuterColumnCap d β B C1+(|sourceLocalSelectedLeading d β B C1|+1))*
    ((B+1)*‖(treeEdgeWeight d)⁻¹‖)^2

def sourceLocalHarmonicErrorConstant (d:ℕ)(β B C1:ℝ):ℝ:=
  2*(d:ℝ)*(|sourceLocalPostOuterColumnError d β B C1|+1)

namespace RegularGraph

theorem eventually_source_local_star_harmonic (a b d:ℕ)(c β Bcap C1:ℝ)
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
      let S:=pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
      let O:=s.outerFirstSet selector r x y
      let I:=s.innerStarDeletedCore selector r x y
      let J:=s.innerFirstSet selector r x y
      let h:=s.innerStarLayout selector r hr x y
      let M:=(((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S).delete {v:S|v.val∈O}
      let aJ:=restrictedStarInner S O J h.inner_right h.inner_not_outer
      let eI:=restrictedStarCore S O I J h.core_right h.core_not_outer h.inner_right h.inner_not_outer h.core_not_inner
      let E:=embeddedStarEmbedding aJ eI
      let R:=((M.delete (Set.range aJ)).extensionGreen q z).submatrix eI eI
      let G:=(M.extensionGreen q z).submatrix E E
      let η:=fun u:({v:S|v.val∈O}ᶜ:Set S)=>u.val.val
      ∀t:I⊕J,
      (∑i:I,‖(G.submatrix id Sum.inl*R⁻¹) t i‖)≤
          sourceLocalHarmonicRowConstant d β Bcap C1*Real.log (N:ℝ) ∧
      ∀i:I,‖(G.submatrix id Sum.inl*R⁻¹) t i‖≤
          sourceLocalHarmonicLeadingConstant d β Bcap C1*Real.log (N:ℝ)*
            physicalTransfer d z^(cappedGraphDistance (outsideGraph (s.fullResample selector).graph T) r (η (E t)) (η (eI i).val))+
          sourceLocalHarmonicErrorConstant d β Bcap C1*Real.log (N:ℝ)^2*
            graphPaperError a d N (logarithmicRadius β d N) z := by
  let C:=sourceLocalPostOuterColumnCap d β Bcap C1
  let B:=2*C
  let K:=|sourceLocalSelectedLeading d β Bcap C1|+1
  let D:=|sourceLocalPostOuterColumnError d β Bcap C1|+1
  have hK:0≤K:=by dsimp only [K];positivity
  have hD:0≤D:=by dsimp only [D];positivity
  have hce:=finiteExtraReferenceConstant_ge_one d hd
  filter_upwards [eventually_source_local_post_outer_columns a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_radius_hierarchy a d c β hd hc hβ hβc,
    eventually_log_ge_nat 1,eventually_ge_atTop 1] with N hpost hradii hlog hN
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  intro hr
  let S:=pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
  let O:=s.outerFirstSet selector r x y
  let I:=s.innerStarDeletedCore selector r x y
  let J:=s.innerFirstSet selector r x y
  let layout:=s.innerStarLayout selector r hr x y
  let M0:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S
  let M:=M0.delete {v:S|v.val∈O}
  let aJ:=restrictedStarInner S O J layout.inner_right layout.inner_not_outer
  let eI:=restrictedStarCore S O I J layout.core_right layout.core_not_outer layout.inner_right layout.inner_not_outer layout.core_not_inner
  let E:=embeddedStarEmbedding aJ eI
  let η:=fun u:({v:S|v.val∈O}ᶜ:Set S)=>u.val.val
  let Γ:=outsideGraph (s.fullResample selector).graph T
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  have hBcap:0≤Bcap:=(norm_nonneg z).trans hzB
  have hC:0≤C:=by
    dsimp only [C,sourceLocalPostOuterColumnCap,sourceLocalSelectedWholeCap,sourceLocalSelectedCutCap,
      sourceLocalSelectedCoreCap,sourcePartialEndpointRowCap,sourcePartialFirstInverseCap,sourcePartialFirstOffDiagonalConstant]
    positivity
  have hB:0≤B:=by dsimp only [B];positivity
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hL0:0≤L:=by dsimp only [L];linarith
  have hpostM:=hpost g o z q hz hzB hfloor hq hprior hballs labels samples x y
  have hsep:2*(r-2)≤selector:=by
    have hh:2*logarithmicRadius β d N≤selector:=hradii.2.2.1
    exact (Nat.mul_le_mul_left 2 ((Nat.sub_le r 2).trans (Nat.sub_le _ _))).trans hh
  have hn:Nat.card J≤2:=s.innerFirstSet_card selector r hsep x y
  have hnR:(Fintype.card J:ℝ)≤2:=by exact_mod_cast (show Fintype.card J≤2 by simpa only [Nat.card_eq_fintype_card] using hn)
  have hng:∀v j,M.graph.Adj v.val (aJ j)→v∈Set.range eI:=by
    intro v j hadj
    have hj:v.val.val.val∉J:=by
      intro hj
      exact v.property ⟨⟨v.val.val.val,hj⟩,Subtype.ext (Subtype.ext rfl)⟩
    have hi:v.val.val.val∈I:=layout.neighbor_core j.val j.property v.val.val.val hadj.symm v.val.property hj
    exact ⟨⟨v.val.val.val,hi⟩,Subtype.ext (Subtype.ext (Subtype.ext rfl))⟩
  intro t
  have hselected (j:J):(aJ j).val∈s.partialFirstRemovedSet selector S:=j.property.1
  have hrow:(∑j:J,‖M.extensionGreen q z (E t) (aJ j)‖)≤B*L:=by
    have hp:(∑j:J,‖M.extensionGreen q z (E t) (aJ j)‖)≤(Fintype.card J:ℝ)*(C*L):=by
      exact (Finset.sum_le_sum (fun j _=>(hpostM (E t) (aJ j) (hselected j)).1)).trans_eq
        (by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];rfl)
    exact hp.trans ((mul_le_mul_of_nonneg_right hnR (mul_nonneg hC hL0)).trans_eq (by dsimp only[B];ring))
  have hfar:∀i j,M.extensionMatrix q z (aJ j) (eI i).val≠0→
      2≤cappedGraphDistance Γ r (η (E t)) (η (eI i).val)→
      ‖M.extensionGreen q z (E t) (aJ j)‖≤
        K*L*physicalTransfer d z^(cappedGraphDistance Γ r (η (E t)) (η (eI i).val)-2)+D*L*(L*ε):=by
    intro i j hactive hdi
    have ha:=M.actual_star_coupling_nonzero_adj aJ eI q z i j hactive
    have hadj:Γ.Adj (η (eI i).val) (η (aJ j)):=ha.symm
    have hf:=capped_neighbor_far Γ r (η (E t)) (η (eI i).val) (η (aJ j)) hadj hdi
    have hdist:((cappedGraphDistance Γ r (η (E t)) (η (eI i).val)-2+1:ℕ):ℕ∞)≤
        M0.graph.edist (E t).val (aJ j).val:=
      hf.trans (graphHom_edist_le (SimpleGraph.Embedding.induce (G:=Γ) S).toHom (E t).val (aJ j).val)
    have hh:=(hpostM (E t) (aJ j) (hselected j)).2 _ hdist
    have hKK:sourceLocalSelectedLeading d β Bcap C1≤K:=by dsimp only [K];linarith [le_abs_self (sourceLocalSelectedLeading d β Bcap C1)]
    have hDD:sourceLocalPostOuterColumnError d β Bcap C1≤D:=by dsimp only [D];linarith [le_abs_self (sourceLocalPostOuterColumnError d β Bcap C1)]
    exact hh.trans (add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKK hL0) (pow_nonneg (physicalTransfer_pos d hd z).le _))
      (by
        have he:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDD (sq_nonneg L)) hε
        simpa only[pow_two,mul_assoc] using he))
  have hh:=M.actual_star_harmonic_log_bounds hd aJ eI hng q z hz hq Bcap hzB η Γ r t B K D L (L*ε)
    hB hK hD hlog (mul_nonneg hL0 hε) hn hrow hfar
  refine ⟨hh.1,?_⟩
  intro i
  convert hh.2 i using 1
  dsimp only[sourceLocalHarmonicLeadingConstant,sourceLocalHarmonicErrorConstant,B,C,K,D,L,ε]
  ring

end RegularGraph
end LocalLaw
