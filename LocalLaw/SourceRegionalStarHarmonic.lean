import LocalLaw.SourceRegionalPostColumns
import LocalLaw.ModelStarHarmonicBounds

/-! # Fixed-L1 source harmonic weights for any captured regional sampled star -/

open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance sourceRegionalHarmonicDecidable (p:Prop):Decidable p:=Classical.propDecidable p
local instance (priority := 2000) sourceRegionalHarmonicRangeDecidable {L W:Type}(a:L↪W) :
    DecidablePred (fun v:W=>v∈Set.range a):=fun _=>Classical.propDecidable _

def sourceRegionalHarmonicRow (d:ℕ)(β B C1:ℝ):ℝ:=1+2*sourceRegionalPostColumnCap d β B C1*(d:ℝ)

def sourceRegionalHarmonicLeading (d:ℕ)(β B C1:ℝ):ℝ:=
  1+2*(d:ℝ)*(2*sourceRegionalPostColumnCap d β B C1+(|sourceRegionalSelectedLeading d β B C1|+1))*
    ((B+1)*‖(treeEdgeWeight d)⁻¹‖)^2

def sourceRegionalHarmonicError (d:ℕ)(β B C1:ℝ):ℝ:=2*(d:ℝ)*(|sourceRegionalPostColumnError d β B C1|+1)

namespace RegularGraph

theorem eventually_source_regional_star_harmonic (a b d:ℕ)(c β Bcap C1:ℝ)
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
      ∀S:Set (Tᶜ:Set (Fin N)),S⊆s.twoTargetEndpointVertices selector r x y→
      ((s.selectedFirstSet selector⊆S ∧ ∀i:s.AdmissibleSampleIndex selector,s.admissibleBoundaryVertex selector i∈S) ∨
        Nat.card (s.partialFirstRemovedSet selector S)≤2)→
      ∀O:Set (Tᶜ:Set (Fin N)),O⊆s.selectedFirstSet selector→
      let M0:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S
      let M:=M0.delete {v:S|v.val∈O}
      ∀{I J:Type}[Fintype I][Fintype J][DecidableEq I][DecidableEq J]
      (aJ:J↪({v:S|v.val∈O}ᶜ:Set S))(eI:I↪((Set.range aJ)ᶜ:Set ({v:S|v.val∈O}ᶜ:Set S))),
      (∀j,(aJ j).val∈s.partialFirstRemovedSet selector S)→
      (∀v j,M.graph.Adj v.val (aJ j)→v∈Set.range eI)→Nat.card J≤2→
      let R:=((M.delete (Set.range aJ)).extensionGreen q z).submatrix eI eI
      let E:=embeddedStarEmbedding aJ eI
      let G:=(M.extensionGreen q z).submatrix E E
      let η:=fun u:({v:S|v.val∈O}ᶜ:Set S)=>u.val.val.val
      ∀t:I⊕J,(∑i:I,‖(G.submatrix id Sum.inl*R⁻¹) t i‖)≤sourceRegionalHarmonicRow d β Bcap C1 ∧
        ∀i:I,‖(G.submatrix id Sum.inl*R⁻¹) t i‖≤
          sourceRegionalHarmonicLeading d β Bcap C1*Real.log (N:ℝ)*
            physicalTransfer d z^(cappedGraphDistance (s.fullResample selector).graph r (η (E t)) (η (eI i).val))+
          sourceRegionalHarmonicError d β Bcap C1*Real.log (N:ℝ)*graphPaperError a d N (logarithmicRadius β d N) z := by
  let C:=sourceRegionalPostColumnCap d β Bcap C1
  let B:=2*C
  let K:=|sourceRegionalSelectedLeading d β Bcap C1|+1
  let D:=|sourceRegionalPostColumnError d β Bcap C1|+1
  have hK:0≤K:=by dsimp only[K];positivity
  have hD:0≤D:=by dsimp only[D];positivity
  have hCe:=finiteExtraReferenceConstant_ge_one d hd
  filter_upwards [eventually_source_regional_post_columns a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_log_ge_nat 1,eventually_ge_atTop 1] with N hpost hlog hN
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  intro S hS hregion O hO
  let M0:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S
  let M:=M0.delete {v:S|v.val∈O}
  intro I J _ _ _ _ aJ eI hselected hng hn
  let E:=embeddedStarEmbedding aJ eI
  let η:=fun u:({v:S|v.val∈O}ᶜ:Set S)=>u.val.val.val
  let Γ:=(s.fullResample selector).graph
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  have hC:0≤C:=by
    dsimp only[C,sourceRegionalPostColumnCap,sourceRegionalSelectedWholeCap,sourceRegionalSelectedCutCap,
      sourcePartialEndpointRowCap,sourcePartialFirstInverseCap,sourcePartialFirstOffDiagonalConstant]
    positivity
  have hB:0≤B:=by dsimp only[B];positivity
  have hL:0≤L:=by dsimp only[L];linarith
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hW:{v:S|v.val∈O}⊆s.partialFirstRemovedSet selector S:=fun _ h=>hO h
  have hp:=hpost g o z q hz hzB hfloor hq hprior hballs labels samples x y S hS hregion _ hW
  have hnR:(Fintype.card J:ℝ)≤2:=by exact_mod_cast (show Fintype.card J≤2 by simpa only[Nat.card_eq_fintype_card] using hn)
  intro t
  have hrow:(∑j:J,‖M.extensionGreen q z (E t) (aJ j)‖)≤B:=by
    have hh: (∑j:J,‖M.extensionGreen q z (E t) (aJ j)‖)≤(Fintype.card J:ℝ)*C:=by
      exact (Finset.sum_le_sum (fun j _=>(hp (E t) (aJ j) (hselected j)).1)).trans_eq
        (by simp only[Finset.sum_const,Finset.card_univ,nsmul_eq_mul];rfl)
    exact hh.trans (mul_le_mul_of_nonneg_right hnR hC)
  have hfar:∀i j,M.extensionMatrix q z (aJ j) (eI i).val≠0→
      2≤cappedGraphDistance Γ r (η (E t)) (η (eI i).val)→
      ‖M.extensionGreen q z (E t) (aJ j)‖≤
        K*L*physicalTransfer d z^(cappedGraphDistance Γ r (η (E t)) (η (eI i).val)-2)+D*L*ε:=by
    intro i j hactive hdi
    have ha:=M.actual_star_coupling_nonzero_adj aJ eI q z i j hactive
    have hadj:Γ.Adj (η (eI i).val) (η (aJ j)):=ha.symm
    have hf:=capped_neighbor_far Γ r (η (E t)) (η (eI i).val) (η (aJ j)) hadj hdi
    have hdist:((cappedGraphDistance Γ r (η (E t)) (η (eI i).val)-2+1:ℕ):ℕ∞)≤
        M0.graph.edist (E t).val (aJ j).val:=
      hf.trans ((ambient_edist_le_induced_edist Γ Tᶜ (E t).val.val (aJ j).val.val).trans
        (graphHom_edist_le (SimpleGraph.Embedding.induce (G:=outsideGraph Γ T) S).toHom (E t).val (aJ j).val))
    have hh:=(hp (E t) (aJ j) (hselected j)).2 _ hdist
    have hKK:sourceRegionalSelectedLeading d β Bcap C1≤K:=by dsimp only[K];linarith [le_abs_self (sourceRegionalSelectedLeading d β Bcap C1)]
    have hDD:sourceRegionalPostColumnError d β Bcap C1≤D:=by dsimp only[D];linarith [le_abs_self (sourceRegionalPostColumnError d β Bcap C1)]
    exact hh.trans (add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKK hL) (pow_nonneg (physicalTransfer_pos d hd z).le _))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDD hL) hε))
  exact M.actual_star_harmonic_bounds hd aJ eI hng q z hz hq Bcap hzB η Γ r t B K D L ε
    hB hK hD hlog hε hn hrow hfar

end RegularGraph
end LocalLaw
