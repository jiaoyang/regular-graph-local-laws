import LocalLaw.SourceOuterFirstDeletion
import LocalLaw.SourceSelectedWholeRows
import LocalLaw.SubsetNormRows

/-! # Sampled columns after the actual far sampled vertices are deleted

The correction pays the true whole sampled-row mass. Its residual has no
sample-count factor. All inverse, scalar and graph inputs are source-derived.
-/

open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000
namespace LocalLaw
local instance sourcePostOuterColumnsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourcePostOuterColumnCap (d:ℕ)(β B C1:ℝ):ℝ:=
  let K:=sourceSelectedWholeRowCap d B
  K+K*(4*sourcePartialFirstInverseCap d B)*sourcePartialFirstOffDiagonalConstant d β B C1

def sourcePostOuterColumnError (d:ℕ)(β B C1:ℝ):ℝ:=
  sourceSelectedFarError d β B C1+
    sourceSelectedWholeRowCap d B*(4*sourcePartialFirstInverseCap d B)*sourcePartialFirstOffDiagonalConstant d β B C1

namespace RegularGraph

theorem eventually_source_post_outer_columns (a b d:ℕ)(c β Bcap C1:ℝ)
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
      let A:=s.twoTargetEndpointVertices selector r x y
      let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict A
      let W:=s.outerFirstRegion selector r x y A
      ∀u v:(Wᶜ:Set A),v.val∈s.partialFirstRemovedSet selector A→
        ‖(M.delete W).extensionGreen q z u v‖≤sourcePostOuterColumnCap d β Bcap C1 ∧
        ∀h:ℕ,((h+1:ℕ):ℕ∞)≤M.graph.edist u.val v.val→
          ‖(M.delete W).extensionGreen q z u v‖≤
            sourceSelectedFarLeading d β Bcap C1*Real.log (N:ℝ)*physicalTransfer d z^h+
              sourcePostOuterColumnError d β Bcap C1*Real.log (N:ℝ)*
                graphPaperError a d N (logarithmicRadius β d N) z := by
  let K:=sourceSelectedWholeRowCap d Bcap
  let C:=4*sourcePartialFirstInverseCap d Bcap
  let D:=sourcePartialFirstOffDiagonalConstant d β Bcap C1
  have hce:=finiteExtraReferenceConstant_ge_one d hd
  have hC:0≤C:=by dsimp only [C,sourcePartialFirstInverseCap];positivity
  have hD:0≤D:=by dsimp only [D,sourcePartialFirstOffDiagonalConstant];positivity
  filter_upwards [eventually_source_selected_far_columns a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_selected_whole_rows a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_partial_first_principal_caps a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_partial_first_offdiagonal a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_paperError_small a b d β ha hb hd hβ,
    eventually_log_ge_nat 1,eventually_ge_atTop 1] with N hfar hwhole hinv hoff hpaper hlog hN
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let A:=s.twoTargetEndpointVertices selector r x y
  let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict A
  let W:=s.outerFirstRegion selector r x y A
  let BB:=s.partialFirstRemovedSet selector A
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let δ:=D*L*ε
  have hBcap:0≤Bcap:=(norm_nonneg z).trans hzB
  have hK:0≤K:=by
    dsimp only [K,sourceSelectedWholeRowCap,sourcePartialEndpointRowCap,sourceSelectedCutRowCap,
      leafDeletedMateRowCap,leafDeletedSeparatedRowCap]
    positivity
  have hLp:0<L:=by dsimp only [L];linarith
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hδ:0≤δ:=by dsimp only [δ];positivity
  have hεL:L*ε≤1:=by
    have hc:ε*L^(4*a)≤1:=(le_div_iff₀ (pow_pos hLp _)).mp (by simpa only [one_div] using hpaper z hz hfloor)
    have hp:L≤L^(4*a):=by simpa only [pow_one] using pow_le_pow_right₀ hlog (by omega:1≤4*a)
    exact (mul_le_mul_of_nonneg_right hp hε).trans (by nlinarith only [hc])
  have hδD:δ≤D:=by
    have hh:=mul_le_mul_of_nonneg_left hεL hD
    dsimp only [δ]
    nlinarith only [hh]
  have hwholeM:=hwhole g o z q hz hzB hfloor hq hprior hballs labels samples x y
  have hfarM:=hfar g o z q hz hzB hfloor hq hprior hballs labels samples x y
  have hindexed:=hinv g o z q hz hzB hfloor hq hprior hballs labels samples x y A (Set.Subset.refl _)
  have hcaps:=s.removed_first_inverse_caps_of_indexed selector A (M.extensionGreen q z) C hindexed W
    (s.outerFirstRegion_subset_removed selector r x y A)
  have ho:=s.partialFirst_removed_offdiagonal_of_indexed selector A (M.extensionGreen q z) δ
    (hoff g o z q hz hzB hfloor hq hprior hballs labels samples x y A (Set.Subset.refl _))
  intro u v hv
  let vB:BB:=⟨v.val,hv⟩
  have hleft:(∑w:W,‖M.extensionGreen q z u.val w.val‖)≤K:=
    (sum_norm_subtype_le W BB (s.outerFirstRegion_subset_removed selector r x y A)
      (fun w:A=>M.extensionGreen q z u.val w)).trans (hwholeM u.val)
  have hright:∀w:W,‖M.extensionGreen q z w.val v.val‖≤δ:=by
    intro w
    let wB:BB:=⟨w.val,s.outerFirstRegion_subset_removed selector r x y A w.property⟩
    have hne:wB≠vB:=by
      intro heq
      have heq':w.val=v.val:=congrArg Subtype.val heq
      exact v.property (heq' ▸ w.property)
    exact ho wB vB hne
  have hdiff:=M.deleted_target_difference_left_mass_any_rows hd W q z hz hq C K δ hC hK hδ
    _ _ hcaps.2.1 u v hleft hright
  have hdiffRev:‖(M.delete W).extensionGreen q z u v-M.extensionGreen q z u.val v.val‖≤K*C*δ:=
    (norm_sub_rev _ _).trans_le hdiff
  have htri:‖(M.delete W).extensionGreen q z u v‖≤‖M.extensionGreen q z u.val v.val‖+K*C*δ:=by
    have hh:=norm_add_le ((M.delete W).extensionGreen q z u v-M.extensionGreen q z u.val v.val)
      (M.extensionGreen q z u.val v.val)
    rw [sub_add_cancel] at hh
    exact hh.trans ((add_le_add_right hdiffRev _).trans_eq (add_comm _ _))
  have hsingle:‖M.extensionGreen q z u.val v.val‖≤K:=by
    have hh:‖M.extensionGreen q z u.val vB.val‖≤∑w:BB,‖M.extensionGreen q z u.val w.val‖:=
      Finset.single_le_sum (fun w _=>norm_nonneg (M.extensionGreen q z u.val w.val)) (Finset.mem_univ vB)
    exact hh.trans (hwholeM u.val)
  constructor
  · exact htri.trans ((add_le_add hsingle (mul_le_mul_of_nonneg_left hδD (mul_nonneg hK hC))).trans_eq rfl)
  · intro h hgeo
    have hh:=hfarM u.val vB h hgeo
    have hsum:=htri.trans (add_le_add_right hh _)
    exact hsum.trans_eq (by
      change _=sourceSelectedFarLeading d β Bcap C1*L*physicalTransfer d z^h+
        (sourceSelectedFarError d β Bcap C1+K*C*D)*L*ε
      dsimp only [δ]
      ring)

end RegularGraph
end LocalLaw
