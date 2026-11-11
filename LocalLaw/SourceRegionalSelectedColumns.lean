import LocalLaw.RegionalCommonCutRows
import LocalLaw.SmallSampleFixedCutRows
import LocalLaw.SourceLocalSelectedColumns
import LocalLaw.SourceOmittedRestoredEntryCap

/-! # Fixed sampled rows for a fully retained region or at most two sampled roots -/

open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance sourceRegionalSelectedDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceRegionalSelectedCutCap (d:ℕ)(B C1:ℝ):ℝ:=
  |sourceSelectedCutRowCap d B|+2*(d:ℝ)*(|omittedRestoredEntryCap d B C1|+1)+1

def sourceRegionalSelectedWholeCap (d:ℕ)(B C1:ℝ):ℝ:=
  sourcePartialEndpointRowCap d*(sourceRegionalSelectedCutCap d B C1+1)

def sourceRegionalSelectedLeading (d:ℕ)(β B C1:ℝ):ℝ:=
  sourcePartialEndpointRowCap d*sourceLocalSelectedCoreCap d β B C1*((d:ℝ)/Real.sqrt ((d:ℝ)-1))

def sourceRegionalSelectedError (d:ℕ)(β B C1:ℝ):ℝ:=
  sourceRegionalSelectedLeading d β B C1+
    sourcePartialFirstOffDiagonalConstant d β B C1*(sourceRegionalSelectedCutCap d B C1+1)

namespace RegularGraph

theorem eventually_source_regional_selected_columns (a b d : ℕ) (c β Bcap C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in atTop,∀(g : RegularGraph N d)(o : Fin N)(z q : ℂ),
      0<z.im → ‖z‖≤Bcap → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → 0≤q.im →
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) →
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀{ι : Type}[Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y : ((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      ∀S:Set (Tᶜ:Set (Fin N)),S⊆s.twoTargetEndpointVertices selector r x y→
      ((s.selectedFirstSet selector⊆S ∧ ∀i:s.AdmissibleSampleIndex selector,s.admissibleBoundaryVertex selector i∈S) ∨
        Nat.card (s.partialFirstRemovedSet selector S)≤2)→
      let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S
      let B:=s.partialFirstRemovedSet selector S
      (∀u:S,∑v:B,‖M.extensionGreen q z u v.val‖≤sourceRegionalSelectedWholeCap d Bcap C1) ∧
      ∀(u:S)(v:B)(h:ℕ),((h+1:ℕ):ℕ∞)≤M.graph.edist u v.val→
        ‖M.extensionGreen q z u v.val‖≤
          sourceRegionalSelectedLeading d β Bcap C1*Real.log (N:ℝ)*physicalTransfer d z^h+
            sourceRegionalSelectedError d β Bcap C1*Real.log (N:ℝ)*
              graphPaperError a d N (logarithmicRadius β d N) z := by
  let K:=sourceLocalSelectedCoreCap d β Bcap C1
  let C:=sourcePartialEndpointRowCap d
  let D:=sourcePartialFirstOffDiagonalConstant d β Bcap C1
  let U:=sourceRegionalSelectedCutCap d Bcap C1
  let C0:=|omittedRestoredEntryCap d Bcap C1|+1
  have hCe:=finiteExtraReferenceConstant_ge_one d hd
  have hK:0≤K:=by dsimp only[K,sourceLocalSelectedCoreCap];positivity
  have hC:0≤C:=by dsimp only[C,sourcePartialEndpointRowCap];positivity
  have hD:0≤D:=by dsimp only[D,sourcePartialFirstOffDiagonalConstant];positivity
  have hU:0≤U:=by dsimp only[U,sourceRegionalSelectedCutCap];positivity
  have hC0:0≤C0:=by dsimp only[C0];positivity
  have hlead:0≤sourceRegionalSelectedLeading d β Bcap C1:=by
    change 0≤C*K*((d:ℝ)/Real.sqrt ((d:ℝ)-1));positivity
  filter_upwards [eventually_source_omitted_restored_decay a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_local_common_incidence_rows a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_omitted_restored_entry_cap a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_partial_endpoint_caps a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_partial_first_offdiagonal a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_sourceObservationBounds a b d c β Bcap C1 ha hb hd hc hβ hβc hC1]
    with N hcore hcommon hfixed hcaps hoff hnum
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  intro S hS hregion
  let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S
  let B:=s.partialFirstRemovedSet selector S
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let δ:=D*L*ε
  have num:=hnum z hz hfloor
  have hL:0≤L:=by linarith[num.log_one]
  have hε:0≤ε:=num.error_nonnegative
  have hδ:0≤δ:=by dsimp only[δ];positivity
  have hold:=hcore g o z q hz hzB hfloor hq hprior hballs labels samples x y S hS
  have hdecay:=g.native_omitted_core_decay T labels samples selector S q z Bcap C1
    (omittedCompletionObservationLogCap d β) L ε hL hε hold
  have hcut:letI:DecidableEq (Bᶜ:Set S):=fun a b=>Classical.propDecidable (a=b)
      ∀u:(Bᶜ:Set S),(∑j:B,‖((M.delete B).extensionGreen q z*M.H.submatrix
        (Subtype.val:(Bᶜ:Set S)→S) (Subtype.val:B→S)) u j‖)≤U:=by
    rcases hregion with ⟨hB,hA⟩|hsmall
    · have hr:=g.regional_selected_cut_rows_of_common_rows T labels samples selector S hB hA q z
        (leafDeletedMateRowCap d Bcap) (leafDeletedSeparatedRowCap d Bcap)
        (hcommon g o z q hz hzB hfloor hq hprior hballs labels samples x y S hS)
      intro u
      have hb:sourceSelectedCutRowCap d Bcap≤U:=by
        dsimp only[U,sourceRegionalSelectedCutCap]
        have hp:0≤2*(d:ℝ)*(|omittedRestoredEntryCap d Bcap C1|+1):=by positivity
        linarith [le_abs_self (sourceSelectedCutRowCap d Bcap)]
      exact (hr u).trans hb
    · letI:DecidableEq (Bᶜ:Set S):=fun a b=>Classical.propDecidable (a=b)
      have hp:∀u v:(Bᶜ:Set S),‖(M.delete B).extensionGreen q z u v‖≤C0:=by
        intro u v
        have hh:=hfixed g o z q hz hzB hfloor hq hprior hballs labels samples x y S hS u v
        have he:=(M.delete B).extensionGreen_decidableEq_eq (Subtype.instDecidableEq)
          (fun a b=>Classical.propDecidable (a=b)) q z
        rw[he] at hh
        exact hh.trans (by dsimp only[C0];linarith [le_abs_self (omittedRestoredEntryCap d Bcap C1)])
      have hr:=M.small_sample_fixed_cut_rows hd B q z C0 hC0 hsmall hp
      intro u
      have hb:2*(d:ℝ)*C0≤U:=by
        dsimp only[U,sourceRegionalSelectedCutCap,C0]
        linarith [abs_nonneg (sourceSelectedCutRowCap d Bcap)]
      exact (hr u).trans hb
  have hee:=hcaps g o z q hz hzB hfloor hq hprior hballs labels samples x y S hS
  have hBB:∀u:B,∑v:B,‖M.extensionGreen q z u.val v.val‖≤C:=
    s.partialFirst_removed_rows_of_endpoint_rows selector S (M.extensionGreen q z) C hee.1
  have hdiag:∀v:B,‖M.extensionGreen q z v.val v.val‖≤C:=
    s.partialFirst_removed_diagonal_of_endpoint_rows selector S (M.extensionGreen q z) C hee.1
  have hoffset:∀u v:B,u≠v→‖M.extensionGreen q z u.val v.val‖≤δ:=
    s.partialFirst_removed_offdiagonal_of_indexed selector S (M.extensionGreen q z) δ
      (hoff g o z q hz hzB hfloor hq hprior hballs labels samples x y S hS)
  have hcross:=M.deleted_sample_cross_rows hd B q z hz hq U C hC hcut hBB
  refine ⟨?_,?_⟩
  · intro u
    change (∑v:B,‖M.extensionGreen q z u v.val‖)≤C*(U+1)
    by_cases hu:u∈B
    · exact (hBB ⟨u,hu⟩).trans (by nlinarith only[mul_nonneg hC hU])
    · exact (hcross ⟨u,hu⟩).trans (by nlinarith only[hC])
  · intro u v h hfar
    by_cases hu:u∈B
    · let uB:B:=⟨u,hu⟩
      have huv:uB≠v:=by
        intro heq
        have heq':u=v.val:=congrArg Subtype.val heq
        have hbad:((h+1:ℕ):ℕ∞)≤0:=by simpa only[heq',SimpleGraph.edist_self] using hfar
        have hh:h+1≤0:=ENat.coe_le_coe.mp hbad
        omega
      have hh:=hoffset uB v huv
      have hDe:D≤sourceRegionalSelectedError d β Bcap C1:=by
        change D≤sourceRegionalSelectedLeading d β Bcap C1+D*(U+1)
        nlinarith only[hlead,mul_nonneg hD hU]
      have hs:=mul_le_mul_of_nonneg_right hDe (mul_nonneg hL hε)
      have ht:=mul_nonneg (mul_nonneg hlead hL) (pow_nonneg (physicalTransfer_pos d hd z).le h)
      exact hh.trans (by dsimp only[δ] at *;nlinarith only[hs,ht])
    · have he:=M.sampled_far_column_of_leafCoreDecayBound hd B q z hz hq K L ε C δ U
        hK hL hε hC hδ hdecay ⟨u,hu⟩ v h hfar (hdiag v)
        (fun j hj=>hoffset j v hj) (hcut ⟨u,hu⟩)
      have hid:C*((K*L*physicalTransfer d z^h+K*L*ε)*((d:ℝ)/Real.sqrt ((d:ℝ)-1)))+δ*U=
          sourceRegionalSelectedLeading d β Bcap C1*L*physicalTransfer d z^h+
            sourceRegionalSelectedError d β Bcap C1*L*ε-δ:=by
        change _=(C*K*((d:ℝ)/Real.sqrt ((d:ℝ)-1)))*L*physicalTransfer d z^h+
          (C*K*((d:ℝ)/Real.sqrt ((d:ℝ)-1))+D*(U+1))*L*ε-δ
        dsimp only[δ];ring
      rw[hid] at he
      exact he.trans (sub_le_self _ hδ)

end RegularGraph
end LocalLaw
