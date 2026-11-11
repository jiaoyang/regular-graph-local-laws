import LocalLaw.RegionalEntireKernel
import LocalLaw.SourceRegionalCutRows

/-! # Actual entire-kernel decay on every supported regional surgery model -/

open Filter
noncomputable section
set_option maxHeartbeats 1600000
namespace LocalLaw
local instance sourceRegionalEntireDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceRegionalEntireLeading (d:ℕ)(β B C1:ℝ):ℝ:=
  sourceLocalSelectedCoreCap d β B C1*(1+(d:ℝ)*sourceRegionalSelectedWholeCap d B C1)+
    sourceRegionalSelectedLeading d β B C1*(sourceRegionalSelectedCutCap d B C1+1)

def sourceRegionalEntireError (d:ℕ)(β B C1:ℝ):ℝ:=
  sourceLocalSelectedCoreCap d β B C1*(1+(d:ℝ)*sourceRegionalSelectedWholeCap d B C1)+
    sourceRegionalSelectedError d β B C1*(sourceRegionalSelectedCutCap d B C1+1)


theorem sourceRegionalEntireLeading_nonnegative (d:ℕ)(hd:3≤d)(β B C1:ℝ) :
    0≤sourceRegionalEntireLeading d β B C1:=by
  have hCe:=finiteExtraReferenceConstant_ge_one d hd
  have hc0:0≤finiteExtraReferenceConstant d:=by linarith
  dsimp only[sourceRegionalEntireLeading,sourceLocalSelectedCoreCap,sourceRegionalSelectedWholeCap,
    sourcePartialEndpointRowCap,sourceRegionalSelectedCutCap,sourceRegionalSelectedLeading]
  positivity

theorem sourceRegionalEntireError_nonnegative (d:ℕ)(hd:3≤d)(β B C1:ℝ) :
    0≤sourceRegionalEntireError d β B C1:=by
  have hCe:=finiteExtraReferenceConstant_ge_one d hd
  have hc0:0≤finiteExtraReferenceConstant d:=by linarith
  dsimp only[sourceRegionalEntireError,sourceLocalSelectedCoreCap,sourceRegionalSelectedWholeCap,
    sourcePartialEndpointRowCap,sourceRegionalSelectedCutCap,sourceRegionalSelectedError,
    sourceRegionalSelectedLeading,sourcePartialFirstOffDiagonalConstant]
  positivity

namespace RegularGraph

theorem eventually_source_regional_entire_decay (a b d : ℕ) (c β Bcap C1 : ℝ)
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
      ∀(u v:S)(h:ℕ),((2*h+2:ℕ):ℕ∞)≤M.graph.edist u v→
        ‖M.extensionGreen q z u v‖≤
          sourceRegionalEntireLeading d β Bcap C1*Real.log (N:ℝ)*physicalTransfer d z^h+
            sourceRegionalEntireError d β Bcap C1*Real.log (N:ℝ)*graphPaperError a d N (logarithmicRadius β d N) z := by
  let K:=sourceLocalSelectedCoreCap d β Bcap C1
  let A:=sourceRegionalSelectedLeading d β Bcap C1
  let D:=sourceRegionalSelectedError d β Bcap C1
  let U:=sourceRegionalSelectedCutCap d Bcap C1
  let B:=sourceRegionalSelectedWholeCap d Bcap C1
  have hCe:=finiteExtraReferenceConstant_ge_one d hd
  have hK:0≤K:=by dsimp only[K,sourceLocalSelectedCoreCap];positivity
  have hU:0≤U:=by dsimp only[U,sourceRegionalSelectedCutCap];positivity
  have hB:0≤B:=by dsimp only[B,sourceRegionalSelectedWholeCap,sourcePartialEndpointRowCap];positivity
  have hA:0≤A:=by
    dsimp only[A,sourceRegionalSelectedLeading,sourcePartialEndpointRowCap,sourceLocalSelectedCoreCap];positivity
  have hD:0≤D:=by
    change 0≤A+sourcePartialFirstOffDiagonalConstant d β Bcap C1*(U+1)
    dsimp only[sourcePartialFirstOffDiagonalConstant];positivity
  filter_upwards [eventually_source_regional_cut_rows a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_regional_selected_columns a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_omitted_restored_decay a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_log_ge_nat 1,eventually_ge_atTop 1]
    with N hcut hcolumns hcore hlog hN
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  intro S hS hregion
  let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S
  let BB:=s.partialFirstRemovedSet selector S
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  have hL:0≤L:=by dsimp only[L];linarith
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hcp:=g.native_omitted_core_decay T labels samples selector S q z Bcap C1
    (omittedCompletionObservationLogCap d β) L ε hL hε
    (hcore g o z q hz hzB hfloor hq hprior hballs labels samples x y S hS)
  have hdecay:∀u v:(BBᶜ:Set S),∀n:ℕ,(n:ℕ∞)≤(M.delete BB).graph.edist u v→
      ‖(M.delete BB).extensionGreen q z u v‖≤K*L*physicalTransfer d z^n+K*L*ε:=by
    intro u v n hn
    have hh:=hcp u v n hn
    have he:=(M.delete BB).extensionGreen_decidableEq_eq
      (fun a b=>Classical.propDecidable (a=b)) inferInstance q z
    rw[he] at hh
    exact hh
  have hct:(∀u:(BBᶜ:Set S),(∑b:BB,‖((M.delete BB).extensionGreen q z*M.H.submatrix
      (Subtype.val:(BBᶜ:Set S)→S) (Subtype.val:BB→S)) u b‖)≤U):=by
    have hh:=hcut g o z q hz hzB hfloor hq hprior hballs labels samples x y S hS hregion
    dsimp only at hh
    have he:=(M.delete BB).extensionGreen_decidableEq_eq
      (fun a b=>Classical.propDecidable (a=b)) inferInstance q z
    rw[he] at hh
    exact hh
  have hc:=hcolumns g o z q hz hzB hfloor hq hprior hballs labels samples x y S hS hregion
  intro u v h hfar
  exact M.entire_kernel_of_fixed_rows hd BB q z hz hq K L ε A D U B hK hL hε hA hD hU hB
    hdecay hct hc.1 hc.2 u v h hfar

end RegularGraph
end LocalLaw
