import LocalLaw.NativeOmittedCoreDecay
import LocalLaw.SmallSampleCutRows
import LocalLaw.SurgeryBallCapture
import LocalLaw.SourceSelectedFarColumns
import LocalLaw.SelectedFirstKernelRowsTransport
import LocalLaw.DeletedSampleCrossRows

/-! # Actual local sampled columns and their logarithmic row masses -/

open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2500000
namespace LocalLaw
local instance sourceLocalSelectedDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceLocalSelectedCoreCap (d:ℕ)(β B C1:ℝ):ℝ:=
  |omittedRestoredSpatialConstant d B (omittedCompletionObservationLogCap d β)|+
    |omittedRestoredErrorConstant d B C1 (omittedCompletionObservationLogCap d β)|+1

def sourceLocalSelectedCutCap (d:ℕ)(β B C1:ℝ):ℝ:=4*(d:ℝ)*sourceLocalSelectedCoreCap d β B C1

def sourceLocalSelectedWholeCap (d:ℕ)(β B C1:ℝ):ℝ:=
  sourcePartialEndpointRowCap d*(sourceLocalSelectedCutCap d β B C1+1)

def sourceLocalSelectedLeading (d:ℕ)(β B C1:ℝ):ℝ:=
  sourcePartialEndpointRowCap d*sourceLocalSelectedCoreCap d β B C1*((d:ℝ)/Real.sqrt ((d:ℝ)-1))

def sourceLocalSelectedError (d:ℕ)(β B C1:ℝ):ℝ:=
  sourceLocalSelectedLeading d β B C1+
    sourcePartialFirstOffDiagonalConstant d β B C1*(sourceLocalSelectedCutCap d β B C1+1)

namespace RegularGraph

theorem eventually_source_local_selected_columns (a b d : ℕ) (c β Bcap C1 : ℝ)
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
      let A:=pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
      let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict A
      let B:=s.partialFirstRemovedSet selector A
      (∀u:A,∑v:B,‖M.extensionGreen q z u v.val‖≤
        sourceLocalSelectedWholeCap d β Bcap C1*Real.log (N:ℝ)) ∧
      ∀(u:A)(v:B)(h:ℕ),((h+1:ℕ):ℕ∞)≤M.graph.edist u v.val →
        ‖M.extensionGreen q z u v.val‖≤
          sourceLocalSelectedLeading d β Bcap C1*Real.log (N:ℝ)*physicalTransfer d z^h+
            sourceLocalSelectedError d β Bcap C1*Real.log (N:ℝ)^2*
              graphPaperError a d N (logarithmicRadius β d N) z := by
  let K:=sourceLocalSelectedCoreCap d β Bcap C1
  let C:=sourcePartialEndpointRowCap d
  let D:=sourcePartialFirstOffDiagonalConstant d β Bcap C1
  let U:=sourceLocalSelectedCutCap d β Bcap C1
  have hCe:=finiteExtraReferenceConstant_ge_one d hd
  have hK:0≤K:=by dsimp only[K,sourceLocalSelectedCoreCap];positivity
  have hC:0≤C:=by dsimp only[C,sourcePartialEndpointRowCap];positivity
  have hD:0≤D:=by dsimp only[D,sourcePartialFirstOffDiagonalConstant];positivity
  have hU:0≤U:=by dsimp only[U,sourceLocalSelectedCutCap];positivity
  have hlead:0≤sourceLocalSelectedLeading d β Bcap C1:=by
    change 0≤C*K*((d:ℝ)/Real.sqrt ((d:ℝ)-1))
    positivity
  filter_upwards [eventually_source_omitted_restored_decay a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_partial_endpoint_caps a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_partial_first_offdiagonal a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_sourceObservationBounds a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc]
    with N hcore hcaps hoff hnum hmargin
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let A:=pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
  let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict A
  let B:=s.partialFirstRemovedSet selector A
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let δ:=D*L*ε
  have num:=hnum z hz hfloor
  have hL:0≤L:=by linarith[num.log_one]
  have hε:0≤ε:=num.error_nonnegative
  have hεone:ε≤1:=by
    calc
      _≤C1^2*ε:=le_mul_of_one_le_left hε (one_le_pow₀ hC1)
      _≤(C1^2*ε)*L^4:=le_mul_of_one_le_right (by positivity) (one_le_pow₀ num.log_one)
      _≤1:=num.error_scaled
  have hsep:2*r≤selector:=by dsimp only[r,selector];omega
  have hcard:Nat.card B≤2:=s.partialFirstRemovedSet_new_pair_card selector r hsep x y
  have hS:A⊆s.twoTargetEndpointVertices selector r x y:=s.twoTargetEndpointVertices_contains_new_pair selector r x y
  have hold:=hcore g o z q hz hzB hfloor hq hprior hballs labels samples x y A hS
  have hdecay:=g.native_omitted_core_decay T labels samples selector A q z Bcap C1
    (omittedCompletionObservationLogCap d β) L ε hL hε hold
  have hcut:=M.small_sample_cut_rows hd B q z K L ε hK hL hε hεone hcard hdecay
  have hcut':letI:DecidableEq (Bᶜ:Set A):=fun a b=>Classical.propDecidable (a=b)
      ∀u:(Bᶜ:Set A),(∑j:B,‖((M.delete B).extensionGreen q z*M.H.submatrix
        (Subtype.val:(Bᶜ:Set A)→A) (Subtype.val:B→A)) u j‖)≤U*L:=hcut
  have hee:=hcaps g o z q hz hzB hfloor hq hprior hballs labels samples x y A hS
  have hBB:∀u:B,∑v:B,‖M.extensionGreen q z u.val v.val‖≤C:=
    s.partialFirst_removed_rows_of_endpoint_rows selector A (M.extensionGreen q z) C hee.1
  have hdiag:∀v:B,‖M.extensionGreen q z v.val v.val‖≤C:=
    s.partialFirst_removed_diagonal_of_endpoint_rows selector A (M.extensionGreen q z) C hee.1
  have hoffset:∀u v:B,u≠v→‖M.extensionGreen q z u.val v.val‖≤δ:=
    s.partialFirst_removed_offdiagonal_of_indexed selector A (M.extensionGreen q z) δ
      (hoff g o z q hz hzB hfloor hq hprior hballs labels samples x y A hS)
  have hcross:=M.deleted_sample_cross_rows hd B q z hz hq (U*L) C hC hcut' hBB
  refine ⟨?_,?_⟩
  · intro u
    change (∑v:B,‖M.extensionGreen q z u v.val‖)≤C*(U+1)*L
    by_cases hu:u∈B
    · exact (hBB ⟨u,hu⟩).trans (by nlinarith only [mul_nonneg hC hU,mul_le_mul_of_nonneg_left num.log_one (show 0≤C*(U+1) by positivity)])
    · exact (hcross ⟨u,hu⟩).trans (by nlinarith only [mul_nonneg hC hL])
  · intro u v h hfar
    have hδ:0≤δ:=by dsimp only[δ];positivity
    by_cases hu:u∈B
    · let uB:B:=⟨u,hu⟩
      have huv:uB≠v:=by
        intro heq
        have heq':u=v.val:=congrArg Subtype.val heq
        have hbad:((h+1:ℕ):ℕ∞)≤0:=by simpa only[heq',SimpleGraph.edist_self] using hfar
        have hh:h+1≤0:=ENat.coe_le_coe.mp hbad
        omega
      have hh:=hoffset uB v huv
      have hDe:D≤sourceLocalSelectedError d β Bcap C1:=by
        change D≤sourceLocalSelectedLeading d β Bcap C1+D*(U+1)
        nlinarith only [hlead,mul_nonneg hD hU]
      have hLE:L*ε≤L^2*ε:=by nlinarith only [mul_le_mul_of_nonneg_right num.log_one (mul_nonneg hL hε)]
      have hscaled:=mul_le_mul_of_nonneg_left hLE hD
      have he:=mul_le_mul_of_nonneg_right hDe (show 0≤L^2*ε by positivity)
      have ht:=mul_nonneg (mul_nonneg hlead hL) (pow_nonneg (physicalTransfer_pos d hd z).le h)
      exact hh.trans (by dsimp only[δ] at *;nlinarith only[hscaled,he,ht])
    · have he:=M.sampled_far_column_of_leafCoreDecayBound hd B q z hz hq K L ε C δ (U*L)
        hK hL hε hC hδ hdecay ⟨u,hu⟩ v h hfar (hdiag v)
        (fun j hj=>hoffset j v hj) (hcut' ⟨u,hu⟩)
      have hid:C*((K*L*physicalTransfer d z^h+K*L*ε)*((d:ℝ)/Real.sqrt ((d:ℝ)-1)))+δ*(U*L)=
          sourceLocalSelectedLeading d β Bcap C1*L*physicalTransfer d z^h+
            sourceLocalSelectedLeading d β Bcap C1*L*ε+D*U*L^2*ε:=by
        change _=(C*K*((d:ℝ)/Real.sqrt ((d:ℝ)-1)))*L*physicalTransfer d z^h+
          (C*K*((d:ℝ)/Real.sqrt ((d:ℝ)-1)))*L*ε+D*U*L^2*ε
        dsimp only[δ]
        ring
      rw[hid] at he
      have hLE:L*ε≤L^2*ε:=by nlinarith only [mul_le_mul_of_nonneg_right num.log_one (mul_nonneg hL hε)]
      have hs:=mul_le_mul_of_nonneg_left hLE hlead
      exact he.trans (by
        change _≤sourceLocalSelectedLeading d β Bcap C1*L*physicalTransfer d z^h+
          (sourceLocalSelectedLeading d β Bcap C1+D*(U+1))*L^2*ε
        have hz0:0≤D*L^2*ε:=by positivity
        nlinarith only[hs,hz0])

end RegularGraph
end LocalLaw
