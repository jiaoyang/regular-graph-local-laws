import LocalLaw.SourceSelectedFarColumns
import LocalLaw.SelectedFirstKernelRowsTransport
import LocalLaw.DeletedSampleCrossRows

/-! # Fixed sampled-vertex row sums for every actual augmented target -/

open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
namespace LocalLaw
local instance sourceSelectedWholeRowsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceSelectedWholeRowCap (d:ℕ)(B:ℝ):ℝ:=
  sourcePartialEndpointRowCap d*(sourceSelectedCutRowCap d B+1)

namespace RegularGraph

theorem eventually_source_selected_whole_rows (a b d:ℕ)(c β Bcap C1:ℝ)
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
      let B:=s.partialFirstRemovedSet selector A
      ∀u:A,∑v:B,‖M.extensionGreen q z u v.val‖≤sourceSelectedWholeRowCap d Bcap := by
  let C:=sourcePartialEndpointRowCap d
  let U:=sourceSelectedCutRowCap d Bcap
  have hce:=finiteExtraReferenceConstant_ge_one d hd
  have hC:0≤C:=by dsimp only [C,sourcePartialEndpointRowCap];positivity
  filter_upwards [eventually_source_selected_cut_rows a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_partial_endpoint_caps a b d c β Bcap C1 ha hb hd hc hβ hβc hC1]
    with N hcut hcaps
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let A:=s.twoTargetEndpointVertices selector r x y
  let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict A
  let B:=s.partialFirstRemovedSet selector A
  have hBcap:0≤Bcap:=(norm_nonneg z).trans hzB
  have hU:0≤U:=by
    dsimp only [U,sourceSelectedCutRowCap,leafDeletedMateRowCap,leafDeletedSeparatedRowCap]
    positivity
  have hee:=hcaps g o z q hz hzB hfloor hq hprior hballs labels samples x y A (Set.Subset.refl _)
  have hBB:∀u:B,∑v:B,‖M.extensionGreen q z u.val v.val‖≤C:=
    s.partialFirst_removed_rows_of_endpoint_rows selector A (M.extensionGreen q z) C hee.1
  have hcutOld:=hcut g o z q hz hzB hfloor hq hprior hballs labels samples x y
  dsimp only [SelectedCutRowsControlled] at hcutOld
  have hdeleted:M.delete B=((g.deficient.delete T).restrict A).delete B:=
    g.restricted_selectedFirst_deletion_eq T labels samples selector A
      (s.selectedFirstSet_subset_twoTarget selector r x y)
  have hcutNew:letI : DecidableEq (Bᶜ:Set A):=fun a b=>Classical.propDecidable (a=b)
      ∀u:(Bᶜ:Set A),(∑j:B,‖((M.delete B).extensionGreen q z*M.H.submatrix
        (Subtype.val:(Bᶜ:Set A)→A) (Subtype.val:B→A)) u j‖)≤U:=by
    rw [hdeleted]
    exact hcutOld
  have hcross:=M.deleted_sample_cross_rows hd B q z hz hq U C hC hcutNew hBB
  intro u
  by_cases hu:u∈B
  · have he:=hBB ⟨u,hu⟩
    have hh:C≤C*(U+1):=by nlinarith only [mul_nonneg hC hU]
    exact he.trans hh
  · have he:=hcross ⟨u,hu⟩
    have hh:U*C≤C*(U+1):=by nlinarith only [hC]
    exact he.trans hh

end RegularGraph
end LocalLaw
