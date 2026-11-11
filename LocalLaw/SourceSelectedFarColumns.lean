import LocalLaw.SelectedFirstKernelCapsTransport
import LocalLaw.ActualSourcePartialEndpointCaps
import LocalLaw.SourcePartialFirstOffDiagonal
import LocalLaw.SwitchedCommonKernelTransport
import LocalLaw.SourceSelectedCutRows
import LocalLaw.LeafCoreFarAdapter

/-! # Actual sampled columns away from either target

Only the original strong-radius graph budget and the weak scalar prior
are assumed. Both sampled and nonsampled targets are covered.
-/

open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 650000
namespace LocalLaw
local instance sourceSelectedFarColumnsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceSelectedCutRowCap (d : ℕ) (B : ℝ) : ℝ :=
  (Real.sqrt ((d:ℝ)-1))⁻¹*(leafDeletedMateRowCap d B+leafDeletedSeparatedRowCap d B)

def sourceSelectedFarLeading (d : ℕ) (β B C1 : ℝ) : ℝ :=
  sourcePartialEndpointRowCap d *
    leafDeletedCoreDecayConstant d B (leafCompletionObservationLogCap d β) C1 *
      ((d:ℝ)/Real.sqrt ((d:ℝ)-1))

def sourceSelectedFarError (d : ℕ) (β B C1 : ℝ) : ℝ :=
  sourceSelectedFarLeading d β B C1 +
    sourcePartialFirstOffDiagonalConstant d β B C1*(sourceSelectedCutRowCap d B+1)

namespace RegularGraph

theorem eventually_source_selected_far_columns (a b d : ℕ) (c β Bcap C1 : ℝ)
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
      let A:=s.twoTargetEndpointVertices selector r x y
      let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict A
      let B:=s.partialFirstRemovedSet selector A
      ∀(u:A)(v:B)(h:ℕ),((h+1:ℕ):ℕ∞)≤M.graph.edist u v.val →
        ‖M.extensionGreen q z u v.val‖≤
          sourceSelectedFarLeading d β Bcap C1*Real.log (N:ℝ)*physicalTransfer d z^h+
            sourceSelectedFarError d β Bcap C1*Real.log (N:ℝ)*
              graphPaperError a d N (logarithmicRadius β d N) z := by
  let K:=leafDeletedCoreDecayConstant d Bcap (leafCompletionObservationLogCap d β) C1
  let C:=sourcePartialEndpointRowCap d
  let D:=sourcePartialFirstOffDiagonalConstant d β Bcap C1
  let U:=sourceSelectedCutRowCap d Bcap
  have hCextra:=finiteExtraReferenceConstant_ge_one d hd
  have hC : 0≤C := by dsimp only [C,sourcePartialEndpointRowCap]; positivity
  have hD : 0≤D := by
    dsimp only [D,sourcePartialFirstOffDiagonalConstant]
    positivity
  have hAlog : 0≤leafCompletionObservationLogCap d β := by
    dsimp only [leafCompletionObservationLogCap]
    exact mul_nonneg (by positivity) (sourceObservationLogCap_nonnegative d hd β hβ.le)
  have hK : 0≤K := leafDeletedCoreDecayConstant_nonnegative d hd Bcap _ C1 hAlog
  have hlead : 0≤sourceSelectedFarLeading d β Bcap C1 := by
    change 0≤C*K*((d:ℝ)/Real.sqrt ((d:ℝ)-1))
    positivity
  filter_upwards [eventually_source_common_leaf_kernel_decay a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_selected_cut_rows a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_partial_endpoint_caps a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_partial_first_offdiagonal a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_sourceObservationBounds a b d c β Bcap C1 ha hb hd hc hβ hβc hC1]
    with N hcore hcut hcaps hoff hnum
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let A:=s.twoTargetEndpointVertices selector r x y
  let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict A
  let B:=s.partialFirstRemovedSet selector A
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let δ:=D*L*ε
  letI : DecidableEq (Bᶜ:Set A):=fun a b=>Classical.propDecidable (a=b)
  have hBcap : 0≤Bcap := (norm_nonneg z).trans hzB
  have hU : 0≤U := by
    dsimp only [U,sourceSelectedCutRowCap,leafDeletedMateRowCap,leafDeletedSeparatedRowCap]
    positivity
  have num:=hnum z hz hfloor
  have hL : 0≤L := by linarith [num.log_one]
  have hδ : 0≤δ := mul_nonneg (mul_nonneg hD hL) num.error_nonnegative
  have hrows:=hcaps g o z q hz hzB hfloor hq hprior hballs labels samples x y A (Set.Subset.refl _)
  have hdiag : ∀v:B,‖M.extensionGreen q z v.val v.val‖≤C :=
    s.partialFirst_removed_diagonal_of_endpoint_rows selector A (M.extensionGreen q z) C hrows.1
  have hoffset : ∀u v:B,u≠v→‖M.extensionGreen q z u.val v.val‖≤δ :=
    s.partialFirst_removed_offdiagonal_of_indexed selector A (M.extensionGreen q z) δ
      (hoff g o z q hz hzB hfloor hq hprior hballs labels samples x y A (Set.Subset.refl _))
  have hold:=hcore g o z q hz hzB hfloor hq hprior hballs labels samples x y
  have hdecay:=g.switched_common_core_decay T labels samples selector A
    (s.selectedFirstSet_subset_twoTarget selector r x y) q z K L ε hold
  have hcutOld:=hcut g o z q hz hzB hfloor hq hprior hballs labels samples x y
  dsimp only [SelectedCutRowsControlled] at hcutOld
  have hdeleted : M.delete B=((g.deficient.delete T).restrict A).delete B :=
    g.restricted_selectedFirst_deletion_eq T labels samples selector A
      (s.selectedFirstSet_subset_twoTarget selector r x y)
  have hcutNew (u:(Bᶜ:Set A)) :
      (∑j:B,‖((M.delete B).extensionGreen q z*M.H.submatrix
        (Subtype.val:(Bᶜ:Set A)→A) (Subtype.val:B→A)) u j‖)≤U := by
    rw [hdeleted]
    exact hcutOld u
  intro u v h hfar
  by_cases hu:u∈B
  · let uB:B:=⟨u,hu⟩
    have huv:uB≠v := by
      intro heq
      have heq' : u=v.val := congrArg Subtype.val heq
      have hbad : ((h+1:ℕ):ℕ∞)≤0 := by simpa only [heq',SimpleGraph.edist_self] using hfar
      have hnat : h+1≤0 := ENat.coe_le_coe.mp hbad
      omega
    have he : ‖M.extensionGreen q z u v.val‖≤δ := hoffset uB v huv
    have hDle : D≤sourceSelectedFarError d β Bcap C1 := by
      change D≤sourceSelectedFarLeading d β Bcap C1+D*(U+1)
      nlinarith
    exact he.trans (by
      have hεprod : 0≤L*ε := mul_nonneg hL num.error_nonnegative
      have hm:=mul_le_mul_of_nonneg_right hDle hεprod
      have ht:=mul_nonneg (mul_nonneg hlead hL) (pow_nonneg (physicalTransfer_pos d hd z).le h)
      dsimp only [δ]
      nlinarith only [hm,ht])
  · have he : ‖M.extensionGreen q z u v.val‖≤
        C*((K*L*physicalTransfer d z^h+K*L*ε)*((d:ℝ)/Real.sqrt ((d:ℝ)-1)))+δ*U := by
      exact M.sampled_far_column_of_leafCoreDecayBound hd B q z hz hq K L ε C δ U
        hK hL num.error_nonnegative hC hδ hdecay ⟨u,hu⟩ v h hfar (hdiag v)
        (fun j hj=>hoffset j v hj) (hcutNew ⟨u,hu⟩)
    have hid : C*((K*L*physicalTransfer d z^h+K*L*ε)*((d:ℝ)/Real.sqrt ((d:ℝ)-1)))+δ*U =
        sourceSelectedFarLeading d β Bcap C1*L*physicalTransfer d z^h+
        sourceSelectedFarError d β Bcap C1*L*ε-δ := by
      change C*((K*L*physicalTransfer d z^h+K*L*ε)*((d:ℝ)/Real.sqrt ((d:ℝ)-1)))+δ*U =
        (C*K*((d:ℝ)/Real.sqrt ((d:ℝ)-1)))*L*physicalTransfer d z^h+
        (C*K*((d:ℝ)/Real.sqrt ((d:ℝ)-1))+D*(U+1))*L*ε-δ
      dsimp only [δ]
      ring
    rw [hid] at he
    exact he.trans (sub_le_self _ hδ)

end RegularGraph
end LocalLaw
