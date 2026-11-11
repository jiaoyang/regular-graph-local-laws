import LocalLaw.SourceRegionalSelectedColumns
import LocalLaw.FullRegionSupport
import LocalLaw.SourcePartialFirstPrincipalCaps
import LocalLaw.PartialFirstRemovedRows
import LocalLaw.DeletionRowsInstanceAdapter
import LocalLaw.StructuredOuterTail
import LocalLaw.PhysicalTailRadiusLoss
import LocalLaw.FullOutsideReplacement

/-! # Structured cost of deleting the far samples on either full-region side

The sample count multiplies only the spatial tail. Actual source smallness
removes it from the ordinary error before the full T harmonic lift.
-/
open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2500000
namespace LocalLaw
local instance sourceFullRegionOuterDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceFullRegionOuterInverse (d:ℕ)(B:ℝ):ℝ:=4*sourcePartialFirstInverseCap d B
def sourceFullRegionOuterLeading (d:ℕ)(β B C1:ℝ):ℝ:=|sourceRegionalSelectedLeading d β B C1|+1
def sourceFullRegionOuterError (d:ℕ)(β B C1:ℝ):ℝ:=|sourceRegionalSelectedError d β B C1|+1

def sourceFullRegionOuterMain (d:ℕ)(β B C1:ℝ):ℝ:=
  2*sourceFullRegionOuterInverse d B*(sourceFullRegionOuterError d β B C1)^2

def sourceFullRegionOuterTail (d:ℕ)(β B C1:ℝ):ℝ:=
  2*sourceFullRegionOuterInverse d B*(sourceFullRegionOuterLeading d β B C1)^2*
    ((B+1)*‖(treeEdgeWeight d)⁻¹‖)^4

namespace RegularGraph

theorem eventually_source_full_region_outer_comparison (a b d:ℕ)(c β Bcap C1:ℝ)
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
      ∀S:Set (Tᶜ:Set (Fin N)),S⊆s.fullSliceOutside (s.fullTwoTargetVertices selector r x y)→
      ((s.selectedFirstSet selector⊆S ∧ ∀i:s.AdmissibleSampleIndex selector,s.admissibleBoundaryVertex selector i∈S) ∨
        Nat.card (s.partialFirstRemovedSet selector S)≤2)→
      let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S
      let O:=s.fullRegionOuterFirst selector r x y
      let W:Set S:={u|u.val∈O}
      let μ:=Nat.card (BoundaryOrientedEdge g.graph T)
      let L:=Real.log (N:ℝ)
      let ε:=graphPaperError a d N (logarithmicRadius β d N) z
      ∀loss:ℕ,loss≤r/2→∀u v:(Wᶜ:Set S),
      ((s.fullResample selector).graph.edist x u.val.val.val≤(loss:ℕ∞) ∨
        (s.fullResample selector).graph.edist y u.val.val.val≤(loss:ℕ∞))→
      ((s.fullResample selector).graph.edist x v.val.val.val≤(loss:ℕ∞) ∨
        (s.fullResample selector).graph.edist y v.val.val.val≤(loss:ℕ∞))→
      ‖M.extensionGreen q z u.val v.val-(M.delete W).extensionGreen q z u v‖≤
        sourceFullRegionOuterMain d β Bcap C1*L*ε+
          sourceFullRegionOuterTail d β Bcap C1*((μ:ℝ)+1)*L^4*physicalTransfer d z^(2*(r-loss)):=by
  let C:=sourceFullRegionOuterInverse d Bcap
  let A:=sourceFullRegionOuterLeading d β Bcap C1
  let D:=sourceFullRegionOuterError d β Bcap C1
  let Count:ℝ:=(d:ℝ)*((d:ℝ)+1)
  have hC:0≤C:=by
    have hce:=finiteExtraReferenceConstant_ge_one d hd
    dsimp only[C,sourceFullRegionOuterInverse,sourcePartialFirstInverseCap]
    positivity
  have hA:0≤A:=by dsimp only[A,sourceFullRegionOuterLeading];positivity
  have hD:0≤D:=by dsimp only[D,sourceFullRegionOuterError];positivity
  have hCount:0≤Count:=by dsimp only[Count];positivity
  filter_upwards [eventually_source_regional_selected_columns a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_partial_first_principal_caps a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_inner_complement_nonempty a d (by omega) hd,
    eventually_actual_boundary_card_log_bound a d hd (by omega),
    eventually_paperError_small a b d β ha hb hd hβ,
    eventually_resampling_radius_margin a d 2 8 β hd hβ,
    eventually_log_ge_nat Count,eventually_log_ge_nat 1,eventually_ge_atTop 1]
    with N hselected hinverse hdummy hμ hpaper hroom hlarge hlog hN
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  intro S hS0 hregion
  let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S
  let O:=s.fullRegionOuterFirst selector r x y
  let W:Set S:={u|u.val∈O}
  let μ:=Nat.card (BoundaryOrientedEdge g.graph T)
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let w:(Tᶜ:Set (Fin N)):=Classical.choice (hdummy g o z)
  let px:=s.outsideReplacement w x
  let py:=s.outsideReplacement w y
  have hS:S⊆s.twoTargetEndpointVertices selector r px py:=
    fun v hv=>s.fullTwoTarget_outside_subset_replacements selector r w x y (hS0 hv)
  have hselectedN:=hselected g o z q hz hzB hfloor hq hprior hballs labels samples px py S hS hregion
  have hinvN:=hinverse g o z q hz hzB hfloor hq hprior hballs labels samples px py S hS
  have hW:W⊆s.partialFirstRemovedSet selector S:=fun _ hv=>hv.1
  have hcaps:=s.removed_first_inverse_caps_of_indexed selector S (M.extensionGreen q z) C hinvN W hW
  have hWcard:Nat.card W≤μ:=by
    let f:W→s.selectedFirstSet selector:=fun v=>⟨v.val.val,v.property.1⟩
    have hf:Function.Injective f:=by
      intro u v huv
      exact Subtype.ext (Subtype.ext (congrArg (fun b:s.selectedFirstSet selector=>b.val) huv))
    have hi:Nat.card (s.AdmissibleSampleIndex selector)≤Nat.card ι:=Finite.card_subtype_le _
    have hsel:Nat.card (s.selectedFirstSet selector)≤Nat.card ι:=
      (Finite.card_range_le (s.selectedFirstEmbedding selector)).trans hi
    exact (Nat.card_le_card_of_injective f hf).trans (hsel.trans_eq (Nat.card_congr labels))
  have hcount:(Fintype.card W:ℝ)≤Count*L^(2*a):=by
    have hh:=(Nat.cast_le (α:=ℝ).mpr hWcard).trans (hμ g o z)
    simpa only[Nat.card_eq_fintype_card] using hh
  have hL:0<L:=by dsimp only[L];linarith
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hεcap:ε*L^(4*a)≤1:=
    (le_div_iff₀ (pow_pos hL _)).mp (by simpa only[one_div] using hpaper z hz hfloor)
  have hsmall:(Fintype.card W:ℝ)*L*ε≤1:=
    count_linear_residual_contraction a (by omega) L ε (Fintype.card W) Count hlog hε hCount hcount hεcap hlarge
  have hr:4≤r:=by dsimp only[r,effectiveModelRadius,modelRadiusLoss];omega
  intro loss hloss u v hu hv
  have hloss':loss≤r-2:=by omega
  let t:=physicalTransfer d z^(r-loss-2)
  let F:=A*L*t+D*L*ε
  have ht:0≤t:=pow_nonneg (physicalTransfer_pos d hd z).le _
  have hF:0≤F:=by dsimp only[F];positivity
  have hbound (u0:S)(hu0:(s.fullResample selector).graph.edist x u0.val.val≤(loss:ℕ∞) ∨
        (s.fullResample selector).graph.edist y u0.val.val≤(loss:ℕ∞))(b:W):
      ‖M.extensionGreen q z u0 b.val‖≤F:=by
    let bb:s.partialFirstRemovedSet selector S:=⟨b.val,hW b.property⟩
    have hgeo:(((r-loss-2)+1:ℕ):ℕ∞)≤M.graph.edist u0 b.val:=
      (s.fullRegion_outer_far_of_near selector r loss x y hloss' (by omega) u0.val b.val.val hu0 b.property).trans
        ((ambient_edist_le_induced_edist (s.fullResample selector).graph Tᶜ u0.val b.val.val).trans
          (ambient_edist_le_induced_edist (outsideGraph (s.fullResample selector).graph T) S u0 b.val))
    have hh:=hselectedN.2 u0 bb (r-loss-2) hgeo
    have hAle:sourceRegionalSelectedLeading d β Bcap C1≤A:=
      (le_abs_self _).trans (le_add_of_nonneg_right (by norm_num))
    have hDle:sourceRegionalSelectedError d β Bcap C1≤D:=
      (le_abs_self _).trans (le_add_of_nonneg_right (by norm_num))
    exact hh.trans (add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAle hL.le) ht)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDle hL.le) hε))
  have hx:∀b:W,‖M.extensionGreen q z u.val b.val‖≤F:=hbound u.val hu
  have hy:∀b:W,‖M.extensionGreen q z b.val v.val‖≤F:=by
    intro b
    rw[(M.extensionGreen_isSymm q z).apply v.val b.val]
    exact hbound v.val hv b
  have hdelete:=M.far_deleted_target_difference_any_rows hd W q z hz hq C F F hC hF hF
    _ _ hcaps.2.1 u v hx hy
  have hraw:‖M.extensionGreen q z u.val v.val-(M.delete W).extensionGreen q z u v‖≤
      (Fintype.card W:ℝ)*C*F^2:=hdelete.trans_eq (by ring)
  have htail:t^2≤((Bcap+1)*‖(treeEdgeWeight d)⁻¹‖)^4*physicalTransfer d z^(2*(r-loss)):=by
    have hh:=physical_tail_radius_loss d hd z Bcap hzB (r-loss) 2 (by omega)
    dsimp only[t]
    rw[←pow_mul,Nat.mul_comm (r-loss-2) 2]
    exact hh
  have hn:(Fintype.card W:ℝ)≤(μ:ℝ):=by
    simpa only[Nat.card_eq_fintype_card] using (Nat.cast_le (α:=ℝ).mpr hWcard)
  have hrate:=structured_outer_tail (Fintype.card W) C A D μ L ε t
    (((Bcap+1)*‖(treeEdgeWeight d)⁻¹‖)^4) (physicalTransfer d z^(2*(r-loss)))
    (Nat.cast_nonneg _) hC (Nat.cast_nonneg _) hlog hε (by positivity)
    (pow_nonneg (physicalTransfer_pos d hd z).le _) hn hsmall htail
  exact hraw.trans hrate

end RegularGraph
end LocalLaw
