import LocalLaw.SourceOmittedRestoredDecay
import LocalLaw.CanonicalOmittedIdentification
import LocalLaw.LeafCoreFarAdapter

/-! # Literal switched local-core decay with every omitted-neighbor charge -/

noncomputable section
set_option maxHeartbeats 1500000
namespace LocalLaw
local instance nativeOmittedDecayDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

theorem native_omitted_core_decay (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))(q z:ℂ)(B C1 A L ε:ℝ)
    (hL:0≤L)(hε:0≤ε)
    (hdecay:g.OmittedRestoredDecayControlled T labels samples selector S q z B C1 A L ε) :
    let s:=g.admissibleState T labels samples
    let Bi:=s.partialFirstRemovedSet selector S
    let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S
    M.LeafCoreDecayBound Bi q z
      (|omittedRestoredSpatialConstant d B A|+|omittedRestoredErrorConstant d B C1 A|+1) L ε := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let Bi:=s.partialFirstRemovedSet selector S
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
  let M:=new.restrict S
  let e:=restrictionDeletionGraphIso new.graph S (s.selectedFirstSet selector) Bi (fun _=>Iff.rfl)
  let canonicalEq:DecidableEq (s.OmittedCore selector S):=fun a b=>Classical.propDecidable (a=b)
  letI:=canonicalEq
  have he:=g.canonical_omitted_restored_Green T labels samples selector S q z
  have hcore:∀x y:(Biᶜ:Set S),∀h:ℕ,(h:ℕ∞)≤(M.delete Bi).graph.edist x y→
      ‖(M.delete Bi).extensionGreen q z x y‖≤
        (|omittedRestoredSpatialConstant d B A|+|omittedRestoredErrorConstant d B C1 A|+1)*L*physicalTransfer d z^h+
        (|omittedRestoredSpatialConstant d B A|+|omittedRestoredErrorConstant d B C1 A|+1)*L*ε := by
    intro x y h hfar
    have hh:=hdecay (e x) (e y) h (by
      have hmetric:=graphIso_edist e x y
      change ((new.delete (s.selectedFirstSet selector)).restrict
        {v:((s.selectedFirstSet selector)ᶜ:Set (Tᶜ:Set (Fin N)))|v.val∈S}).graph.edist (e x) (e y)=
          (M.delete Bi).graph.edist x y at hmetric
      have hc:=g.labelledResampled_delete_selectedFirst_eq T labels samples selector
      change new.delete (s.selectedFirstSet selector)=(g.deficient.delete T).delete (s.selectedFirstSet selector) at hc
      rw[hc] at hmetric
      exact hfar.trans_eq hmetric.symm)
    have hid:=congrArg (fun P=>P x y) he
    change (g.omittedKeptRestoredModel T labels samples selector S).extensionGreen q z (e x) (e y)=
      (M.delete Bi).extensionGreen q z x y at hid
    rw[hid] at hh
    have hS:omittedRestoredSpatialConstant d B A≤
        |omittedRestoredSpatialConstant d B A|+|omittedRestoredErrorConstant d B C1 A|+1:=by
      linarith [le_abs_self (omittedRestoredSpatialConstant d B A),abs_nonneg (omittedRestoredErrorConstant d B C1 A)]
    have hE:omittedRestoredErrorConstant d B C1 A≤
        |omittedRestoredSpatialConstant d B A|+|omittedRestoredErrorConstant d B C1 A|+1:=by
      linarith [le_abs_self (omittedRestoredErrorConstant d B C1 A),abs_nonneg (omittedRestoredSpatialConstant d B A)]
    exact hh.trans (add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hS hL)
        (pow_nonneg (norm_nonneg _) _))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE hL) hε))
  dsimp only [DeficientGraph.LeafCoreDecayBound]
  intro x y h hfar
  have hh:=hcore x y h hfar
  have hEq:=(M.delete Bi).extensionGreen_decidableEq_eq inferInstance
    (fun a b=>Classical.propDecidable (a=b)) q z
  rw[hEq] at hh
  exact hh

end RegularGraph
end LocalLaw
