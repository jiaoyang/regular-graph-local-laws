import LocalLaw.RestrictedCommonLocalModel
import LocalLaw.DeficientGraphInstanceTransport

/-! # Canonical inverse reindexing for the correctly charged local common core -/

noncomputable section
set_option maxHeartbeats 2500000
namespace LocalLaw
local instance canonicalRestrictedCommonLocalDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

omit [Fintype ι] in
theorem canonical_restricted_common_local_Green (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(A S:Set (Tᶜ:Set (Fin N)))
    (hA:(g.admissibleState T labels samples).selectedFirstSet selector⊆A)(hSA:S⊆A)(q z:ℂ) :
    let s:=g.admissibleState T labels samples
    let M:=(g.deficient.delete T).restrict A
    let B:=s.partialFirstRemovedSet selector A
    let K:Set (Bᶜ:Set A):={u | u.val.val∈S}
    let e:=s.selectedCommonLocalEquiv selector A S hSA
    letI:DecidableEq (Bᶜ:Set A):=fun a b=>Classical.propDecidable (a=b)
    letI:DecidableEq (s.OmittedCore selector S):=fun a b=>Classical.propDecidable (a=b)
    ((g.omittedCommonModel T labels samples selector S).extensionGreen q z).submatrix e e=
      ((M.delete B).restrict K).extensionGreen q z := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let W:=s.selectedFirstSet selector
  let old:=g.deficient.delete T
  let M:=old.restrict A
  let B:=s.partialFirstRemovedSet selector A
  let K:Set (Bᶜ:Set A):={u | u.val.val∈S}
  letI:DecidableEq (Bᶜ:Set A):=fun a b=>Classical.propDecidable (a=b)
  letI:DecidableEq (s.OmittedCore selector S):=fun a b=>Classical.propDecidable (a=b)
  let e:((M.delete B).restrict K).graph ≃g (g.omittedCommonModel T labels samples selector S).graph:=
    {toEquiv:=s.selectedCommonLocalEquiv selector A S hSA
     map_rel_iff':=Iff.rfl}
  have hδ:∀v,((M.delete B).restrict K).deficit v=
      (g.omittedCommonModel T labels samples selector S).deficit (e v):=by
    intro v
    exact old.restrictionDeletion_deficit A W B (fun _=>Iff.rfl) hA v.val
  exact (g.omittedCommonModel T labels samples selector S).extensionGreen_iso
    ((M.delete B).restrict K) e hδ q z

end RegularGraph
end LocalLaw
