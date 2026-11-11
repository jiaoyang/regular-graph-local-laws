import LocalLaw.OmittedLeafIdentification
import LocalLaw.DeficientGraphInstanceTransport

/-! # Exact actual switched-minor identification with canonical core equality

This only transports the equality decider used by the common-core inverse;
the finite matrices and their true inverses are unchanged.
-/

noncomputable section
set_option maxHeartbeats 2000000
namespace LocalLaw
local instance canonicalOmittedIdentificationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}{ι : Type}[Fintype ι]

theorem canonical_omitted_restored_Green (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))(q z:ℂ) :
    let s:=g.admissibleState T labels samples
    let W:=s.selectedFirstSet selector
    let B:=s.partialFirstRemovedSet selector S
    let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
    let e:=restrictionDeletionGraphIso new.graph S W B (fun _=>Iff.rfl)
    letI:DecidableEq (s.OmittedCore selector S):=fun a b=>Classical.propDecidable (a=b)
    ((g.omittedKeptRestoredModel T labels samples selector S).extensionGreen q z).submatrix e e=
      ((new.restrict S).delete B).extensionGreen q z := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let W:=s.selectedFirstSet selector
  let B:=s.partialFirstRemovedSet selector S
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
  let e:=restrictionDeletionGraphIso new.graph S W B (fun _=>Iff.rfl)
  let M:=g.omittedKeptRestoredModel T labels samples selector S
  let oldEq:DecidableEq (s.OmittedCore selector S):=inferInstance
  let canonicalEq:DecidableEq (s.OmittedCore selector S):=fun a b=>Classical.propDecidable (a=b)
  have hg : (@DeficientGraph.extensionGreen (s.OmittedCore selector S) _ oldEq d M q z).submatrix e e=
      ((new.restrict S).delete B).extensionGreen q z :=
    g.omittedKeptRestoredModel_extensionGreen T labels samples selector S q z
  rw [M.extensionGreen_decidableEq_eq oldEq canonicalEq q z] at hg
  exact hg

end RegularGraph
end LocalLaw
