import SpectralConsequences.SampledDoubleMinor
import SpectralConsequences.OutsideObservableMean

/-! # The repeated-index two-sample minor is the actual one-edge cavity entry -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sampledSingletonMinorDecidable (p:Prop):Decidable p:=Classical.propDecidable p

variable {V:Type}
def singletonPairComplementEquiv (b:V) : ((vertexPairSet b b)ᶜ:Set V) ≃ {v:V//v≠b} where
  toFun x:=⟨x.val,fun h=>x.property (Or.inl h)⟩
  invFun x:=⟨x.val,fun h=>h.elim x.property x.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem singletonPair_green_cavity [Fintype V] [DecidableEq V]
    (H:Matrix V V ℂ) (hH:H.IsHermitian) (b:V) (z:ℂ) (hz:0<z.im)
    (x:((vertexPairSet b b)ᶜ:Set V)) :
    green (H.submatrix (Subtype.val:((vertexPairSet b b)ᶜ:Set V)→V)
      (Subtype.val:((vertexPairSet b b)ᶜ:Set V)→V)) z x x =
      matrixCavityTerm (green H z) x.val b := by
  let e:=singletonPairComplementEquiv b
  have hmat:H.submatrix (Subtype.val:((vertexPairSet b b)ᶜ:Set V)→V)
      (Subtype.val:((vertexPairSet b b)ᶜ:Set V)→V)=(deletedMatrix H b).submatrix e e:=by ext u v;rfl
  rw [hmat,green_reindex_equiv]
  dsimp only [Matrix.submatrix_apply]
  rw [green_deleted_vertex H hH z hz b]
  rfl

namespace RegularGraph
variable {N d:ℕ} {T:Set (Fin N)} {ι:Type} [Fintype ι]

theorem sampledDoubleMinor_self (g:LocalLaw.RegularGraph N d)
    (labels:ι≃BoundaryOrientedEdge g.graph T) (S:LocalSamplingFiber g.graph T)
    (selector:ℕ) (z:ℂ) (hz:0<z.im)
    (i:(g.admissibleState T labels S).AdmissibleSampleIndex selector) :
    sampledDoubleMinor g labels S selector z i i=
      fullEdgeCavity g z ⟨(S (labels i.val)).val,(S (labels i.val)).property.1⟩ := by
  let s:=g.admissibleState T labels S
  exact singletonPair_green_cavity g.H (normalizedAdjacency_isHermitian g.graph d)
    (s.admissibleSampleVertex selector i).val z hz
    (LabelledResamplingState.sampledSecondInPairComplement s selector i i i)

end RegularGraph
end SpectralConsequences
