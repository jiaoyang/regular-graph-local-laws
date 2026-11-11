import SpectralConsequences.SelectedTipCrossCaps
import SpectralConsequences.PhysicalTwoPivotExpansion

/-! # The literal original two-sampled-first-vertex minor

The retained targets are the two sampled second endpoints. Eligibility
proves that neither target is one of the deleted first endpoints.
-/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sampledDoubleMinorDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def vertexPairSet {V:Type} (x y:V) : Set V := {v | v=x ∨ v=y}

def vertexPairEquiv {V:Type} (x y:V) (hxy:x≠y) : Fin 2 ≃ vertexPairSet x y where
  toFun i := if i=0 then ⟨x,Or.inl rfl⟩ else ⟨y,Or.inr rfl⟩
  invFun v := if v.val=x then 0 else 1
  left_inv i := by fin_cases i <;> simp [hxy,Ne.symm hxy]
  right_inv v := by
    apply Subtype.ext
    rcases v.property with hv | hv
    · simp [hv]
    · simp [hv,hxy,Ne.symm hxy]

@[simp] theorem vertexPairEquiv_zero {V:Type} (x y:V) (hxy:x≠y) :
    (vertexPairEquiv x y hxy 0).val=x := by simp [vertexPairEquiv]
@[simp] theorem vertexPairEquiv_one {V:Type} (x y:V) (hxy:x≠y) :
    (vertexPairEquiv x y hxy 1).val=y := by simp [vertexPairEquiv]

namespace LabelledResamplingState
variable {V:Type} {T:Set V} {ι:Type} [Fintype ι]

def sampledPairRemoved (s:LabelledResamplingState V T ι) (selector:ℕ)
    (i j:s.AdmissibleSampleIndex selector) : Set V :=
  vertexPairSet (s.admissibleSampleVertex selector i).val (s.admissibleSampleVertex selector j).val

def sampledPairEquiv (s:LabelledResamplingState V T ι) (selector:ℕ)
    (i j:s.AdmissibleSampleIndex selector) (hij:i≠j) : Fin 2 ≃ LabelledResamplingState.sampledPairRemoved s selector i j :=
  vertexPairEquiv _ _ (fun h => hij
    (s.admissibleSampleVertex_injective selector (Subtype.ext h)))

def sampledSecondInPairComplement (s:LabelledResamplingState V T ι) (selector:ℕ)
    (i j k:s.AdmissibleSampleIndex selector) : ((LabelledResamplingState.sampledPairRemoved s selector i j)ᶜ:Set V) :=
  ⟨(s.admissibleSecondVertex selector k).val,by
    intro h
    rcases h with h | h
    · exact selected_first_ne_second s selector k i (Subtype.ext h.symm)
    · exact selected_first_ne_second s selector k j (Subtype.ext h.symm)⟩

end LabelledResamplingState

namespace RegularGraph
variable {N d:ℕ} {T:Set (Fin N)} {ι:Type} [Fintype ι]

/-- Genuine original full-graph minor after deleting the two first samples. -/
def sampledDoubleMinor (g:LocalLaw.RegularGraph N d)
    (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector:ℕ) (z:ℂ)
    (i j:(g.admissibleState T labels samples).AdmissibleSampleIndex selector) : ℂ :=
  let s:=g.admissibleState T labels samples
  let S:=LabelledResamplingState.sampledPairRemoved s selector i j
  green (g.H.submatrix (Subtype.val:((Sᶜ:Set (Fin N)))→Fin N)
    (Subtype.val:((Sᶜ:Set (Fin N)))→Fin N)) z
    (LabelledResamplingState.sampledSecondInPairComplement s selector i j i)
    (LabelledResamplingState.sampledSecondInPairComplement s selector i j j)

end RegularGraph
end SpectralConsequences
