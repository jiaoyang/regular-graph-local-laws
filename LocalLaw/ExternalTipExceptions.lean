import LocalLaw.ActualGoodExternalComparison
import LocalLaw.ResamplingLargeIsolation

/-! Literal fixed-target exceptions for the good sampled-tip bound. -/
noncomputable section
namespace LocalLaw
local instance externalTipExceptionsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} [Fintype V] {T : Set V} {ι : Type} [Fintype ι]

def newFirstNearLabels (s : LabelledResamplingState V T ι) (selector h : ℕ)
    (x : (Tᶜ : Set V)) : Finset ι :=
  Finset.univ.filter (fun i => (outsideGraph (s.fullResample selector).graph T).edist x
    (s.sampledOutsideFirst i)≤(h:ℕ∞))

/-- The sampled first vertex is unchanged by the full involution, so its
new-near labels are included in the actual new triple-near event. -/
theorem newFirstNearLabels_card (s : LabelledResamplingState V T ι) (selector h : ℕ)
    (x : (Tᶜ : Set V)) :
    (s.newFirstNearLabels selector h x).card≤
      (tripleNearIndices (s.fullResample selector).graph T h (s.fullResample selector).samples x).card := by
  have hsub : s.newFirstNearLabels selector h x⊆(s.fullResample selector).labelledTripleNearIndices h x := by
    intro i hi
    have hd:=(Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,s.sampledOutsideFirst i,?_,?_⟩
    · rw [s.fullResample_triple selector i]
      change s.sampledOutsideFirst i ∈ outsideTriple s.graph T s.samples (s.boundary i)
      rw [outsideTriple_mem_iff]
      exact Or.inr (Or.inl rfl)
    · simpa only [SimpleGraph.edist_comm] using hd
  exact (Finset.card_le_card hsub).trans_eq ((s.fullResample selector).labelledTripleNear_card_eq h x)

/-- Both unchanged first endpoints and detached old tips must be far from
the target. Their union is still counted by one actual triple-near event. -/
def newPairNearLabels (s : LabelledResamplingState V T ι) (selector h : ℕ)
    (x : (Tᶜ : Set V)) : Finset ι :=
  Finset.univ.filter (fun i => (outsideGraph (s.fullResample selector).graph T).edist x
    (s.sampledOutsideFirst i)≤(h:ℕ∞) ∨ (outsideGraph (s.fullResample selector).graph T).edist x
    (s.sampledOutsideSecond i).val≤(h:ℕ∞))

theorem newPairNearLabels_card (s : LabelledResamplingState V T ι) (selector h : ℕ)
    (x : (Tᶜ : Set V)) :
    (s.newPairNearLabels selector h x).card≤
      (tripleNearIndices (s.fullResample selector).graph T h (s.fullResample selector).samples x).card := by
  have hsub : s.newPairNearLabels selector h x⊆(s.fullResample selector).labelledTripleNearIndices h x := by
    intro i hi
    have hd:=(Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases hd with hd | hd
    · refine ⟨s.sampledOutsideFirst i,?_,by simpa only [SimpleGraph.edist_comm] using hd⟩
      rw [s.fullResample_triple selector i]
      change s.sampledOutsideFirst i ∈ outsideTriple s.graph T s.samples (s.boundary i)
      rw [outsideTriple_mem_iff]
      exact Or.inr (Or.inl rfl)
    · refine ⟨(s.sampledOutsideSecond i).val,?_,by simpa only [SimpleGraph.edist_comm] using hd⟩
      rw [s.fullResample_triple selector i]
      change (s.sampledOutsideSecond i).val ∈ outsideTriple s.graph T s.samples (s.boundary i)
      rw [outsideTriple_mem_iff]
      exact Or.inr (Or.inr rfl)
  exact (Finset.card_le_card hsub).trans_eq ((s.fullResample selector).labelledTripleNear_card_eq h x)

end LabelledResamplingState

namespace RegularGraph
variable {N d : ℕ} {T : Set (Fin N)} {ι : Type} [Fintype ι]

def sourceExternalTipExceptions (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι≃BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector correlationRadius h : ℕ) (z : ℂ) (φ : ℝ) (x : (Tᶜ : Set (Fin N))) : Finset ι :=
  (Finset.univ.filter (fun i => boundary i∈g.correlatedSampleIndices T z φ correlationRadius x samples)) ∪
    (g.admissibleState T boundary samples).newPairNearLabels selector h x

theorem sourceExternalTipExceptions_card (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι≃BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector correlationRadius h : ℕ) (z : ℂ) (φ : ℝ) (x : (Tᶜ : Set (Fin N))) :
    (g.sourceExternalTipExceptions T boundary samples selector correlationRadius h z φ x).card≤
      (g.correlatedSampleIndices T z φ correlationRadius x samples).card+
      (tripleNearIndices ((g.admissibleState T boundary samples).fullResample selector).graph T h
        ((g.admissibleState T boundary samples).fullResample selector).samples x).card := by
  let corr := Finset.univ.filter (fun i => boundary i∈g.correlatedSampleIndices T z φ correlationRadius x samples)
  have hc : corr.card≤(g.correlatedSampleIndices T z φ correlationRadius x samples).card := by
    have himage : corr.image boundary⊆g.correlatedSampleIndices T z φ correlationRadius x samples := by
      intro α hα
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hα
      exact (Finset.mem_filter.mp hi).2
    have hcard : (corr.image boundary).card=corr.card := Finset.card_image_of_injective _ boundary.injective
    exact hcard.symm.le.trans (Finset.card_le_card himage)
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add hc
    ((g.admissibleState T boundary samples).newPairNearLabels_card selector h x))

theorem not_mem_sourceExternalTipExceptions (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι≃BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector correlationRadius h r : ℕ) (z : ℂ) (φ : ℝ) (x : (Tᶜ : Set (Fin N)))
    (hr : 2*r+1≤h) (i : ι)
    (hi : i∉g.sourceExternalTipExceptions T boundary samples selector correlationRadius h z φ x) :
    boundary i∉g.correlatedSampleIndices T z φ correlationRadius x samples ∧
      ((2*r+1:ℕ):ℕ∞)<
        (outsideGraph ((g.admissibleState T boundary samples).fullResample selector).graph T).edist
          ((g.admissibleState T boundary samples).sampledOutsideFirst i) x := by
  constructor
  · intro hc
    exact hi (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩))
  · have hn : ¬(outsideGraph ((g.admissibleState T boundary samples).fullResample selector).graph T).edist
        x ((g.admissibleState T boundary samples).sampledOutsideFirst i)≤(h:ℕ∞) := by
      intro hn
      exact hi (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl hn⟩))
    rw [SimpleGraph.edist_comm]
    exact (ENat.coe_le_coe.mpr hr).trans_lt (lt_of_not_ge hn)

/-- The same literal exception event also makes the detached old tip far. -/
theorem not_mem_sourceExternalTipExceptions_tip_far (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι≃BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector correlationRadius h r : ℕ) (z : ℂ) (φ : ℝ) (x : (Tᶜ : Set (Fin N)))
    (hr : 2*r+1≤h) (i : ι)
    (hi : i∉g.sourceExternalTipExceptions T boundary samples selector correlationRadius h z φ x) :
    ((2*r+1:ℕ):ℕ∞)<
      (outsideGraph ((g.admissibleState T boundary samples).fullResample selector).graph T).edist
        ((g.admissibleState T boundary samples).sampledOutsideSecond i).val x := by
  have hn : ¬(outsideGraph ((g.admissibleState T boundary samples).fullResample selector).graph T).edist
      x ((g.admissibleState T boundary samples).sampledOutsideSecond i).val≤(h:ℕ∞) := by
    intro hn
    exact hi (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr hn⟩))
  rw [SimpleGraph.edist_comm]
  exact (ENat.coe_le_coe.mpr hr).trans_lt (lt_of_not_ge hn)

end RegularGraph
end LocalLaw
