import LocalLaw.EndpointComponentCounts
import LocalLaw.SourceMinorCorrelations

/-! # Actual old endpoint rows outside an isolated sampled pair -/

noncomputable section
namespace LocalLaw
local instance sourceEndpointCorrelationsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type*} {T : Set V} {ι : Type*} [Fintype ι]

def endpointPairFinset (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i : s.AdmissibleSampleIndex selector) : Finset (s.endpointModelRoots selector) :=
  {s.endpointRootLabel selector (Sum.inr (i,0)),s.endpointRootLabel selector (Sum.inr (i,1))}

omit [Fintype ι] in
theorem endpointPairFinset_card (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i : s.AdmissibleSampleIndex selector) : (s.endpointPairFinset selector i).card ≤ 2 :=
  (Finset.card_insert_le _ _).trans (by simp)

omit [Fintype ι] in
theorem mem_endpointPairFinset_iff (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i : s.AdmissibleSampleIndex selector) (v : s.endpointModelRoots selector) :
    v ∈ s.endpointPairFinset selector i ↔ v.val ∈ s.admissiblePairRoots selector i := by
  simp only [endpointPairFinset,Finset.mem_insert,Finset.mem_singleton,
    admissiblePairRoots,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

end LabelledResamplingState

namespace RegularGraph
variable {N d : ℕ} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- Literal source isolation controls every old endpoint row outside its own
sample pair, including its own old boundary root. -/
theorem source_good_endpoint_pair_row (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector radius : ℕ) (z : ℂ) (φ : ℝ)
    (i : (g.admissibleState T labels S).AdmissibleSampleIndex selector)
    (hi : labels i.val ∈ g.sourceCorrelationGoodLabels T z φ radius S)
    (u v : (g.admissibleState T labels S).endpointModelRoots selector)
    (hu : u ∈ (g.admissibleState T labels S).endpointPairFinset selector i)
    (hv : v ∉ (g.admissibleState T labels S).endpointPairFinset selector i) :
    ‖green (normalizedAdjacency (outsideGraph g.graph T) d) z u.val v.val‖ ≤ φ := by
  let s := g.admissibleState T labels S
  let H := outsideGraph g.graph T
  have hself (v : (Tᶜ : Set (Fin N))) : v ∈ closedNeighborFinset H v := by simp [closedNeighborFinset]
  have hsymm : (green (normalizedAdjacency H d) z).IsSymm := by
    have hh := (g.deficient.delete T).extensionGreen_isSymm (0 : ℂ) z
    simpa only [DeficientGraph.extensionGreen,DeficientGraph.H,boundaryGreen,boundaryMatrix,
      zero_smul,sub_zero,green] using hh
  have hu' := (s.mem_endpointPairFinset_iff selector i u).mp hu
  have hv' : v.val ∉ s.admissiblePairRoots selector i :=
    fun h => hv ((s.mem_endpointPairFinset_iff selector i v).mpr h)
  have hrow (σ : Bool) (huσ : u.val = g.outsideEdgePoint T (S (labels i.val)) σ) :
      ‖green (normalizedAdjacency H d) z u.val v.val‖ ≤ φ := by
    rw [huσ]
    rcases v.property with ⟨a,ha⟩ | hvv
    · have hvEq : v.val = boundaryOutsideVertex g.graph T a := ha.symm
      rw [hvEq,hsymm.apply]
      exact (g.sourceCorrelationGood_old_norm_small T z φ radius S (labels i.val) hi a σ
        (boundaryOutsideVertex g.graph T a) (g.outsideEdgePoint T (S (labels i.val)) σ)
          (hself _) (hself _)).le
    · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hvv
      have hji : j.val ≠ i.val := by
        intro h
        have heq : j = i := Subtype.ext h
        exact hv' (heq ▸ hj)
      apply g.source_good_other_exterior_norm_small T labels S z φ radius i.val hi v.val
        ⟨j.val,hji,?_⟩ σ
      exact s.admissiblePairRoots_subset_triple selector j hj
  rcases hu' with hu' | hu'
  · exact hrow false hu'
  · exact hrow true hu'

end RegularGraph
end LocalLaw
