import LocalLaw.CorrelationIsolation

/-!
# A literal isolated-correlation good set

Every good sampled pair is unrelated to all fixed old points and to every
other sampled pair. On the proved isolation event, only O(log² N) labels are
excluded. Further deterministic/geometric good conditions can be intersected
with this set by an ordinary finite union bound.
-/

noncomputable section
namespace LocalLaw
local instance isolatedCorrelationLabelsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {I E X : Type*} [Fintype I] [Fintype E]

def correlationGoodLabels (R : X → X → Prop) (hR : Symmetric R) (first second : E → X)
    (old : I → X) (f : I → E) : Finset I :=
  Finset.univ \ (badSampleIndices (oldPointHitSet R first second old) f ∪
    (sampleCollisionGraph (pairEndpointRelated R first second)
      (pairEndpointRelated_symmetric R hR first second) f).support.toFinset)

/-- The isolated good property is a proved pointwise consequence of membership. -/
theorem correlationGoodLabels_properties (R : X → X → Prop) (hR : Symmetric R)
    (first second : E → X) (old : I → X) (f : I → E) (a : I)
    (ha : a ∈ correlationGoodLabels R hR first second old f) :
    (∀ b, ¬endpointRelated R first second (old b) (f a)) ∧
      (∀ b, b ≠ a → ¬pairEndpointRelated R first second (f a) (f b)) := by
  have hnot := (Finset.mem_sdiff.mp ha).2
  have hold : a ∉ badSampleIndices (oldPointHitSet R first second old) f :=
    fun h => hnot (Finset.mem_union_left _ h)
  have hcollision : a ∉ (sampleCollisionGraph (pairEndpointRelated R first second)
      (pairEndpointRelated_symmetric R hR first second) f).support.toFinset :=
    fun h => hnot (Finset.mem_union_right _ h)
  constructor
  · intro b hab
    apply hold
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ a,
      Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩⟩⟩
  · intro b hba hab
    apply hcollision
    apply Set.mem_toFinset.mpr
    exact (SimpleGraph.mem_support _).mpr ⟨b, hba.symm, hab⟩

/-- The actual isolation event supplies an explicit quadratic count. -/
theorem correlationGoodLabels_bad_card (R : X → X → Prop) (hR : Symmetric R)
    (first second : E → X) (old : I → X) (f : I → E) (k : ℕ)
    (hold : ¬ k ≤ (badSampleIndices (oldPointHitSet R first second old) f).card)
    (hcollision : ¬ 2 * k * (2 * k + 1) ≤
      (sampleCollisionGraph (pairEndpointRelated R first second)
        (pairEndpointRelated_symmetric R hR first second) f).support.toFinset.card) :
    (Finset.univ \ correlationGoodLabels R hR first second old f).card ≤ 4 * k ^ 2 + 3 * k := by
  have heq : Finset.univ \ correlationGoodLabels R hR first second old f =
      badSampleIndices (oldPointHitSet R first second old) f ∪
        (sampleCollisionGraph (pairEndpointRelated R first second)
          (pairEndpointRelated_symmetric R hR first second) f).support.toFinset := by
    ext a
    simp only [correlationGoodLabels, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
  rw [heq]
  apply (Finset.card_union_le _ _).trans
  have h1 : (badSampleIndices (oldPointHitSet R first second old) f).card ≤ k := by omega
  have h2 : (sampleCollisionGraph (pairEndpointRelated R first second)
      (pairEndpointRelated_symmetric R hR first second) f).support.toFinset.card ≤ 2 * k * (2 * k + 1) := by omega
  exact (Nat.add_le_add h1 h2).trans_eq (by ring)

end LocalLaw
