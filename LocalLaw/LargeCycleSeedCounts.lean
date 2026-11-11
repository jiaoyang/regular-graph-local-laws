import LocalLaw.LargeCycleSeedCover

/-! # Explicit bounded seed counts on the proved full geometric event -/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw

local instance largeCycleSeedCountsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def largeCycleSeedCount (ω k j C t : ℕ) : ℕ :=
  1 + 4 * ((2 * j + C + t) + ((ω + 1 + k) +
    (2 * ω + 2 * j * (ω + 1)) + (j + C)))

namespace LabelledResamplingState
variable {V : Type*} [Fintype V] {T : Set V} {ι : Type*} [Fintype ι]

theorem exceptionalSeedLabels_card (s : LabelledResamplingState V T ι) (R : ℕ) :
    (s.exceptionalSeedLabels R).card = (sampleExceptionalIndices s.graph T R s.samples).card := by
  have himage : (s.exceptionalSeedLabels R).image s.boundary =
      sampleExceptionalIndices s.graph T R s.samples := by
    ext α
    constructor
    · intro hα
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hα
      exact (Finset.mem_filter.mp hi).2
    · intro hα
      refine Finset.mem_image.mpr ⟨s.boundary.symm α, ?_, s.boundary.apply_symm_apply α⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by simpa using hα⟩
  calc
    _ = ((s.exceptionalSeedLabels R).image s.boundary).card :=
      (Finset.card_image_of_injective _ s.boundary.injective).symm
    _ = _ := congrArg Finset.card himage

theorem largeCycleSeeds_card_le (s : LabelledResamplingState V T ι)
    (selector R r : ℕ) (center : V) :
    (s.largeCycleSeeds selector R r center).card ≤
      1 + 4 * ((s.exceptionalSeedLabels R).card + (s.nearbySeedLabels selector r center).card) := by
  have hsupport : ∀ i : ι, (s.quad i).support.toFinset.card ≤ 4 := by
    intro i
    simp only [SwitchingQuad.support, Set.toFinset_insert, Set.toFinset_singleton]
    exact (Finset.card_insert_le _ _).trans (by
      have h₁ := Finset.card_insert_le (s.quad i).b ({(s.quad i).c, (s.quad i).d} : Finset V)
      have h₂ := Finset.card_insert_le (s.quad i).c ({(s.quad i).d} : Finset V)
      simp only [Finset.card_singleton] at h₂
      omega)
  have hbi := Finset.card_biUnion_le (s := s.largeCycleSeedLabels selector R r center)
    (t := fun i => (s.quad i).support.toFinset)
  have hsum : ∑ i ∈ s.largeCycleSeedLabels selector R r center, (s.quad i).support.toFinset.card ≤
      4 * (s.largeCycleSeedLabels selector R r center).card := by
    calc
      _ ≤ ∑ _i ∈ s.largeCycleSeedLabels selector R r center, 4 :=
        Finset.sum_le_sum (fun i _ => hsupport i)
      _ = _ := by simp [Nat.mul_comm]
  have hlabels := Finset.card_union_le (s.exceptionalSeedLabels R) (s.nearbySeedLabels selector r center)
  have hroot := Finset.card_insert_le center ((s.largeCycleSeedLabels selector R r center).biUnion
    (fun i => (s.quad i).support.toFinset))
  change _ ≤ _ at hroot
  unfold largeCycleSeeds
  change (s.largeCycleSeedLabels selector R r center).card ≤ _ at hlabels
  omega

theorem nearbySeedLabels_card_le (s : LabelledResamplingState V T ι)
    (selector R r A B C : ℕ) (hr : r ≤ R) (center : V)
    (hnear : ∀ x : {v : V // v ∉ T}, (tripleNearIndices s.graph T r s.samples x).card ≤ A)
    (hboundary : (boundaryOtherTripleIndices s.graph T r s.samples).card ≤ B)
    (hsampled : (sampledOtherTripleIndices s.graph T R s.samples).card ≤ C) :
    (s.nearbySeedLabels selector r center).card ≤ A + B + C := by
  by_cases hx : center ∉ T
  · rw [nearbySeedLabels, dif_pos hx, labelledTripleNear_card_eq]
    exact (s.fullResample_tripleNear_count selector r R hr ⟨center, hx⟩).trans
      (Nat.add_le_add (Nat.add_le_add (hnear ⟨center, hx⟩) hboundary) hsampled)
  · simp only [nearbySeedLabels, dif_neg hx, Finset.card_empty]
    omega

end LabelledResamplingState

theorem sourceFullGood_largeCycleSeeds_card {V ι : Type*} [Fintype V] [Fintype ι]
    (G : SimpleGraph V) (o : V) (ell selector R ω k j C t : ℕ)
    (boundary : ι ≃ BoundaryOrientedEdge G (graphBallVertices G o ell))
    (S : LocalSamplingFiber G (graphBallVertices G o ell))
    (hgood : SourceFullGeometricGood G o ell R ω k j C t S) (center : V) :
    let s : LabelledResamplingState V (graphBallVertices G o ell) ι := ⟨G, boundary, S⟩
    (s.largeCycleSeeds selector R (R / 2) center).card ≤ largeCycleSeedCount ω k j C t := by
  let s : LabelledResamplingState V (graphBallVertices G o ell) ι := ⟨G, boundary, S⟩
  have hexception := sampleExceptionalIndices_card_of_sourceFullGood G o ell R ω k j C t S hgood
  have hbad : (s.exceptionalSeedLabels R).card ≤ 2 * j + C + t := by
    rw [s.exceptionalSeedLabels_card]
    exact hexception
  have hboundary : (boundaryOtherTripleIndices s.graph (graphBallVertices G o ell) (R / 2) s.samples).card ≤
      2 * ω + 2 * j * (ω + 1) := by
    have h := hgood.1.2.1
    change (boundaryOtherTripleIndices G (graphBallVertices G o ell) (R / 2) S).card ≤ _
    nlinarith
  have hnear := s.nearbySeedLabels_card_le selector R (R / 2)
    (ω + 1 + k) (2 * ω + 2 * j * (ω + 1)) (j + C) (by omega) center
    hgood.1.1 hboundary hgood.1.2.2.1
  exact (s.largeCycleSeeds_card_le selector R (R / 2) center).trans
    (by unfold largeCycleSeedCount; omega)

end LocalLaw
