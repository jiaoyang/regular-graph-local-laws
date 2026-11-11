import LocalLaw.EndpointBranchTrees
import LocalLaw.SourceDeficitRestoration
import LocalLaw.AdmissibleEndpointModel

/-! # Exact inherited deficits on the actual post-switch branches

Every attached b-branch has zero inherited deficit. Every detached c-branch
has precisely one deficit unit, at its actual sampled tip. These statements
follow from the exact boundary-label conservation and I/J geometry.
-/

noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance endpointBranchDeficitsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type*} {T : Set V} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem admissibleSecondVertex_injective (s : LabelledResamplingState V T ι) (selector : ℕ) :
    Function.Injective (s.admissibleSecondVertex selector) := by
  intro i j heq
  by_contra hij
  have hlabel : s.boundary j.val ≠ s.boundary i.val := fun h => hij (Subtype.ext (s.boundary.injective h).symm)
  have hfar := i.property.2 (s.boundary j.val) hlabel
    (s.admissibleSecondVertex selector i)
    ((outsideTriple_mem_iff s.graph T s.samples _ _).mpr (Or.inr (Or.inr rfl)))
    (s.admissibleSecondVertex selector j)
    ((outsideTriple_mem_iff s.graph T s.samples _ _).mpr (Or.inr (Or.inr rfl)))
  rw [heq, SimpleGraph.edist_self] at hfar
  exact not_lt_of_ge (bot_le : (0 : ℕ∞) ≤ selector) hfar

theorem restoredBoundaryLabels_zero_off_central (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (v : (Tᶜ : Set V)) (hv : v ∉ s.centralEndpointPatch r) :
    s.restoredBoundaryLabels selector v = 0 := by
  letI : IsEmpty {i : ι // s.Eligible selector i ∧ (s.boundary i).val.2 = v.val} := ⟨fun i => by
    apply hv
    have he : boundaryOutsideVertex s.graph T (s.boundary i.val) = v := Subtype.ext i.property.2
    exact ⟨_, ⟨s.boundary i.val, rfl⟩, by
      change (outsideGraph s.graph T).edist (boundaryOutsideVertex s.graph T (s.boundary i.val)) v ≤ (r : ℕ∞)
      rw [he, SimpleGraph.edist_self]
      exact bot_le⟩⟩
  exact Nat.card_of_isEmpty

theorem detachedBoundaryLabels_one_at_tip (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i : s.AdmissibleSampleIndex selector) :
    s.detachedBoundaryLabels selector (s.admissibleSecondVertex selector i) = 1 := by
  let canonical : {j : ι // s.Eligible selector j ∧
      (s.samples (s.boundary j)).val.2 = (s.admissibleSecondVertex selector i).val} :=
    ⟨i.val, i.property, rfl⟩
  letI : Unique {j : ι // s.Eligible selector j ∧
      (s.samples (s.boundary j)).val.2 = (s.admissibleSecondVertex selector i).val} :=
    ⟨⟨canonical⟩, fun j => by
      apply Subtype.ext
      have he : s.admissibleSecondVertex selector (⟨j.val, j.property.1⟩ : s.AdmissibleSampleIndex selector) =
          s.admissibleSecondVertex selector i := Subtype.ext j.property.2
      change j.val = i.val
      exact congrArg (fun k : s.AdmissibleSampleIndex selector => k.val)
        (s.admissibleSecondVertex_injective selector he)⟩
  exact Nat.card_unique

theorem detachedBoundaryLabels_zero_on_central (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2 * r + 2 ≤ selector) (v : (Tᶜ : Set V)) (hv : v ∈ s.centralEndpointPatch r) :
    s.detachedBoundaryLabels selector v = 0 := by
  apply s.detachedBoundaryLabels_eq_zero
  intro j hj he
  let i : s.AdmissibleSampleIndex selector := ⟨j, hj⟩
  have htip : s.admissibleSecondVertex selector i ∈ s.sampledEndpointPatch selector r i :=
    (s.sampledPatchSecond selector r i).property
  have he' : s.admissibleSecondVertex selector i = v := Subtype.ext he
  exact Set.disjoint_left.mp (s.central_sampledEndpointPatch_disjoint_no_edge selector r hsep i).1
    hv (he' ▸ htip)

theorem detachedBoundaryLabels_zero_on_B (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2 * r + 2 ≤ selector) (i : s.AdmissibleSampleIndex selector)
    (v : (Tᶜ : Set V)) (hv : v ∈ s.sampledFirstBranch selector r i) :
    s.detachedBoundaryLabels selector v = 0 := by
  apply s.detachedBoundaryLabels_eq_zero
  intro j hj he
  let j' : s.AdmissibleSampleIndex selector := ⟨j, hj⟩
  have htip := s.admissibleSecondVertex_mem_secondBranch selector r j'
  have he' : s.admissibleSecondVertex selector j' = v := Subtype.ext he
  by_cases hji : j' = i
  · have he'' : s.admissibleSecondVertex selector i = v := by simpa only [hji] using he'
    have hvc : v ∈ s.sampledSecondBranch selector r i :=
      he'' ▸ s.admissibleSecondVertex_mem_secondBranch selector r i
    exact Set.disjoint_left.mp (s.sampledBranch_disjoint selector r (by omega) i) hv hvc
  · exact Set.disjoint_left.mp (s.sampledEndpointPatches_disjoint_no_edge selector r (by omega) i j'
      (Ne.symm hji)).1 (s.sampledFirstBranch_subset selector r i hv)
      (he' ▸ s.sampledSecondBranch_subset selector r j' htip)

theorem detachedBoundaryLabels_on_C (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2 * r + 2 ≤ selector) (i : s.AdmissibleSampleIndex selector)
    (v : (Tᶜ : Set V)) (hv : v ∈ s.sampledSecondBranch selector r i) :
    s.detachedBoundaryLabels selector v = if v = s.admissibleSecondVertex selector i then 1 else 0 := by
  by_cases hvi : v = s.admissibleSecondVertex selector i
  · rw [if_pos hvi, hvi]
    exact s.detachedBoundaryLabels_one_at_tip selector i
  · rw [if_neg hvi]
    apply s.detachedBoundaryLabels_eq_zero
    intro j hj he
    let j' : s.AdmissibleSampleIndex selector := ⟨j, hj⟩
    have he' : s.admissibleSecondVertex selector j' = v := Subtype.ext he
    by_cases hji : j' = i
    · exact hvi ((congrArg (s.admissibleSecondVertex selector) hji).symm.trans he').symm
    · exact Set.disjoint_left.mp (s.sampledEndpointPatches_disjoint_no_edge selector r (by omega) i j'
        (Ne.symm hji)).1 (s.sampledSecondBranch_subset selector r i hv)
        (he' ▸ (s.sampledPatchSecond selector r j').property)

end LabelledResamplingState

namespace RegularGraph
variable {N d : ℕ} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem sampledEndpointPatch_zero_deficit (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hmargin : r + 1 ≤ selector)
    (i : (g.admissibleState T boundary S).AdmissibleSampleIndex selector)
    (v : (Tᶜ : Set (Fin N))) (hv : v ∈ (g.admissibleState T boundary S).sampledEndpointPatch selector r i) :
    (g.deficient.delete T).deficit v = 0 := by
  let s := g.admissibleState T boundary S
  have hpair : v ∈ pairBallVertices (outsideGraph g.graph T)
      (s.admissibleSampleVertex selector i) (s.admissibleSecondVertex selector i) r := by
    change v ∈ pairBallVertices (outsideGraph s.graph T)
      (s.admissibleSampleVertex selector i) (s.admissibleSecondVertex selector i) r
    rw [← s.sampledEndpointPatch_eq_pairBall selector r i]
    exact hv
  have hd := pairBall_subset_succ_of_eq_or_adjacent (outsideGraph g.graph T)
    (s.admissibleSampleVertex selector i) (s.admissibleSecondVertex selector i) r
    (Or.inr (show (outsideGraph g.graph T).Adj _ _ from (S (boundary i.val)).property.1)) hpair
  exact g.boundaryFarOutside_zero_deficit T selector _ (s.admissibleSampleVertex_far_boundary selector i)
    v (hd.trans (ENat.coe_le_coe.mpr hmargin))

theorem endpoint_B_zero_deficit (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector)
    (i : (g.admissibleState T boundary S).AdmissibleSampleIndex selector)
    (v : (Tᶜ : Set (Fin N))) (hv : v ∈ (g.admissibleState T boundary S).sampledFirstBranch selector r i) :
    ((g.labelledResampledGraph T boundary S selector).deficient.delete T).deficit v = 0 := by
  let s := g.admissibleState T boundary S
  have hold := g.sampledEndpointPatch_zero_deficit T boundary S selector r (by omega) i v
    (s.sampledFirstBranch_subset selector r i hv)
  have hoff : v ∉ s.centralEndpointPatch r := fun hc =>
    Set.disjoint_left.mp (s.central_sampledEndpointPatch_disjoint_no_edge selector r hsep i).1 hc
      (s.sampledFirstBranch_subset selector r i hv)
  have hr := s.restoredBoundaryLabels_zero_off_central selector r v hoff
  have ht := s.detachedBoundaryLabels_zero_on_B selector r hsep i v hv
  have h := g.labelledResampled_deleted_deficit_conservation T boundary S selector v
  dsimp only at h
  change _ + s.restoredBoundaryLabels selector v = _ + s.detachedBoundaryLabels selector v at h
  rw [hr, ht, hold] at h
  simpa only [add_zero, zero_add] using h

theorem endpoint_C_one_root_deficit (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector)
    (i : (g.admissibleState T boundary S).AdmissibleSampleIndex selector)
    (v : (Tᶜ : Set (Fin N))) (hv : v ∈ (g.admissibleState T boundary S).sampledSecondBranch selector r i) :
    ((g.labelledResampledGraph T boundary S selector).deficient.delete T).deficit v =
      if v = (g.admissibleState T boundary S).admissibleSecondVertex selector i then 1 else 0 := by
  let s := g.admissibleState T boundary S
  have hold := g.sampledEndpointPatch_zero_deficit T boundary S selector r (by omega) i v
    (s.sampledSecondBranch_subset selector r i hv)
  have hoff : v ∉ s.centralEndpointPatch r := fun hc =>
    Set.disjoint_left.mp (s.central_sampledEndpointPatch_disjoint_no_edge selector r hsep i).1 hc
      (s.sampledSecondBranch_subset selector r i hv)
  have hr := s.restoredBoundaryLabels_zero_off_central selector r v hoff
  have ht := s.detachedBoundaryLabels_on_C selector r hsep i v hv
  have h := g.labelledResampled_deleted_deficit_conservation T boundary S selector v
  dsimp only at h
  change _ + s.restoredBoundaryLabels selector v = _ + s.detachedBoundaryLabels selector v at h
  rw [hr, ht, hold] at h
  by_cases hv : v = (g.admissibleState T boundary S).admissibleSecondVertex selector i
  · rw [if_pos hv]
    have hv' : v = s.admissibleSecondVertex selector i := hv
    simpa only [if_pos hv', add_zero, zero_add] using h
  · rw [if_neg hv]
    have hv' : v ≠ s.admissibleSecondVertex selector i := hv
    simpa only [if_neg hv', add_zero, zero_add] using h

end RegularGraph
end LocalLaw
