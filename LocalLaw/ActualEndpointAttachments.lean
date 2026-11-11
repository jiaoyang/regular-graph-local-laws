import LocalLaw.AdmissibleTreeBranches
import LocalLaw.SourceOutsideSwitchFormula
import LocalLaw.PostComponentClassifier

/-! # Actual post-switch branch attachment data

The data here are constructed from the actual I/J-selected samples. In
particular, the post edge cover is proved from the exact full-resampling
adjacency formula; component labels are not input assumptions.
-/

noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance actualEndpointAttachmentsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*}

theorem edge_subtype_val_iff {S : Set V} (a b x y : S) :
    (SimpleGraph.edge a b).Adj x y ↔ (SimpleGraph.edge a.val b.val).Adj x.val y.val := by
  simp [SimpleGraph.edge_adj, Subtype.ext_iff]

namespace LabelledResamplingState
variable {T : Set V} {ι : Type*}

theorem sampledFirstBranch_subset (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (i : s.AdmissibleSampleIndex selector) :
    s.sampledFirstBranch selector r i ⊆ s.sampledEndpointPatch selector r i :=
  inducedTreeBranch_subset _ _ _ _ _

theorem sampledSecondBranch_subset (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (i : s.AdmissibleSampleIndex selector) :
    s.sampledSecondBranch selector r i ⊆ s.sampledEndpointPatch selector r i :=
  inducedTreeBranch_subset _ _ _ _ _

theorem admissibleSampleVertex_mem_firstBranch (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (i : s.AdmissibleSampleIndex selector) :
    s.admissibleSampleVertex selector i ∈ s.sampledFirstBranch selector r i :=
  inducedTreeBranch_root_mem _ _ _ _ _

theorem admissibleSecondVertex_mem_secondBranch (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (i : s.AdmissibleSampleIndex selector) :
    s.admissibleSecondVertex selector i ∈ s.sampledSecondBranch selector r i :=
  inducedTreeBranch_root_mem _ _ _ _ _

theorem endpointModel_mem_patch (s : LabelledResamplingState V T ι) (selector r : ℕ)
    {v : (Tᶜ : Set V)} (hv : v ∈ s.endpointModelVertices selector r) :
    v ∈ s.centralEndpointPatch r ∨ ∃ i, v ∈ s.sampledEndpointPatch selector r i := by
  rcases hv with ⟨u, hu, huv⟩
  rcases hu with hu | hu
  · exact Or.inl ⟨u, hu, huv⟩
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hu
    exact Or.inr ⟨i, u, hi, huv⟩

theorem centralEndpointPatch_subset_model (s : LabelledResamplingState V T ι) (selector r : ℕ) :
    s.centralEndpointPatch r ⊆ s.endpointModelVertices selector r := by
  rintro v ⟨u, hu, huv⟩
  exact ⟨u, Or.inl hu, huv⟩

theorem sampledEndpointPatch_subset_model (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (i : s.AdmissibleSampleIndex selector) :
    s.sampledEndpointPatch selector r i ⊆ s.endpointModelVertices selector r := by
  rintro v ⟨u, hu, huv⟩
  exact ⟨u, Or.inr (Set.mem_iUnion.mpr ⟨i, hu⟩), huv⟩

theorem endpoint_old_edge_cover (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2 * r + 2 ≤ selector) {x y : (Tᶜ : Set V)}
    (hx : x ∈ s.endpointModelVertices selector r) (hy : y ∈ s.endpointModelVertices selector r)
    (hxy : (outsideGraph s.graph T).Adj x y)
    (hremoved : ∀ i, s.Eligible selector i →
      ¬(SimpleGraph.edge (s.quad i).c (s.quad i).d).Adj x.val y.val) :
    (x ∈ s.centralEndpointPatch r ∧ y ∈ s.centralEndpointPatch r) ∨
      (∃ i, x ∈ s.sampledFirstBranch selector r i ∧ y ∈ s.sampledFirstBranch selector r i) ∨
      (∃ i, x ∈ s.sampledSecondBranch selector r i ∧ y ∈ s.sampledSecondBranch selector r i) := by
  have hr : r ≤ selector := by omega
  have hsame {i : s.AdmissibleSampleIndex selector}
      (hxi : x ∈ s.sampledEndpointPatch selector r i) (hyi : y ∈ s.sampledEndpointPatch selector r i) :
      (∃ i, x ∈ s.sampledFirstBranch selector r i ∧ y ∈ s.sampledFirstBranch selector r i) ∨
      (∃ i, x ∈ s.sampledSecondBranch selector r i ∧ y ∈ s.sampledSecondBranch selector r i) := by
    have hxc : x ∈ s.sampledFirstBranch selector r i ∪ s.sampledSecondBranch selector r i := by
      rw [s.sampledBranch_cover selector r hr i]; exact hxi
    have hyc : y ∈ s.sampledFirstBranch selector r i ∪ s.sampledSecondBranch selector r i := by
      rw [s.sampledBranch_cover selector r hr i]; exact hyi
    rcases hxc with hxB | hxC <;> rcases hyc with hyB | hyC
    · exact Or.inl ⟨i, hxB, hyB⟩
    · have hc := (s.sampledBranch_old_cross_iff selector r hr i hxB hyC).mp hxy
      exact False.elim (hremoved i.val i.property ((edge_subtype_val_iff _ _ _ _).mp hc))
    · have hc := (s.sampledBranch_old_cross_iff selector r hr i hyB hxC).mp hxy.symm
      exact False.elim (hremoved i.val i.property ((edge_subtype_val_iff _ _ _ _).mp hc.symm))
    · exact Or.inr ⟨i, hxC, hyC⟩
  rcases s.endpointModel_mem_patch selector r hx with hx0 | ⟨i, hxi⟩
  · rcases s.endpointModel_mem_patch selector r hy with hy0 | ⟨j, hyj⟩
    · exact Or.inl ⟨hx0, hy0⟩
    · exact False.elim ((s.central_sampledEndpointPatch_disjoint_no_edge selector r hsep j).2 x hx0 y hyj hxy)
  · rcases s.endpointModel_mem_patch selector r hy with hy0 | ⟨j, hyj⟩
    · exact False.elim ((s.central_sampledEndpointPatch_disjoint_no_edge selector r hsep i).2 y hy0 x hxi hxy.symm)
    · by_cases hij : i = j
      · subst j; exact Or.inr (hsame hxi hyj)
      · exact False.elim ((s.sampledEndpointPatches_disjoint_no_edge selector r (by omega) i j hij).2
          x hxi y hyj hxy)

def endpointOldGraph (s : LabelledResamplingState V T ι) (selector r : ℕ) :
    SimpleGraph (s.endpointModelVertices selector r) :=
  (outsideGraph s.graph T).induce (s.endpointModelVertices selector r)

variable [Fintype ι]

def endpointPostGraph (s : LabelledResamplingState V T ι) (selector r : ℕ) :
    SimpleGraph (s.endpointModelVertices selector r) :=
  (outsideGraph (s.fullResample selector).graph T).induce (s.endpointModelVertices selector r)

def endpointAttachmentVertex (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (i : s.AdmissibleSampleIndex selector) : s.endpointModelVertices selector r :=
  ⟨boundaryOutsideVertex s.graph T (s.boundary i.val),
    s.centralEndpointPatch_subset_model selector r ⟨_, ⟨s.boundary i.val, rfl⟩, by
      change (outsideGraph s.graph T).edist (boundaryOutsideVertex s.graph T (s.boundary i.val))
        (boundaryOutsideVertex s.graph T (s.boundary i.val)) ≤ (r : ℕ∞)
      simp⟩⟩

def endpointBaseVertex (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (i : s.AdmissibleSampleIndex selector) : s.endpointModelVertices selector r :=
  ⟨s.admissibleSampleVertex selector i,
    s.sampledEndpointPatch_subset_model selector r i (s.sampledPatchFirst selector r i).property⟩

def endpointTipVertex (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (i : s.AdmissibleSampleIndex selector) : s.endpointModelVertices selector r :=
  ⟨s.admissibleSecondVertex selector i,
    s.sampledEndpointPatch_subset_model selector r i (s.sampledPatchSecond selector r i).property⟩

def endpointBranchAttachmentData (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2 * r + 2 ≤ selector) :
    BranchAttachmentData (s.endpointModelVertices selector r) (s.AdmissibleSampleIndex selector)
      (s.endpointOldGraph selector r) (s.endpointPostGraph selector r) where
  core := {x | x.val ∈ s.centralEndpointPatch r}
  B := fun i => {x | x.val ∈ s.sampledFirstBranch selector r i}
  C := fun i => {x | x.val ∈ s.sampledSecondBranch selector r i}
  attach := s.endpointAttachmentVertex selector r
  base := s.endpointBaseVertex selector r
  tip := s.endpointTipVertex selector r
  attach_mem := fun i => ⟨_, ⟨s.boundary i.val, rfl⟩, by
    change (outsideGraph s.graph T).edist (boundaryOutsideVertex s.graph T (s.boundary i.val))
      (boundaryOutsideVertex s.graph T (s.boundary i.val)) ≤ (r : ℕ∞)
    simp⟩
  base_mem := s.admissibleSampleVertex_mem_firstBranch selector r
  tip_mem := s.admissibleSecondVertex_mem_secondBranch selector r
  core_disjoint := by
    intro i
    apply Set.disjoint_left.mpr
    intro x hx0 hx
    exact Set.disjoint_left.mp (s.central_sampledEndpointPatch_disjoint_no_edge selector r hsep i).1
      hx0 (hx.elim (fun h => s.sampledFirstBranch_subset selector r i h)
        (fun h => s.sampledSecondBranch_subset selector r i h))
  branch_disjoint := by
    intro i
    exact Set.disjoint_left.mpr (fun _ hx hy => Set.disjoint_left.mp
      (s.sampledBranch_disjoint selector r (by omega) i) hx hy)
  family_disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    exact Set.disjoint_left.mp (s.sampledEndpointPatches_disjoint_no_edge selector r (by omega) i j hij).1
      (hi.elim (fun h => s.sampledFirstBranch_subset selector r i h)
        (fun h => s.sampledSecondBranch_subset selector r i h))
      (hj.elim (fun h => s.sampledFirstBranch_subset selector r j h)
        (fun h => s.sampledSecondBranch_subset selector r j h))
  cover := by
    intro x hx
    rcases s.endpointModel_mem_patch selector r x.property with h0 | ⟨i, hi⟩
    · exact False.elim (hx h0)
    · refine ⟨i, ?_⟩
      change x.val ∈ s.sampledFirstBranch selector r i ∪ s.sampledSecondBranch selector r i
      rw [s.sampledBranch_cover selector r (by omega) i]
      exact hi
  attach_edge := by
    intro i
    apply (s.fullResample_outside_adj_iff selector _ _).mpr
    apply Or.inr
    refine ⟨i.val, i.property, ?_⟩
    apply (SimpleGraph.edge_adj _ _ _ _).mpr
    exact ⟨Or.inl ⟨rfl, rfl⟩, fun h => i.property.1.distinct (Subtype.ext h)⟩
  edge_cover := by
    intro x y hxy
    rcases (s.fullResample_outside_adj_iff selector x.val y.val).mp hxy with ⟨hold, hrem⟩ | ⟨j, hj, hadd⟩
    · rcases s.endpoint_old_edge_cover selector r hsep x.property y.property hold hrem with
        ⟨hx, hy⟩ | ⟨i, hx, hy⟩ | ⟨i, hx, hy⟩
      · exact Or.inl ⟨hx, hy, hold⟩
      · exact Or.inr (Or.inl ⟨i, hx, hy⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨i, hx, hy⟩))
    · apply Or.inr; apply Or.inr; apply Or.inr
      refine ⟨⟨j, hj⟩, ?_⟩
      rcases (SimpleGraph.edge_adj _ _ _ _).mp hadd with ⟨h | h, _⟩
      · exact Or.inl ⟨Subtype.ext (Subtype.ext h.1), Subtype.ext (Subtype.ext h.2)⟩
      · exact Or.inr ⟨Subtype.ext (Subtype.ext h.2), Subtype.ext (Subtype.ext h.1)⟩

end LabelledResamplingState
end LocalLaw
