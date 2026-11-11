import LocalLaw.ActualEndpointAttachments

/-! # The actual surgery preserves every core and branch internal graph

Only the bridge between the two sampled branches is removed; only a
core-to-first-branch edge is inserted. These are proved statements about
the actual post graph on the fixed common endpoint vertex set.
-/

noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance endpointInternalGraphsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V I : Type*}

theorem edge_not_inside_set (S : Set V) (a b x y : V)
    (h : a ∉ S ∨ b ∉ S) (hx : x ∈ S) (hy : y ∈ S) :
    ¬(SimpleGraph.edge a b).Adj x y := by
  intro he
  rcases (SimpleGraph.edge_adj _ _ _ _).mp he with ⟨he, _⟩
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h.elim (fun h => h hx) (fun h => h hy)
  · exact h.elim (fun h => h hy) (fun h => h hx)

namespace BranchAttachmentData
variable {old post : SimpleGraph V}

theorem not_mem_B_of_mem_other (D : BranchAttachmentData V I old post) (i j : I) (v : V)
    (hv : v ∈ D.B j ∪ D.C j) (hij : i ≠ j) : v ∉ D.B i := by
  intro hi
  exact Set.disjoint_left.mp (D.family_disjoint i j hij) (Or.inl hi) hv

theorem not_mem_C_of_mem_other (D : BranchAttachmentData V I old post) (i j : I) (v : V)
    (hv : v ∈ D.B j ∪ D.C j) (hij : i ≠ j) : v ∉ D.C i := by
  intro hi
  exact Set.disjoint_left.mp (D.family_disjoint i j hij) (Or.inr hi) hv

theorem core_not_mem_B (D : BranchAttachmentData V I old post) (i : I) (v : V) (hv : v ∈ D.core) :
    v ∉ D.B i := fun h => D.not_core_of_branch i v (Or.inl h) hv

theorem core_not_mem_C (D : BranchAttachmentData V I old post) (i : I) (v : V) (hv : v ∈ D.core) :
    v ∉ D.C i := fun h => D.not_core_of_branch i v (Or.inr h) hv

theorem internal_graph_eq (D : BranchAttachmentData V I old post)
    (hformula : ∀ x y, post.Adj x y ↔
      (old.Adj x y ∧ ∀ i, ¬(SimpleGraph.edge (D.base i) (D.tip i)).Adj x y) ∨
        ∃ i, (SimpleGraph.edge (D.attach i) (D.base i)).Adj x y)
    (S : Set V)
    (hcut : ∀ i, D.base i ∉ S ∨ D.tip i ∉ S)
    (hnew : ∀ i, D.attach i ∉ S ∨ D.base i ∉ S) :
    post.induce S = old.induce S := by
  ext x y
  have hcut' : ∀ i, ¬(SimpleGraph.edge (D.base i) (D.tip i)).Adj x.val y.val :=
    fun i => edge_not_inside_set S _ _ _ _ (hcut i) x.property y.property
  have hnew' : ¬∃ i, (SimpleGraph.edge (D.attach i) (D.base i)).Adj x.val y.val := by
    rintro ⟨i, hi⟩
    exact edge_not_inside_set S _ _ _ _ (hnew i) x.property y.property hi
  change post.Adj x.val y.val ↔ old.Adj x.val y.val
  rw [hformula]
  exact ⟨fun h => h.elim And.left (fun h => False.elim (hnew' h)), fun h => Or.inl ⟨h, hcut'⟩⟩

theorem core_graph_eq (D : BranchAttachmentData V I old post)
    (hf : ∀ x y, post.Adj x y ↔
      (old.Adj x y ∧ ∀ i, ¬(SimpleGraph.edge (D.base i) (D.tip i)).Adj x y) ∨
        ∃ i, (SimpleGraph.edge (D.attach i) (D.base i)).Adj x y) :
    post.induce D.core = old.induce D.core :=
  D.internal_graph_eq hf D.core
    (fun i => Or.inl (D.not_core_of_branch i _ (Or.inl (D.base_mem i))))
    (fun i => Or.inr (D.not_core_of_branch i _ (Or.inl (D.base_mem i))))

theorem B_graph_eq (D : BranchAttachmentData V I old post)
    (hf : ∀ x y, post.Adj x y ↔
      (old.Adj x y ∧ ∀ i, ¬(SimpleGraph.edge (D.base i) (D.tip i)).Adj x y) ∨
        ∃ i, (SimpleGraph.edge (D.attach i) (D.base i)).Adj x y) (i : I) :
    post.induce (D.B i) = old.induce (D.B i) := by
  apply D.internal_graph_eq hf
  · intro j
    by_cases hji : j = i
    · subst j
      exact Or.inr (fun h => Set.disjoint_left.mp (D.branch_disjoint i) h (D.tip_mem i))
    · exact Or.inl (D.not_mem_B_of_mem_other i j _ (Or.inl (D.base_mem j)) (Ne.symm hji))
  · exact fun j => Or.inl (D.core_not_mem_B i _ (D.attach_mem j))

theorem C_graph_eq (D : BranchAttachmentData V I old post)
    (hf : ∀ x y, post.Adj x y ↔
      (old.Adj x y ∧ ∀ i, ¬(SimpleGraph.edge (D.base i) (D.tip i)).Adj x y) ∨
        ∃ i, (SimpleGraph.edge (D.attach i) (D.base i)).Adj x y) (i : I) :
    post.induce (D.C i) = old.induce (D.C i) := by
  apply D.internal_graph_eq hf
  · intro j
    by_cases hji : j = i
    · subst j
      exact Or.inl (fun h => Set.disjoint_left.mp (D.branch_disjoint i) (D.base_mem i) h)
    · exact Or.inl (D.not_mem_C_of_mem_other i j _ (Or.inl (D.base_mem j)) (Ne.symm hji))
  · exact fun j => Or.inl (D.core_not_mem_C i _ (D.attach_mem j))

end BranchAttachmentData

namespace LabelledResamplingState
variable {T : Set V} {ι : Type*} [Fintype ι]

theorem endpoint_exact_adj_iff (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (x y : s.endpointModelVertices selector r) :
    (s.endpointPostGraph selector r).Adj x y ↔
      ((s.endpointOldGraph selector r).Adj x y ∧
        ∀ i : s.AdmissibleSampleIndex selector,
          ¬(SimpleGraph.edge (s.endpointBaseVertex selector r i) (s.endpointTipVertex selector r i)).Adj x y) ∨
      ∃ i : s.AdmissibleSampleIndex selector,
        (SimpleGraph.edge (s.endpointAttachmentVertex selector r i) (s.endpointBaseVertex selector r i)).Adj x y := by
  have he := s.fullResample_outside_adj_iff selector x.val y.val
  have hrem : (∀ i, s.Eligible selector i →
      ¬(SimpleGraph.edge (s.quad i).c (s.quad i).d).Adj x.val.val y.val.val) ↔
      ∀ i : s.AdmissibleSampleIndex selector,
        ¬(SimpleGraph.edge (s.endpointBaseVertex selector r i) (s.endpointTipVertex selector r i)).Adj x y := by
    constructor
    · intro h i hi
      exact h i.val i.property ((edge_subtype_val_iff _ _ _ _).mp ((edge_subtype_val_iff _ _ _ _).mp hi))
    · intro h i hi he
      exact h ⟨i, hi⟩ ((edge_subtype_val_iff _ _ _ _).mpr ((edge_subtype_val_iff _ _ _ _).mpr he))
  have hadd : (∃ i, s.Eligible selector i ∧
      (SimpleGraph.edge (s.quad i).b (s.quad i).c).Adj x.val.val y.val.val) ↔
      ∃ i : s.AdmissibleSampleIndex selector,
        (SimpleGraph.edge (s.endpointAttachmentVertex selector r i) (s.endpointBaseVertex selector r i)).Adj x y := by
    constructor
    · rintro ⟨i, hi, he⟩
      exact ⟨⟨i, hi⟩, (edge_subtype_val_iff _ _ _ _).mpr ((edge_subtype_val_iff _ _ _ _).mpr he)⟩
    · rintro ⟨i, he⟩
      exact ⟨i.val, i.property, (edge_subtype_val_iff _ _ _ _).mp ((edge_subtype_val_iff _ _ _ _).mp he)⟩
  exact he.trans (or_congr (and_congr Iff.rfl hrem) hadd)

theorem endpoint_core_graph_eq (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2 * r + 2 ≤ selector) :
    let D := s.endpointBranchAttachmentData selector r hsep
    (s.endpointPostGraph selector r).induce D.core = (s.endpointOldGraph selector r).induce D.core :=
  (s.endpointBranchAttachmentData selector r hsep).core_graph_eq (s.endpoint_exact_adj_iff selector r)

theorem endpoint_B_graph_eq (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2 * r + 2 ≤ selector) (i : s.AdmissibleSampleIndex selector) :
    let D := s.endpointBranchAttachmentData selector r hsep
    (s.endpointPostGraph selector r).induce (D.B i) = (s.endpointOldGraph selector r).induce (D.B i) :=
  (s.endpointBranchAttachmentData selector r hsep).B_graph_eq (s.endpoint_exact_adj_iff selector r) i

theorem endpoint_C_graph_eq (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2 * r + 2 ≤ selector) (i : s.AdmissibleSampleIndex selector) :
    let D := s.endpointBranchAttachmentData selector r hsep
    (s.endpointPostGraph selector r).induce (D.C i) = (s.endpointOldGraph selector r).induce (D.C i) :=
  (s.endpointBranchAttachmentData selector r hsep).C_graph_eq (s.endpoint_exact_adj_iff selector r) i

end LabelledResamplingState
end LocalLaw
