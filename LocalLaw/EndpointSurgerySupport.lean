import LocalLaw.EndpointModelInvariance
import LocalLaw.ActualEndpointAttachments
import LocalLaw.PairedEndpointSurgery

/-!
# Literal endpoint support of the actual outside switching matrix

The actual J-test separates each selected triple from every other triple.
The bulk resampling adjacency formula therefore reduces to its own switch
on every selected endpoint row. No matrix support is assumed.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance endpointSurgerySupportDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*}

private theorem edge_ends_in_exterior (q : SwitchingQuad V) (x y : V)
    (h : (SimpleGraph.edge q.c q.d).Adj x y ∨ (SimpleGraph.edge q.b q.c).Adj x y) :
    x ∈ q.exterior ∧ y ∈ q.exterior := by
  rcases h with h | h
  · rcases (SimpleGraph.edge_adj _ _ _ _).mp h with ⟨h | h,_⟩ <;>
      rcases h with ⟨rfl,rfl⟩ <;> simp [SwitchingQuad.exterior]
  · rcases (SimpleGraph.edge_adj _ _ _ _).mp h with ⟨h | h,_⟩ <;>
      rcases h with ⟨rfl,rfl⟩ <;> simp [SwitchingQuad.exterior]

namespace LabelledResamplingState
variable {T : Set V} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem eligible_triple_index_unique (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i : s.AdmissibleSampleIndex selector) (x : (Tᶜ : Set V))
    (hx : x.val ∈ (s.quad i.val).exterior) (j : ι)
    (hjx : x.val ∈ (s.quad j).exterior) : j = i.val := by
  by_contra hji
  have hne : s.boundary j ≠ s.boundary i.val := fun h => hji (s.boundary.injective h)
  have hdist := i.property.2 (s.boundary j) hne x hx x hjx
  exact (not_lt_of_ge (bot_le : (0 : ℕ∞) ≤ (selector : ℕ∞))) (by simpa only [SimpleGraph.edist_self] using hdist)

/-- On a selected triple row, the full outside update is exactly its own
old-edge removal and new-edge insertion. -/
theorem fullResample_outside_adj_on_triple (s : LabelledResamplingState V T ι)
    (selector : ℕ) (i : s.AdmissibleSampleIndex selector) (x y : (Tᶜ : Set V))
    (hx : x.val ∈ (s.quad i.val).exterior) :
    (outsideGraph (s.fullResample selector).graph T).Adj x y ↔
      ((outsideGraph s.graph T).Adj x y ∧
        ¬(SimpleGraph.edge (s.quad i.val).c (s.quad i.val).d).Adj x.val y.val) ∨
        (SimpleGraph.edge (s.quad i.val).b (s.quad i.val).c).Adj x.val y.val := by
  rw [s.fullResample_outside_adj_iff selector x y]
  have hremoved : (∀ j, s.Eligible selector j →
      ¬(SimpleGraph.edge (s.quad j).c (s.quad j).d).Adj x.val y.val) ↔
      ¬(SimpleGraph.edge (s.quad i.val).c (s.quad i.val).d).Adj x.val y.val := by
    constructor
    · exact fun h => h i.val i.property
    · intro h j _ hrem
      have heq := s.eligible_triple_index_unique selector i x hx j
        (edge_ends_in_exterior _ _ _ (Or.inl hrem)).1
      exact h (heq ▸ hrem)
  have hadded : (∃ j, s.Eligible selector j ∧
      (SimpleGraph.edge (s.quad j).b (s.quad j).c).Adj x.val y.val) ↔
      (SimpleGraph.edge (s.quad i.val).b (s.quad i.val).c).Adj x.val y.val := by
    constructor
    · rintro ⟨j,_,hadd⟩
      have heq := s.eligible_triple_index_unique selector i x hx j
        (edge_ends_in_exterior _ _ _ (Or.inr hadd)).1
      exact heq ▸ hadd
    · exact fun h => ⟨i.val,i.property,h⟩
  exact or_congr (and_congr Iff.rfl hremoved) hadded

theorem fullResample_outside_row_unchanged_away_triple (s : LabelledResamplingState V T ι)
    (selector : ℕ) (i : s.AdmissibleSampleIndex selector) (x y : (Tᶜ : Set V))
    (hx : x.val ∈ (s.quad i.val).exterior) (hy : y.val ∉ (s.quad i.val).exterior) :
    (outsideGraph (s.fullResample selector).graph T).Adj x y ↔ (outsideGraph s.graph T).Adj x y := by
  rw [s.fullResample_outside_adj_on_triple selector i x y hx]
  have hrem : ¬(SimpleGraph.edge (s.quad i.val).c (s.quad i.val).d).Adj x.val y.val :=
    fun h => hy (edge_ends_in_exterior _ _ _ (Or.inl h)).2
  have hadd : ¬(SimpleGraph.edge (s.quad i.val).b (s.quad i.val).c).Adj x.val y.val :=
    fun h => hy (edge_ends_in_exterior _ _ _ (Or.inr h)).2
  simp only [hrem,hadd,not_false_eq_true,and_true,or_false]

/-- The detached endpoint's actual perturbation row touches only its old
sample partner b. -/
theorem fullResample_outside_tip_row_unchanged (s : LabelledResamplingState V T ι)
    (selector : ℕ) (i : s.AdmissibleSampleIndex selector) (y : (Tᶜ : Set V))
    (hy : y ≠ s.admissibleSampleVertex selector i) :
    (outsideGraph (s.fullResample selector).graph T).Adj (s.admissibleSecondVertex selector i) y ↔
      (outsideGraph s.graph T).Adj (s.admissibleSecondVertex selector i) y := by
  let q := s.quad i.val
  have hadm : q.Admissible s.graph := sampledSwitching_admissible s.graph T selector s.samples
    (s.boundary i.val) i.property.1 i.property.2
  have hx : (s.admissibleSecondVertex selector i).val ∈ q.exterior := by
    exact Or.inr (Or.inr rfl)
  rw [s.fullResample_outside_adj_on_triple selector i _ y hx]
  have hyraw : y.val ≠ q.c := fun h => hy (Subtype.ext h)
  have hrem : ¬(SimpleGraph.edge q.c q.d).Adj (s.admissibleSecondVertex selector i).val y.val := by
    change ¬(SimpleGraph.edge q.c q.d).Adj q.d y.val
    intro h
    rcases (SimpleGraph.edge_adj _ _ _ _).mp h with ⟨⟨h₁,_⟩ | ⟨_,h₂⟩,_⟩
    · exact hadm.cd_ne h₁.symm
    · exact hyraw h₂
  have hadd : ¬(SimpleGraph.edge q.b q.c).Adj (s.admissibleSecondVertex selector i).val y.val := by
    change ¬(SimpleGraph.edge q.b q.c).Adj q.d y.val
    intro h
    rcases (SimpleGraph.edge_adj _ _ _ _).mp h with ⟨⟨h₁,_⟩ | ⟨h₁,_⟩,_⟩
    · exact hadm.bd_ne h₁.symm
    · exact hadm.cd_ne h₁.symm
  simp only [show s.quad i.val = q from rfl,hrem,hadd,not_false_eq_true,and_true,or_false]

variable [Fintype V]

omit [Fintype V] in
theorem outside_perturbation_tip_row_zero (s : LabelledResamplingState V T ι)
    (selector d : ℕ) (i : s.AdmissibleSampleIndex selector) (y : (Tᶜ : Set V))
    (hy : y ≠ s.admissibleSampleVertex selector i) :
    (normalizedAdjacency (outsideGraph (s.fullResample selector).graph T) d -
      normalizedAdjacency (outsideGraph s.graph T) d) (s.admissibleSecondVertex selector i) y = 0 := by
  have heq := s.fullResample_outside_tip_row_unchanged selector i y hy
  simp only [normalizedAdjacency,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,SimpleGraph.adjMatrix_apply]
  rw [heq,sub_self]

end LabelledResamplingState
end LocalLaw
