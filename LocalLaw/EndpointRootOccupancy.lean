import LocalLaw.SourceEndpointMatrices
import LocalLaw.ResamplingGeometricGood

/-! # Literal endpoint-root occupancy from the actual F1 triple count -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance endpointRootOccupancyDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type} [Fintype V]

def outsideTripleVertex (G : SimpleGraph V) (T : Set V) (samples : LocalSamplingFiber G T)
    (α : BoundaryOrientedEdge G T) (k : Fin 3) : (Tᶜ : Set V) :=
  if k = 0 then boundaryOuterEndpoint G T α else
    if k = 1 then sampledFirstOutsideVertex G T samples α else sampledSecondOutsideVertex G T samples α

omit [Fintype V] in
theorem outsideTripleVertex_mem (G : SimpleGraph V) (T : Set V) (samples : LocalSamplingFiber G T)
    (α : BoundaryOrientedEdge G T) (k : Fin 3) : outsideTripleVertex G T samples α k ∈ outsideTriple G T samples α := by
  rw [outsideTriple_mem_iff]
  fin_cases k <;> simp [outsideTripleVertex]

namespace LabelledResamplingState
variable {T : Set V} {ι : Type} [Fintype ι]

omit [Fintype V] [Fintype ι] in
theorem endpointModelRoot_has_triple_vertex (s : LabelledResamplingState V T ι) (selector : ℕ)
    (u : s.endpointModelRoots selector) :
    ∃ p : BoundaryOrientedEdge s.graph T × Fin 3, outsideTripleVertex s.graph T s.samples p.1 p.2 = u.val := by
  rcases u.property with hu | hu
  · obtain ⟨α, hα⟩ := hu
    exact ⟨(α, 0), by simpa only [outsideTripleVertex, if_pos rfl] using hα⟩
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hu
    rcases hi with hi | hi
    · exact ⟨(s.boundary i.val, 1), by simpa [outsideTripleVertex] using hi.symm⟩
    · exact ⟨(s.boundary i.val, 2), by simpa [outsideTripleVertex] using hi.symm⟩

omit [Fintype ι] in
theorem endpointModelRoots_near_card (s : LabelledResamplingState V T ι) (selector h : ℕ)
    (x : (Tᶜ : Set V)) :
    Nat.card {u : s.endpointModelRoots selector // (outsideGraph s.graph T).edist x u.val ≤ (h : ℕ∞)} ≤
      3 * (tripleNearIndices s.graph T h s.samples x).card := by
  let near := tripleNearIndices s.graph T h s.samples x
  let w : s.endpointModelRoots selector → BoundaryOrientedEdge s.graph T × Fin 3 :=
    fun u => Classical.choose (s.endpointModelRoot_has_triple_vertex selector u)
  have hw (u : s.endpointModelRoots selector) : outsideTripleVertex s.graph T s.samples (w u).1 (w u).2 = u.val :=
    Classical.choose_spec (s.endpointModelRoot_has_triple_vertex selector u)
  let A := {u : s.endpointModelRoots selector // (outsideGraph s.graph T).edist x u.val ≤ (h : ℕ∞)}
  let J := {α : BoundaryOrientedEdge s.graph T // α ∈ near} × Fin 3
  have hnear (u : A) : (w u.val).1 ∈ near := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, u.val.val, ?_, u.property⟩
    rw [← hw u.val]
    exact outsideTripleVertex_mem _ _ _ _ _
  let f : A → J := fun u => (⟨(w u.val).1, hnear u⟩, (w u.val).2)
  have hf : Function.Injective f := by
    intro u v huv
    have hα : (w u.val).1 = (w v.val).1 := congrArg (fun p : J => p.1.val) huv
    have hk : (w u.val).2 = (w v.val).2 := congrArg (fun p : J => p.2) huv
    apply Subtype.ext
    apply Subtype.ext
    exact (hw u.val).symm.trans ((congrArg₂ (outsideTripleVertex s.graph T s.samples) hα hk).trans (hw v.val))
  have hcard : Nat.card J = near.card * 3 := by
    simp [J, Nat.card_prod, Nat.card_eq_fintype_card]
  exact (Nat.card_le_card_of_injective f hf).trans_eq (hcard.trans (Nat.mul_comm _ _))

end LabelledResamplingState

/-- A finite kernel row pays a uniform cap for the actual nearby roots and
the decay cap for every remaining root. -/
theorem finite_kernel_near_far_sum {I : Type} [Fintype I] (f : I → ℂ)
    (near : I → Prop) (B C tail : ℝ) (hC : 0 ≤ C) (htail : 0 ≤ tail)
    (hcount : (Nat.card {i : I // near i} : ℝ) ≤ B)
    (hcap : ∀ i, ‖f i‖ ≤ C) (hfar : ∀ i, ¬near i → ‖f i‖ ≤ C * tail) :
    ∑ i, ‖f i‖ ≤ C * B + (Fintype.card I : ℝ) * C * tail := by
  have hp (i : I) : ‖f i‖ ≤ (if near i then C else 0) + C * tail := by
    by_cases hi : near i
    · simp only [hi, if_true]
      exact (hcap i).trans (le_add_of_nonneg_right (mul_nonneg hC htail))
    · simpa only [hi, if_false, zero_add] using hfar i hi
  have hsum : (∑ i, if near i then C else 0) = (Nat.card {i : I // near i} : ℝ) * C := by
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc
    _ ≤ ∑ i, ((if near i then C else 0) + C * tail) := Finset.sum_le_sum (fun i _ => hp i)
    _ = (Nat.card {i : I // near i} : ℝ) * C + (Fintype.card I : ℝ) * (C * tail) := by
      rw [Finset.sum_add_distrib, hsum]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hcount hC]

end LocalLaw
