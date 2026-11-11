import LocalLaw.SourceCorrelationGoodSet
import LocalLaw.EndpointRootOccupancy

/-!
# Actual sampled endpoint error sums from F1 and F2

The near roots are counted by the real triple occupancy, while correlated
sampled roots are counted by the actual independent-sampling event. Every
other sampled term uses the physical correlation bound and model decay.
This theorem concerns sampled endpoints; it makes no assertion about the
unrandomized original boundary endpoints.
-/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sampledErrorColumnsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem finite_exceptional_entry_sum {I : Type} [Fintype I] (f : I→ℂ) (bad : Finset I)
    (δ η : ℝ) (hη : 0≤η) (hcap : ∀ i, ‖f i‖≤δ) (hfar : ∀ i, i∉bad→‖f i‖≤η) :
    (∑ i, ‖f i‖)≤(bad.card:ℝ)*δ+(Fintype.card I:ℝ)*η := by
  have hp (i : I) : ‖f i‖≤(if i∈bad then δ else 0)+η := by
    by_cases hi : i∈bad
    · simpa only [hi,if_true] using (hcap i).trans (le_add_of_nonneg_right hη)
    · simpa only [hi,if_false,zero_add] using hfar i hi
  calc
    _ ≤ ∑ i, ((if i∈bad then δ else 0)+η) := Finset.sum_le_sum (fun i _ => hp i)
    _ = _ := by simp [Finset.sum_add_distrib,←Finset.sum_filter]

namespace RegularGraph
variable {N d : ℕ}

/-- A literal sampled endpoint not counted by F2 is physically small. -/
theorem sampled_endpoint_uncorrelated_norm (g : RegularGraph N d) (T : Set (Fin N))
    (z : ℂ) (φ : ℝ) (radius : ℕ) (S : LocalSamplingFiber g.graph T)
    (x : (Tᶜ : Set (Fin N))) (α : BoundaryOrientedEdge g.graph T)
    (hα : α∉g.correlatedSampleIndices T z φ radius x S) (σ : Bool) :
    ‖(g.deficient.delete T).G z x (g.outsideEdgePoint T (S α) σ)‖<φ := by
  have hnot : ¬g.deletedVertexCorrelation T z φ radius x (g.outsideEdgePoint T (S α) σ) := by
    intro hc
    apply hα
    rw [g.correlatedSampleIndices_eq_related]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    cases σ
    · exact Or.inl hc
    · exact Or.inr hc
  have hh := g.deletedVertexCorrelation_norm_small T z φ radius x (g.outsideEdgePoint T (S α) σ)
    hnot x (g.outsideEdgePoint T (S α) σ) (by simp [closedNeighborFinset]) (by simp [closedNeighborFinset])
  exact hh

/-- Actual F1 and F2 counts give the old sampled model-error column sum.
The uniform comparison and model decay used here are independently proved
by source localization for each concrete restriction. -/
theorem sampled_model_error_sum (g : RegularGraph N d) (T : Set (Fin N))
    (z : ℂ) (φ : ℝ) (radius h k Bnear : ℕ) (S : LocalSamplingFiber g.graph T)
    (x : (Tᶜ : Set (Fin N))) (σ : Bool) (P : Matrix (Tᶜ : Set (Fin N)) (Tᶜ : Set (Fin N)) ℂ)
    (δ C tail : ℝ) (hδ : 0≤δ) (hφ : 0≤φ) (hC : 0≤C) (htail : 0≤tail)
    (hcorr : (g.correlatedSampleIndices T z φ radius x S).card≤k)
    (hnear : (tripleNearIndices g.graph T h S x).card≤Bnear)
    (herror : ∀ α, ‖(g.deficient.delete T).G z x (g.outsideEdgePoint T (S α) σ)-
      P x (g.outsideEdgePoint T (S α) σ)‖≤δ)
    (hfar : ∀ α, ¬(outsideGraph g.graph T).edist x (g.outsideEdgePoint T (S α) σ)≤(h:ℕ∞) →
      ‖P x (g.outsideEdgePoint T (S α) σ)‖≤C*tail) :
    (∑ α, ‖(g.deficient.delete T).G z x (g.outsideEdgePoint T (S α) σ)-
      P x (g.outsideEdgePoint T (S α) σ)‖)≤
      ((k+Bnear:ℕ):ℝ)*δ+(Fintype.card (BoundaryOrientedEdge g.graph T):ℝ)*(φ+C*tail) := by
  let bad := g.correlatedSampleIndices T z φ radius x S ∪ tripleNearIndices g.graph T h S x
  have hbad : bad.card≤k+Bnear := (Finset.card_union_le _ _).trans (Nat.add_le_add hcorr hnear)
  have hh := finite_exceptional_entry_sum
    (fun α => (g.deficient.delete T).G z x (g.outsideEdgePoint T (S α) σ)-P x (g.outsideEdgePoint T (S α) σ))
    bad δ (φ+C*tail) (by positivity) herror (by
      intro α hα
      have hαcorr : α∉g.correlatedSampleIndices T z φ radius x S := fun hc => hα (Finset.mem_union_left _ hc)
      have hαnear : α∉tripleNearIndices g.graph T h S x := fun hn => hα (Finset.mem_union_right _ hn)
      have hdist : ¬(outsideGraph g.graph T).edist x (g.outsideEdgePoint T (S α) σ)≤(h:ℕ∞) := by
        intro hd
        apply hαnear
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,g.outsideEdgePoint T (S α) σ,?_,hd⟩
        rw [outsideTriple_mem_iff]
        cases σ
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      exact (norm_sub_le _ _).trans (add_le_add
        (g.sampled_endpoint_uncorrelated_norm T z φ radius S x α hαcorr σ).le (hfar α hdist)))
  exact hh.trans (add_le_add_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hbad) hδ) _)

end RegularGraph
end LocalLaw
