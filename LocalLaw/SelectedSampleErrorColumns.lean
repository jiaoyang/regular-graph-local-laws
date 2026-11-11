import LocalLaw.SampledErrorColumns

/-! F1/F2 column counting on an arbitrary genuinely selected label subtype. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance selectedSampleErrorColumnsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {J : Type} [Fintype J]

/-- Only selected labels are summed. Selection can depend on the entire
sample; its label map must be injective, and no independence of selection
is assumed. The counting events concern the original independent draws. -/
theorem selected_sampled_model_error_sum (g : RegularGraph N d) (T : Set (Fin N))
    (z : ℂ) (φ : ℝ) (radius h k Bnear : ℕ) (S : LocalSamplingFiber g.graph T)
    (x : (Tᶜ : Set (Fin N))) (σ : Bool) (label : J↪BoundaryOrientedEdge g.graph T)
    (P : J→ℂ) (δ C tail : ℝ) (hδ : 0≤δ) (hφ : 0≤φ) (hC : 0≤C) (htail : 0≤tail)
    (hcorr : (g.correlatedSampleIndices T z φ radius x S).card≤k)
    (hnear : (tripleNearIndices g.graph T h S x).card≤Bnear)
    (herror : ∀ j, ‖(g.deficient.delete T).G z x (g.outsideEdgePoint T (S (label j)) σ)-P j‖≤δ)
    (hfar : ∀ j, ¬(outsideGraph g.graph T).edist x (g.outsideEdgePoint T (S (label j)) σ)≤(h:ℕ∞) →
      ‖P j‖≤C*tail) :
    (∑ j, ‖(g.deficient.delete T).G z x (g.outsideEdgePoint T (S (label j)) σ)-P j‖)≤
      ((k+Bnear:ℕ):ℝ)*δ+(Fintype.card J:ℝ)*(φ+C*tail) := by
  let badAll := g.correlatedSampleIndices T z φ radius x S ∪ tripleNearIndices g.graph T h S x
  let bad : Finset J := Finset.univ.filter (fun j => label j∈badAll)
  have hbad : bad.card≤k+Bnear := by
    let f : {j:J // j∈bad}→{α:BoundaryOrientedEdge g.graph T // α∈badAll} :=
      fun j => ⟨label j.val,(Finset.mem_filter.mp j.property).2⟩
    have hf : Function.Injective f := by
      intro i j hij
      exact Subtype.ext (label.injective (congrArg Subtype.val hij))
    have hh := Nat.card_le_card_of_injective f hf
    have hnat : bad.card≤badAll.card := by simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hh
    exact hnat.trans ((Finset.card_union_le _ _).trans (Nat.add_le_add hcorr hnear))
  have hh := finite_exceptional_entry_sum
    (fun j => (g.deficient.delete T).G z x (g.outsideEdgePoint T (S (label j)) σ)-P j)
    bad δ (φ+C*tail) (by positivity) herror (by
      intro j hj
      have hjnot : label j∉badAll := fun h => hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      have hjcorr : label j∉g.correlatedSampleIndices T z φ radius x S :=
        fun hc => hjnot (Finset.mem_union_left _ hc)
      have hjnear : label j∉tripleNearIndices g.graph T h S x :=
        fun hn => hjnot (Finset.mem_union_right _ hn)
      have hdist : ¬(outsideGraph g.graph T).edist x (g.outsideEdgePoint T (S (label j)) σ)≤(h:ℕ∞) := by
        intro hd
        apply hjnear
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,g.outsideEdgePoint T (S (label j)) σ,?_,hd⟩
        rw [outsideTriple_mem_iff]
        cases σ
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      exact (norm_sub_le _ _).trans (add_le_add
        (g.sampled_endpoint_uncorrelated_norm T z φ radius S x (label j) hjcorr σ).le (hfar j hdist)))
  exact hh.trans (add_le_add_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hbad) hδ) _)

end RegularGraph
end LocalLaw
