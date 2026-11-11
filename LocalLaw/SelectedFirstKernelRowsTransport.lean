import LocalLaw.SelectedFirstKernelCapsTransport

/-! # Endpoint row sums on the literal sampled vertex block -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance selectedFirstKernelRowsTransportDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type} [Fintype V] {T:Set V} {ι:Type} [Fintype ι]

theorem partialFirst_removed_rows_of_endpoint_rows (s:LabelledResamplingState V T ι)
    (selector:ℕ)(S:Set (Tᶜ:Set V))(G:Matrix S S ℂ)(C:ℝ)
    (h:∀i:s.PartialEndpointIndex selector S,∑j:s.PartialEndpointIndex selector S,
      ‖G (s.partialEndpointEmbedding selector S i) (s.partialEndpointEmbedding selector S j)‖≤C) :
    ∀u:s.partialFirstRemovedSet selector S,∑v:s.partialFirstRemovedSet selector S,‖G u.val v.val‖≤C := by
  intro u
  let e:=s.partialFirstRemovalEquiv selector S
  let i:s.PartialEndpointIndex selector S:=.inr (.inl (e.symm u))
  have hi:s.partialEndpointEmbedding selector S i=u.val:=congrArg Subtype.val (e.apply_symm_apply u)
  have he (j:s.partialFirstMask selector S):s.partialEndpointEmbedding selector S (.inr (.inl j))=(e j).val:=rfl
  let f:s.partialFirstMask selector S↪s.PartialEndpointIndex selector S:=
    ⟨fun j=>.inr (.inl j),fun _ _ h=>Sum.inl_injective (Sum.inr_injective h)⟩
  have hB:(∑j:s.partialFirstMask selector S,
      ‖G (s.partialEndpointEmbedding selector S i) (s.partialEndpointEmbedding selector S (f j))‖)≤C:=by
    calc
      _=∑j∈Finset.univ.map f,
          ‖G (s.partialEndpointEmbedding selector S i) (s.partialEndpointEmbedding selector S j)‖:=by
        rw [Finset.sum_map]
      _≤∑j:s.PartialEndpointIndex selector S,
          ‖G (s.partialEndpointEmbedding selector S i) (s.partialEndpointEmbedding selector S j)‖:=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=>norm_nonneg _)
      _≤C:=h i
  have hsum:=e.sum_comp (fun v:s.partialFirstRemovedSet selector S=>‖G u.val v.val‖)
  simp only [←finsum_eq_sum_of_fintype] at hsum hB ⊢
  rw [←hsum]
  simpa only [f,Function.Embedding.coeFn_mk,he,hi] using hB

end LabelledResamplingState
end LocalLaw
