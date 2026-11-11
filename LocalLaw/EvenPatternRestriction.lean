import LocalLaw.EvenCycleSpaceExact

/-!
# Restricting actual even patterns to their supported vertices

An injective vertex inclusion containing all supported vertices recovers the
entire edge pattern by map-after-comap. Degrees, evenness, and injectivity of
restriction follow. In particular an even pattern supported in a forest is
empty. These are the finite restriction steps for local cyclic-core transfer.
-/

noncomputable section
set_option maxHeartbeats 1000000
namespace LocalLaw

local instance evenPatternRestrictionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V W : Type*} [Fintype V] [Fintype W]

omit [Fintype V] [Fintype W] in
theorem map_comap_eq_of_support_subset (F : SimpleGraph W) (f : V ↪ W)
    (hsupport : F.support ⊆ Set.range f) : (F.comap f).map f = F := by
  apply le_antisymm (SimpleGraph.map_comap_le f F)
  intro x y hxy
  obtain ⟨a, rfl⟩ := hsupport ((F.mem_support).mpr ⟨y, hxy⟩)
  obtain ⟨b, rfl⟩ := hsupport ((F.mem_support).mpr ⟨f a, hxy.symm⟩)
  exact SimpleGraph.map_adj_apply.mpr hxy

theorem comap_even_of_support_subset (F : SimpleGraph W) (f : V ↪ W)
    (hsupport : F.support ⊆ Set.range f) (heven : ∀ w, Even (F.degree w)) :
    ∀ v, Even ((F.comap f).degree v) := by
  intro v
  have h := mappedPattern_degree_image (F.comap f) f v
  have hmap := map_comap_eq_of_support_subset F f hsupport
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h ⊢
  rw [hmap] at h
  rw [← h]
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using heven (f v)

/-- An even pattern whose supported vertices lie in an actual forest must
be empty; no ambient connectivity assumption is needed. -/
theorem even_pattern_eq_bot_of_comap_forest (F : SimpleGraph W) (f : V ↪ W)
    (hsupport : F.support ⊆ Set.range f) (heven : ∀ w, Even (F.degree w))
    (hforest : (F.comap f).IsAcyclic) : F = ⊥ := by
  have hzero := even_forest_eq_bot (F.comap f) hforest (comap_even_of_support_subset F f hsupport heven)
  have hmap := map_comap_eq_of_support_subset F f hsupport
  rw [hzero] at hmap
  have hbot : (⊥ : SimpleGraph V).map f = ⊥ := by
    ext x y
    simp only [SimpleGraph.map_adj, SimpleGraph.bot_adj, false_and, exists_false]
  rw [hbot] at hmap
  exact hmap.symm

/-- A supported even pattern, before an actual vertex restriction. -/
def SupportedEvenSubgraph (G : SimpleGraph W) (S : Set W) :=
  {F : EvenEdgeSubgraph G // F.val.support ⊆ S}

def restrictSupportedEvenSubgraph (G : SimpleGraph W) (f : V ↪ W) :
    SupportedEvenSubgraph G (Set.range f) → EvenEdgeSubgraph (G.comap f) :=
  fun F => ⟨F.val.val.comap f, fun _ _ h => F.val.property.1 h,
    comap_even_of_support_subset F.val.val f F.property F.val.property.2⟩

theorem restrictSupportedEvenSubgraph_injective (G : SimpleGraph W) (f : V ↪ W) :
    Function.Injective (restrictSupportedEvenSubgraph G f) := by
  intro F K h
  have hgraph : F.val.val.comap f = K.val.val.comap f := congrArg Subtype.val h
  have hm := congrArg (fun H : SimpleGraph V => H.map f) hgraph
  dsimp only at hm
  rw [map_comap_eq_of_support_subset F.val.val f F.property,
    map_comap_eq_of_support_subset K.val.val f K.property] at hm
  exact Subtype.ext (Subtype.ext hm)

theorem connected_graphExcess_le_of_even_injection (G : SimpleGraph V) (H : SimpleGraph W)
    (hG : G.Connected) (hH : H.Connected) (f : EvenEdgeSubgraph G → EvenEdgeSubgraph H)
    (hf : Function.Injective f) : graphExcess G ≤ graphExcess H := by
  have hc := Nat.card_le_card_of_injective f hf
  rw [evenEdgeSubgraph_card_eq_excess G hG, evenEdgeSubgraph_card_eq_excess H hH] at hc
  by_contra h
  have hh : graphExcess H < graphExcess G := by omega
  have hpow : 2 ^ graphExcess H < 2 ^ graphExcess G := Nat.pow_lt_pow_right (by decide) hh
  omega

end LocalLaw
