import LocalLaw.IsolatedCellBudget

/-!
# Actual component root counts from one isolated cell

A genuine component stays in a closed old cell. Its endpoint-index fiber
injects into the fiber in one connected component of that cell. This allows
local central-boundary and two-root tree counts to control a large union.
-/

noncomputable section
namespace LocalLaw
local instance isolatedCellRootsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V I : Type*}

theorem induced_component_subset_of_closed (G : SimpleGraph V) (K S : Set V)
    (hclosed : ∀ u ∈ K, u ∈ S → ∀ v ∈ K, v ∉ S → ¬G.Adj u v)
    (c : (G.induce K).ConnectedComponent) (x : c.supp) (hx : x.val.val ∈ S) :
    ∀ v : c.supp, v.val.val ∈ S := by
  intro v
  obtain ⟨p⟩ := c.connected_induce_supp.preconnected x v
  apply walk_end_mem_isolated (G.induce K) {v : K | v.val ∈ S} ?_
    (p.map (SimpleGraph.Embedding.induce c.supp).toHom) hx
  intro u hu w hw huw
  exact hclosed u.val u.property hu w.val w.property hw huw

variable [Fintype I]

/-- Local roots are counted with their actual global index, so repetitions
are retained and no unproved endpoint-injectivity assumption is required. -/
theorem induced_component_root_card_le_isolated_cell (G : SimpleGraph V) (K S : Set V)
    (center : I → K) (c : (G.induce K).ConnectedComponent)
    (hsub : ∀ v : c.supp, v.val.val ∈ S) (m : ℕ)
    (hcell : ∀ d : (G.induce S).ConnectedComponent,
      Nat.card {i : I // ∃ hi : (center i).val ∈ S, (⟨(center i).val, hi⟩ : S) ∈ d.supp} ≤ m) :
    Nat.card {i : I // center i ∈ c.supp} ≤ m := by
  let a : c.supp := Classical.choice c.connected_induce_supp.nonempty
  let e : ((G.induce K).induce c.supp) →g (G.induce S) :=
    { toFun := fun v => ⟨v.val.val, hsub v⟩
      map_rel' := fun h => h }
  let d := (G.induce S).connectedComponentMk (e a)
  let f : {i : I // center i ∈ c.supp} →
      {i : I // ∃ hi : (center i).val ∈ S, (⟨(center i).val, hi⟩ : S) ∈ d.supp} := fun i => ⟨i.val, by
    let v : c.supp := ⟨center i.val, i.property⟩
    obtain ⟨p⟩ := c.connected_induce_supp.preconnected a v
    exact ⟨hsub v, (SimpleGraph.ConnectedComponent.sound (p.map e).reachable).symm⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hval : i.val = j.val := congrArg
      (fun z : {i : I // ∃ hi : (center i).val ∈ S, (⟨(center i).val, hi⟩ : S) ∈ d.supp} => z.val) hij
    exact Subtype.ext hval
  exact (Nat.card_le_card_of_injective f hf).trans (hcell d)

end LocalLaw
