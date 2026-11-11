import LocalLaw.PairBallGeometry
import LocalLaw.ComponentBallGeometry

/-!
# Contact geometry for an old set augmented by two hubs

Distinct old induced components have no edges between them. Consequently
any connection between the two hubs either is direct or passes through one
old component touching both. No separation between either hub and the old
set is assumed.
-/

noncomputable section
namespace LocalLaw
local instance twoHubContactDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type}

def liftedComponent (G : SimpleGraph V) (K : Set V) (c : (G.induce K).ConnectedComponent) : Set V :=
  {v | ∃ hv : v ∈ K, (⟨v, hv⟩ : K) ∈ c.supp}

theorem liftedComponent_mem (G : SimpleGraph V) (K : Set V) (c : (G.induce K).ConnectedComponent)
    (v : K) : v.val ∈ liftedComponent G K c ↔ v ∈ c.supp := by
  constructor
  · rintro ⟨_, h⟩; exact h
  · exact fun h => ⟨v.property, h⟩

theorem liftedComponent_adj_closed (G : SimpleGraph V) (K : Set V) (c : (G.induce K).ConnectedComponent)
    {u v : V} (hu : u ∈ liftedComponent G K c) (hv : v ∈ K) (huv : G.Adj u v) :
    v ∈ liftedComponent G K c := by
  obtain ⟨huK, hcu⟩ := hu
  exact ⟨hv, (c.mem_supp_congr_adj (show (G.induce K).Adj ⟨u, huK⟩ ⟨v, hv⟩ from huv)).mp hcu⟩

def setsContact (G : SimpleGraph V) (A B : Set V) : Prop :=
  ∃ u ∈ A, ∃ v ∈ B, u = v ∨ G.Adj u v

theorem setsContact_symm (G : SimpleGraph V) (A B : Set V) : setsContact G A B ↔ setsContact G B A := by
  constructor <;> rintro ⟨u, hu, v, hv, h⟩
  · exact ⟨v, hv, u, hu, h.elim (fun hh => Or.inl hh.symm) (fun hh => Or.inr hh.symm)⟩
  · exact ⟨v, hv, u, hu, h.elim (fun hh => Or.inl hh.symm) (fun hh => Or.inr hh.symm)⟩

def twoHubVertices (K L M : Set V) : Set V := K ∪ (L ∪ M)

theorem twoHub_bridge_of_reachable (G : SimpleGraph V) (K L M : Set V)
    (a b : twoHubVertices K L M) (ha : a.val ∈ L) (hb : b.val ∈ M)
    (hreach : (G.induce (twoHubVertices K L M)).Reachable a b) :
    setsContact G L M ∨ ∃ c : (G.induce K).ConnectedComponent,
      setsContact G (liftedComponent G K c) L ∧ setsContact G (liftedComponent G K c) M := by
  by_cases hdirect : setsContact G L M
  · exact Or.inl hdirect
  apply Or.inr
  by_contra hnone
  have hbridge (c : (G.induce K).ConnectedComponent)
      (hc : setsContact G (liftedComponent G K c) L) :
      ¬setsContact G (liftedComponent G K c) M := fun h => hnone ⟨c, hc, h⟩
  let S : Set (twoHubVertices K L M) :=
    {v | v.val ∈ L ∨ ∃ c : (G.induce K).ConnectedComponent,
      v.val ∈ liftedComponent G K c ∧ setsContact G (liftedComponent G K c) L}
  have haS : a ∈ S := Or.inl ha
  have hbS : b ∉ S := by
    rintro (hbL | ⟨c, hbc, htouch⟩)
    · exact hdirect ⟨b.val, hbL, b.val, hb, Or.inl rfl⟩
    · exact hbridge c htouch ⟨b.val, hbc, b.val, hb, Or.inl rfl⟩
  have hcut : ∀ u ∈ S, ∀ v ∉ S, ¬(G.induce (twoHubVertices K L M)).Adj u v := by
    intro u hu v hv huv
    have hvL : v.val ∉ L := fun h => hv (Or.inl h)
    rcases hu with huL | ⟨c, huc, htouch⟩
    · rcases v.property with hvK | hvH
      · let cc := (G.induce K).connectedComponentMk ⟨v.val, hvK⟩
        have hvc : v.val ∈ liftedComponent G K cc := ⟨hvK, rfl⟩
        have ht : setsContact G (liftedComponent G K cc) L := ⟨v.val, hvc, u.val, huL, Or.inr huv.symm⟩
        exact hv (Or.inr ⟨cc, hvc, ht⟩)
      · rcases hvH with hvL' | hvM
        · exact hvL hvL'
        · exact hdirect ⟨u.val, huL, v.val, hvM, Or.inr huv⟩
    · rcases v.property with hvK | hvH
      · exact hv (Or.inr ⟨c, liftedComponent_adj_closed G K c huc hvK huv, htouch⟩)
      · rcases hvH with hvL' | hvM
        · exact hvL hvL'
        · exact hbridge c htouch ⟨u.val, huc, v.val, hvM, Or.inr huv⟩
  obtain ⟨p⟩ := hreach
  exact hbS (walk_end_mem_isolated (G.induce (twoHubVertices K L M)) S hcut p haS)

/-- Any vertex connected to a hub either lies in a hub already, or lies in
one old component that touches a hub. This is an actual walk/cut argument. -/
theorem twoHub_entry_of_reachable (G : SimpleGraph V) (K L M : Set V)
    (a b : twoHubVertices K L M) (hb : b.val ∈ L ∪ M)
    (hreach : (G.induce (twoHubVertices K L M)).Reachable a b) :
    a.val ∈ L ∪ M ∨ ∃ c : (G.induce K).ConnectedComponent,
      a.val ∈ liftedComponent G K c ∧ setsContact G (liftedComponent G K c) (L ∪ M) := by
  by_cases haH : a.val ∈ L ∪ M
  · exact Or.inl haH
  apply Or.inr
  have haK : a.val ∈ K := a.property.resolve_right haH
  let c := (G.induce K).connectedComponentMk ⟨a.val, haK⟩
  have hac : a.val ∈ liftedComponent G K c := ⟨haK, rfl⟩
  refine ⟨c, hac, ?_⟩
  by_cases hbc : b.val ∈ liftedComponent G K c
  · exact ⟨b.val, hbc, b.val, hb, Or.inl rfl⟩
  · obtain ⟨p⟩ := hreach
    obtain ⟨u, hu, v, hv, huv⟩ := walk_crosses_cut (G.induce (twoHubVertices K L M)) p
      {v | v.val ∈ liftedComponent G K c} hac hbc
    have hvH : v.val ∈ L ∪ M := by
      rcases v.property with hvK | hvH
      · exact False.elim (hv (liftedComponent_adj_closed G K c hu hvK huv))
      · exact hvH
    exact ⟨u.val, hu, v.val, hvH, Or.inr huv⟩

end LocalLaw
