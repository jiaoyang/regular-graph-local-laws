import LocalLaw.GeneralGraphEuler
import LocalLaw.GraphExcessSurgery

/-!
# Adding edges to a possibly disconnected finite graph

Adding an edge set merges components and increases Euler excess by at most
the number of added edges. The component-count monotonicity is derived from
the actual surjective map on connected components.
-/

noncomputable section
namespace LocalLaw
local instance generalExcessSurgeryDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V]

theorem connectedComponent_card_mono {G H : SimpleGraph V} (hGH : G ≤ H) :
    Nat.card H.ConnectedComponent ≤ Nat.card G.ConnectedComponent := by
  let f : G →g H := { toFun := id, map_rel' := fun h => hGH h }
  have hf : Function.Surjective (fun C : G.ConnectedComponent => C.map f) := by
    intro C
    obtain ⟨v, hv⟩ := C.exists_rep
    exact ⟨G.connectedComponentMk v, hv⟩
  exact Nat.card_le_card_of_surjective _ hf

theorem graphExcess_sup_le (G H : SimpleGraph V) :
    graphExcess (G ⊔ H) ≤ graphExcess G + graphEdgeCount H := by
  have he := graphEdgeCount_sup_le G H
  have hc := connectedComponent_card_mono (show G ≤ G ⊔ H from le_sup_left)
  have hG := graph_excess_euler G
  have hsup := graph_excess_euler (G ⊔ H)
  omega

end LocalLaw
