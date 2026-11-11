import LocalLaw.SelectedFirstPairOccupancy
import LocalLaw.AugmentedPairCapture

/-! # Retain only the selected B vertices whose complete stars are captured

The two-edge inset keeps every neighbor of a restored sampled vertex in
the actual target pair neighborhood. Every selected target is retained;
the remaining selected vertices are far enough for direct deletion.
-/

noncomputable section
namespace LocalLaw
local instance innerSelectedGeometryDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type}{T:Set V}{ι:Type} [Fintype ι]

def innerFirstSet (s:LabelledResamplingState V T ι)(selector r:ℕ)(x y:(Tᶜ:Set V)) :
    Set (Tᶜ:Set V):=
  s.selectedFirstSet selector∩pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y (r-2)

def outerFirstSet (s:LabelledResamplingState V T ι)(selector r:ℕ)(x y:(Tᶜ:Set V)) :
    Set (Tᶜ:Set V):=
  s.selectedFirstSet selector\pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y (r-2)

theorem outerFirst_targets_not_mem (s:LabelledResamplingState V T ι)(selector r:ℕ)(x y:(Tᶜ:Set V)) :
    x∉s.outerFirstSet selector r x y ∧ y∉s.outerFirstSet selector r x y := by
  constructor
  · intro h
    exact h.2 (Or.inl (center_mem_graphBall _ x (r-2)))
  · intro h
    exact h.2 (Or.inr (center_mem_graphBall _ y (r-2)))

theorem innerFirst_neighbors_captured (s:LabelledResamplingState V T ι)
    (selector r:ℕ)(hr:1≤r)(x y b v:(Tᶜ:Set V))
    (hb:b∈s.innerFirstSet selector r x y)
    (hvb:(outsideGraph (s.fullResample selector).graph T).Adj b v) :
    v∈pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r := by
  let G:=outsideGraph (s.fullResample selector).graph T
  have he:G.edist b v=1:=SimpleGraph.edist_eq_one_iff_adj.mpr hvb
  have hroom:(r-2)+1≤r:=by omega
  have hone (a:(Tᶜ:Set V))(ha:G.edist a b≤((r-2:ℕ):ℕ∞)) : G.edist a v≤(r:ℕ∞):=by
    calc
      _≤G.edist a b+G.edist b v:=G.edist_triangle
      _≤((r-2:ℕ):ℕ∞)+1:=by rw [he];exact add_le_add_right ha _
      _≤(r:ℕ∞):=by exact_mod_cast hroom
  rcases hb.2 with hx|hy
  · exact Or.inl (hone x hx)
  · exact Or.inr (hone y hy)

theorem inner_outer_partition (s:LabelledResamplingState V T ι)(selector r:ℕ)(x y:(Tᶜ:Set V)) :
    s.innerFirstSet selector r x y∪s.outerFirstSet selector r x y=s.selectedFirstSet selector := by
  ext v
  simp only [innerFirstSet,outerFirstSet,Set.mem_union,Set.mem_inter_iff,Set.mem_diff]
  tauto

variable [Fintype V]

theorem innerFirstSet_card (s:LabelledResamplingState V T ι)(selector r:ℕ)
    (hsep:2*(r-2)≤selector)(x y:(Tᶜ:Set V)) : Nat.card (s.innerFirstSet selector r x y)≤2 :=
  s.selectedFirst_new_pairBall_card selector (r-2) hsep x y

end LabelledResamplingState
end LocalLaw
