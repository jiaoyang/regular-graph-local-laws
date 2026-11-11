import LocalLaw.GraphExcessSurgery

/-!
# Edges between two connected bounded-radius cells

Two disjoint connected cells, each lying within radius s of its own center,
have at most omega+1 cross edges if every radius-(2s+1) ball has excess at
most omega. A cross edge places both cells in one actual ball, and the
connected-cutset excess identity bounds their attachment multiplicity.
-/

noncomputable section
namespace LocalLaw
local instance cellCrossDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V]

def CellCrossEdge (G : SimpleGraph V) (A B : Set V) :=
  {e : V × V // G.Adj e.1 e.2 ∧ e.1 ∈ A ∧ e.2 ∈ B}

instance cellCrossEdgeFintype (G : SimpleGraph V) (A B : Set V) : Fintype (CellCrossEdge G A B) := by
  unfold CellCrossEdge
  infer_instance

theorem connected_cell_cross_edge_bound (G : SimpleGraph V) (A B : Set V)
    (hdisjoint : Disjoint A B) (hA : (G.induce A).Connected) (hB : (G.induce B).Connected)
    (a b : V) (s ω : ℕ)
    (hAradius : ∀ x ∈ A, G.edist a x ≤ (s : ℕ∞))
    (hBradius : ∀ x ∈ B, G.edist b x ≤ (s : ℕ∞))
    (hbudget : ∀ x, graphBallExcess G x (2 * s + 1) ≤ ω) :
    Nat.card (CellCrossEdge G A B) ≤ ω + 1 := by
  by_cases hnonempty : Nonempty (CellCrossEdge G A B)
  · obtain ⟨e⟩ := hnonempty
    let u := e.val.1
    let v := e.val.2
    let R := 2 * s + 1
    have hAin : A ⊆ graphBallVertices G u R := by
      intro x hx
      calc
        G.edist u x ≤ G.edist u a + G.edist a x := G.edist_triangle
        _ ≤ (s : ℕ∞) + (s : ℕ∞) := add_le_add
          (by simpa only [SimpleGraph.edist_comm] using hAradius u e.property.2.1) (hAradius x hx)
        _ ≤ (R : ℕ∞) := by dsimp only [R]; norm_cast; omega
    have hBin : B ⊆ graphBallVertices G u R := by
      intro x hx
      calc
        G.edist u x ≤ G.edist u v + G.edist v x := G.edist_triangle
        _ ≤ 1 + (G.edist v b + G.edist b x) := add_le_add
          (le_of_eq (SimpleGraph.edist_eq_one_iff_adj.mpr e.property.1)) G.edist_triangle
        _ ≤ 1 + ((s : ℕ∞) + (s : ℕ∞)) := add_le_add_left
          (add_le_add (by simpa only [SimpleGraph.edist_comm] using hBradius v e.property.2.2) (hBradius x hx)) 1
        _ = (R : ℕ∞) := by dsimp only [R]; norm_cast; omega
    let H := graphBall G u R
    let T : Set (graphBallVertices G u R) := {x | x.val ∈ A}
    let isoA : H.induce T ≃g G.induce A :=
      { toEquiv :=
          { toFun := fun x => ⟨x.val.val, x.property⟩
            invFun := fun x => ⟨⟨x.val, hAin x.property⟩, x.property⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        map_rel_iff' := Iff.rfl }
    have hT : (H.induce T).Connected := isoA.connected_iff.mpr hA
    let f : G.induce B →g outsideGraph H T :=
      { toFun := fun x => ⟨⟨x.val, hBin x.property⟩, by
          intro hx
          exact Set.disjoint_left.mp hdisjoint hx x.property⟩
        map_rel' := fun h => h }
    let bv : B := ⟨v, e.property.2.2⟩
    let C := (outsideGraph H T).connectedComponentMk (f bv)
    have hmember : ∀ x : B, f x ∈ C.supp := by
      intro x
      obtain ⟨p⟩ := hB.preconnected bv x
      exact (SimpleGraph.ConnectedComponent.sound (p.map f).reachable).symm
    let F : CellCrossEdge G A B → CutBoundaryEdge H T C := fun e' =>
      ⟨⟨(⟨e'.val.1, hAin e'.property.2.1⟩, ⟨e'.val.2, hBin e'.property.2.2⟩),
        e'.property.1, e'.property.2.1, by
          intro ha
          exact Set.disjoint_left.mp hdisjoint ha e'.property.2.2⟩,
        hmember ⟨e'.val.2, e'.property.2.2⟩⟩
    have hF : Function.Injective F := by
      intro x y h
      apply Subtype.ext
      have hh := congrArg (fun z : CutBoundaryEdge H T C =>
        (z.val.val.1.val, z.val.val.2.val)) h
      exact hh
    exact (Nat.card_le_card_of_injective F hF).trans
      (component_cut_multiplicity_bound H T (graphBall_connected G u R) hT ω (hbudget u) C)
  · haveI : IsEmpty (CellCrossEdge G A B) := not_nonempty_iff.mp hnonempty
    simp only [Nat.card_of_isEmpty, Nat.zero_le]

end LocalLaw
