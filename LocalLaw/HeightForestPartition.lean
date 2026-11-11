import LocalLaw.ComponentPairGeometry
import LocalLaw.ConnectedPartitionExcess

/-!
# Connected cells from a height-decreasing parent forest

A shortest-distance parent system to a set of roots gives an actual connected
vertex partition. Every vertex is connected to its assigned root by a walk
of exactly its height, entirely inside its own cell. This constructs the
bounded-radius cells needed for the union-ball excess estimate.
-/

noncomputable section
namespace LocalLaw
local instance heightForestPartitionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

structure HeightForestData (V : Type*) where
  height : V → ℕ
  parent : {v : V // height v ≠ 0} → V
  parent_height : ∀ v, height (parent v) + 1 = height v.val

namespace HeightForestData
variable {V : Type*} (D : HeightForestData V)

def terminal (D : HeightForestData V) (v : V) : V :=
  if h : D.height v = 0 then v else terminal D (D.parent ⟨v, h⟩)
termination_by D.height v
decreasing_by
  have hh := D.parent_height ⟨v, h⟩
  change D.height (D.parent ⟨v, h⟩) + 1 = D.height v at hh
  omega

theorem terminal_of_zero (v : V) (hv : D.height v = 0) : D.terminal v = v := by
  rw [terminal, dif_pos hv]

theorem terminal_parent (v : V) (hv : D.height v ≠ 0) :
    D.terminal v = D.terminal (D.parent ⟨v, hv⟩) := by
  rw [terminal, dif_neg hv]

theorem terminal_height_zero (v : V) : D.height (D.terminal v) = 0 := by
  have haux : ∀ n : ℕ, ∀ w : V, D.height w = n → D.height (D.terminal w) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hw
      by_cases hz : D.height w = 0
      · rw [D.terminal_of_zero w hz]
        exact hz
      · rw [D.terminal_parent w hz]
        apply ih (D.height (D.parent ⟨w, hz⟩)) _ _ rfl
        have hh := D.parent_height ⟨w, hz⟩
        change D.height (D.parent ⟨w, hz⟩) + 1 = D.height w at hh
        omega
  exact haux _ v rfl

def rootLabel (v : V) : {v : V // D.height v = 0} := ⟨D.terminal v, D.terminal_height_zero v⟩

theorem rootLabel_of_zero (v : V) (hv : D.height v = 0) : D.rootLabel v = ⟨v, hv⟩ :=
  Subtype.ext (D.terminal_of_zero v hv)

theorem rootLabel_parent (v : V) (hv : D.height v ≠ 0) :
    D.rootLabel v = D.rootLabel (D.parent ⟨v, hv⟩) :=
  Subtype.ext (D.terminal_parent v hv)

theorem walk_to_terminal (G : SimpleGraph V)
    (hparent : ∀ v, G.Adj v.val (D.parent v)) (v : V) :
    ∃ p : G.Walk v (D.terminal v), p.length = D.height v ∧
      ∀ x ∈ p.support, D.rootLabel x = D.rootLabel v := by
  have haux : ∀ n : ℕ, ∀ w : V, D.height w = n →
      ∃ p : G.Walk w (D.terminal w), p.length = D.height w ∧
        ∀ x ∈ p.support, D.rootLabel x = D.rootLabel w := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hw
      by_cases hz : D.height w = 0
      · rw [D.terminal_of_zero w hz]
        refine ⟨SimpleGraph.Walk.nil, hz.symm, ?_⟩
        intro x hx
        have heq : x = w := by simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton] using hx
        exact heq ▸ rfl
      · let a := D.parent ⟨w, hz⟩
        have ha : D.height a < n := by
          have hh := D.parent_height ⟨w, hz⟩
          change D.height a + 1 = D.height w at hh
          omega
        obtain ⟨p, hp, hsupp⟩ := ih (D.height a) ha a rfl
        have hlabel : D.rootLabel a = D.rootLabel w := (D.rootLabel_parent w hz).symm
        have hterminal : D.terminal a = D.terminal w := (D.terminal_parent w hz).symm
        have htarget : ∃ q : G.Walk w (D.terminal a), q.length = D.height w ∧
            ∀ x ∈ q.support, D.rootLabel x = D.rootLabel w := by
          refine ⟨p.cons (hparent ⟨w, hz⟩), ?_, ?_⟩
          · simp only [SimpleGraph.Walk.length_cons, hp]
            exact D.parent_height ⟨w, hz⟩
          · intro x hx
            simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact rfl
            · exact (hsupp x hx).trans hlabel
        exact Eq.mp (congrArg (fun t : V => ∃ q : G.Walk w t, q.length = D.height w ∧
          ∀ x ∈ q.support, D.rootLabel x = D.rootLabel w) hterminal) htarget
  exact haux _ v rfl

theorem cell_connected (G : SimpleGraph V) (hparent : ∀ v, G.Adj v.val (D.parent v))
    (i : {v : V // D.height v = 0}) : (G.induce {v | D.rootLabel v = i}).Connected := by
  let S : Set V := {v | D.rootLabel v = i}
  have hi : i.val ∈ S := D.rootLabel_of_zero i.val i.property
  let c : S := ⟨i.val, hi⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨c, ?_⟩
  intro v
  obtain ⟨p, _, hsupp⟩ := D.walk_to_terminal G hparent v.val
  have hs : ∀ x ∈ p.support, x ∈ S := fun x hx => (hsupp x hx).trans v.property
  have hend : D.terminal v.val ∈ S := hs _ p.end_mem_support
  obtain ⟨q, _⟩ := walk_lift_induced_of_support G S p hs v.property hend
  have hterminal : D.terminal v.val = i.val := congrArg Subtype.val v.property
  have heq : (⟨D.terminal v.val, hend⟩ : S) = c := Subtype.ext hterminal
  rw [heq] at q
  exact q.reachable.symm

theorem cell_radius (G : SimpleGraph V) (hparent : ∀ v, G.Adj v.val (D.parent v))
    (r : ℕ) (hheight : ∀ v, D.height v ≤ r) (i : {v : V // D.height v = 0})
    (v : V) (hv : D.rootLabel v = i) : G.edist i.val v ≤ (r : ℕ∞) := by
  obtain ⟨p, hp, _⟩ := D.walk_to_terminal G hparent v
  have hterminal : D.terminal v = i.val := congrArg Subtype.val hv
  have hh : G.edist (D.terminal v) v ≤ (D.height v : ℕ∞) := by
    simpa only [SimpleGraph.Walk.length_reverse, hp] using G.edist_le p.reverse
  rw [hterminal] at hh
  exact hh.trans (ENat.coe_le_coe.mpr (hheight v))

end HeightForestData
end LocalLaw
