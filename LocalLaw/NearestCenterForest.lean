import LocalLaw.HeightForestPartition

/-!
# The actual nearest-center parent forest of a union of balls

The height is the least radius at which a vertex enters the union of root
balls. A genuine shortest walk gives an adjacent parent whose height drops
by exactly one. Thus the zero-height root set is exactly the supplied center
set, including all finite-radius rounding and disconnected ambient graphs.
-/

noncomputable section
namespace LocalLaw
local instance nearestForestDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*}

def setBallReachable (G : SimpleGraph V) (S : Set V) (r : ℕ) (v : graphSetBall G S r) :
    ∃ n : ℕ, v.val ∈ graphSetBall G S n := ⟨r, v.property⟩

def setBallHeight (G : SimpleGraph V) (S : Set V) (r : ℕ) (v : graphSetBall G S r) : ℕ :=
  Nat.find (setBallReachable G S r v)

theorem setBallHeight_spec (G : SimpleGraph V) (S : Set V) (r : ℕ) (v : graphSetBall G S r) :
    v.val ∈ graphSetBall G S (setBallHeight G S r v) := Nat.find_spec (setBallReachable G S r v)

theorem setBallHeight_le (G : SimpleGraph V) (S : Set V) (r : ℕ) (v : graphSetBall G S r) :
    setBallHeight G S r v ≤ r := Nat.find_min' (setBallReachable G S r v) v.property

theorem setBallHeight_zero (G : SimpleGraph V) (S : Set V) (r : ℕ) (v : graphSetBall G S r) :
    setBallHeight G S r v = 0 ↔ v.val ∈ S := by
  constructor
  · intro h
    have hh := setBallHeight_spec G S r v
    simpa only [h, graphSetBall_zero] using hh
  · intro h
    apply Nat.le_zero.mp
    apply Nat.find_min' (setBallReachable G S r v)
    simpa only [graphSetBall_zero] using h

theorem setBall_parent_exists (G : SimpleGraph V) (S : Set V) (r : ℕ)
    (v : {v : graphSetBall G S r // setBallHeight G S r v ≠ 0}) :
    ∃ u : graphSetBall G S r, (G.induce (graphSetBall G S r)).Adj v.val u ∧
      setBallHeight G S r u + 1 = setBallHeight G S r v.val := by
  obtain ⟨s, hs, p, hp⟩ := (mem_graphSetBall_iff_walk G S _ v.val.val).mp
    (setBallHeight_spec G S r v.val)
  have hrev : p.reverse.length ≤ setBallHeight G S r v.val := by
    simpa only [SimpleGraph.Walk.length_reverse] using hp
  generalize heq : p.reverse = q at hrev
  cases q with
  | nil =>
    exact False.elim (v.property ((setBallHeight_zero G S r v.val).mpr hs))
  | @cons v0 u s hvu q =>
    have htail : q.length + 1 ≤ setBallHeight G S r v.val := hrev
    have htailR : q.length ≤ r := by have hh := setBallHeight_le G S r v.val; omega
    have humem : u ∈ graphSetBall G S r :=
      (mem_graphSetBall_iff_walk G S r u).mpr
        ⟨s, hs, q.reverse, by simpa only [SimpleGraph.Walk.length_reverse] using htailR⟩
    let uu : graphSetBall G S r := ⟨u, humem⟩
    have huheight : setBallHeight G S r uu ≤ q.length :=
      Nat.find_min' (setBallReachable G S r uu)
        ((mem_graphSetBall_iff_walk G S q.length u).mpr
          ⟨s, hs, q.reverse, by simp only [SimpleGraph.Walk.length_reverse]; exact le_rfl⟩)
    have hvheight : setBallHeight G S r v.val ≤ setBallHeight G S r uu + 1 := by
      apply Nat.find_min' (setBallReachable G S r v.val)
      obtain ⟨a, ha, hd⟩ := setBallHeight_spec G S r uu
      refine ⟨a, ha, ?_⟩
      calc
        G.edist a v.val.val ≤ G.edist a u + G.edist u v.val.val := G.edist_triangle
        _ ≤ (setBallHeight G S r uu : ℕ∞) + 1 :=
          add_le_add hd (le_of_eq (SimpleGraph.edist_eq_one_iff_adj.mpr hvu.symm))
        _ = ((setBallHeight G S r uu + 1 : ℕ) : ℕ∞) := by norm_cast
    exact ⟨uu, hvu, by omega⟩

def setBallHeightForest (G : SimpleGraph V) (S : Set V) (r : ℕ) :
    HeightForestData (graphSetBall G S r) where
  height := setBallHeight G S r
  parent v := Classical.choose (setBall_parent_exists G S r v)
  parent_height v := (Classical.choose_spec (setBall_parent_exists G S r v)).2

theorem setBallHeightForest_parent_adj (G : SimpleGraph V) (S : Set V) (r : ℕ)
    (v : {v : graphSetBall G S r // (setBallHeightForest G S r).height v ≠ 0}) :
    (G.induce (graphSetBall G S r)).Adj v.val ((setBallHeightForest G S r).parent v) :=
  (Classical.choose_spec (setBall_parent_exists G S r v)).1

def setBallZeroRootEquiv (G : SimpleGraph V) (S : Set V) (r : ℕ) :
    {v : graphSetBall G S r // (setBallHeightForest G S r).height v = 0} ≃ S where
  toFun v := ⟨v.val.val, (setBallHeight_zero G S r v.val).mp v.property⟩
  invFun v := ⟨⟨v.val, ⟨v.val, v.property, by simp⟩⟩,
    (setBallHeight_zero G S r _).mpr v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end LocalLaw
