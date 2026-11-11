import LocalLaw.CapturedBallComponents

/-! # Captured radii around a secondary target without halving the radius -/

namespace LocalLaw
variable {V : Type*} (G : SimpleGraph V)

theorem captured_ball_shift (S : Set V) (root leaf : V) (r : ℕ)
    (hreach : G.Reachable root leaf) (hcap : graphBallVertices G root r⊆S) (hleaf : leaf∈S) :
    graphBallVertices G leaf (r-min r (G.dist root leaf))⊆S := by
  by_cases hd : r≤G.dist root leaf
  · rw [min_eq_left hd,Nat.sub_self]
    intro v hv
    have he : leaf=v := SimpleGraph.edist_eq_zero_iff.mp (le_antisymm hv bot_le)
    exact he ▸ hleaf
  · have hdr : G.dist root leaf≤r := by omega
    rw [min_eq_right hdr]
    intro v hv
    apply hcap
    have heq : (G.dist root leaf:ℕ∞)=G.edist root leaf :=
      ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr hreach)
    calc
      G.edist root v≤G.edist root leaf+G.edist leaf v := G.edist_triangle
      _≤(G.dist root leaf:ℕ∞)+(r-G.dist root leaf:ℕ) := add_le_add heq.ge hv
      _=(r:ℕ∞) := by rw [←ENat.coe_add,Nat.add_sub_of_le hdr]

theorem captured_balls_shift_nearest (S : Set V) (i j leaf : V) (r : ℕ)
    (hi : G.Reachable i leaf) (hj : G.Reachable j leaf)
    (hI : graphBallVertices G i r⊆S) (hJ : graphBallVertices G j r⊆S) (hleaf : leaf∈S) :
    graphBallVertices G leaf (r-min r (min (G.dist i leaf) (G.dist j leaf)))⊆S := by
  by_cases hd : G.dist i leaf≤G.dist j leaf
  · rw [min_eq_left hd]
    exact captured_ball_shift G S i leaf r hi hI hleaf
  · rw [min_eq_right (by omega : G.dist j leaf≤G.dist i leaf)]
    exact captured_ball_shift G S j leaf r hj hJ hleaf

theorem shifted_localization_exponent (r d : ℕ) :
    r+(r-min r d)=2*r-min r d := by omega

end LocalLaw
