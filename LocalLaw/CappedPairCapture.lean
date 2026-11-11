import LocalLaw.ShiftedBallCapture

/-! # Remaining pair radii with unreachable distances handled explicitly

The capped distance equals r for an unreachable vertex. The corresponding
remaining radius is zero; no default natural graph distance is used across
components. These radii match the harmonic restoration tail inequalities.
-/

noncomputable section
namespace LocalLaw
local instance cappedPairCaptureDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type*}

def cappedGraphDistance (G:SimpleGraph V)(r:ℕ)(x u:V):ℕ:=
  if G.Reachable x u then min r (G.dist x u) else r

def remainingPairRadius (G:SimpleGraph V)(r:ℕ)(x y u:V):ℕ:=
  max (r-cappedGraphDistance G r x u) (r-cappedGraphDistance G r y u)

theorem cappedGraphDistance_le (G:SimpleGraph V)(r:ℕ)(x u:V) :
    cappedGraphDistance G r x u≤r := by
  unfold cappedGraphDistance
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem cappedGraphDistance_coe_le_edist (G:SimpleGraph V)(r:ℕ)(x u:V) :
    (cappedGraphDistance G r x u:ℕ∞)≤G.edist x u := by
  by_cases hr:G.Reachable x u
  · rw [cappedGraphDistance,if_pos hr]
    have he:(G.dist x u:ℕ∞)=G.edist x u:=
      ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr hr)
    exact (ENat.coe_le_coe.mpr (min_le_right r (G.dist x u))).trans he.le
  · rw [cappedGraphDistance,if_neg hr]
    have he:G.edist x u=⊤:=by
      by_contra hn
      exact hr (SimpleGraph.edist_ne_top_iff_reachable.mp hn)
    rw [he]
    exact le_top

theorem remainingPairRadius_recovery (G:SimpleGraph V)(r:ℕ)(x y u:V) :
    r≤remainingPairRadius G r x y u+cappedGraphDistance G r x u ∧
      r≤remainingPairRadius G r x y u+cappedGraphDistance G r y u := by
  have hx:=cappedGraphDistance_le G r x u
  have hy:=cappedGraphDistance_le G r y u
  have hleft:=le_max_left (r-cappedGraphDistance G r x u) (r-cappedGraphDistance G r y u)
  have hright:=le_max_right (r-cappedGraphDistance G r x u) (r-cappedGraphDistance G r y u)
  dsimp only [remainingPairRadius]
  omega

theorem captured_ball_capped_shift (G:SimpleGraph V)(S:Set V)(r:ℕ)(x u:V)
    (hcap:graphBallVertices G x r⊆S)(hu:u∈S) :
    graphBallVertices G u (r-cappedGraphDistance G r x u)⊆S := by
  by_cases hr:G.Reachable x u
  · rw [cappedGraphDistance,if_pos hr]
    exact captured_ball_shift G S x u r hr hcap hu
  · rw [cappedGraphDistance,if_neg hr,Nat.sub_self]
    intro v hv
    have he:u=v:=SimpleGraph.edist_eq_zero_iff.mp (le_antisymm hv bot_le)
    exact he ▸ hu

theorem captured_pair_remaining_radius (G:SimpleGraph V)(S:Set V)(r:ℕ)(x y u:V)
    (hx:graphBallVertices G x r⊆S)(hy:graphBallVertices G y r⊆S)(hu:u∈S) :
    graphBallVertices G u (remainingPairRadius G r x y u)⊆S := by
  have hi:=captured_ball_capped_shift G S r x u hx hu
  have hj:=captured_ball_capped_shift G S r y u hy hu
  unfold remainingPairRadius
  by_cases hh:r-cappedGraphDistance G r x u≤r-cappedGraphDistance G r y u
  · rw [max_eq_right hh]
    exact hj
  · rw [max_eq_left (by omega:r-cappedGraphDistance G r y u≤r-cappedGraphDistance G r x u)]
    exact hi

theorem graphHom_captured_ball {W:Type*}(G:SimpleGraph W)(H:SimpleGraph V)(f:G→g H)
    (S:Set V)(u:W)(r:ℕ)(hcap:graphBallVertices H (f u) r⊆S) :
    graphBallVertices G u r⊆{v:W | f v∈S} := by
  intro v hv
  exact hcap ((graphHom_edist_le f u v).trans hv)

end LocalLaw
