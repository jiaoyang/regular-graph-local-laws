import LocalLaw.CappedPairCapture

/-! # Capped-distance triangle and shifted remaining-radius recovery

The capped distance is the truncation of the extended graph metric.
Unreachable pairs retain the full cap, so no default zero graph distance
is used in the triangle or recovery inequalities.
-/
noncomputable section
namespace LocalLaw
local instance shiftedRemainingRadiusDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type*}

theorem cappedGraphDistance_triangle (G:SimpleGraph V)(r:ℕ)(x u i:V):
    cappedGraphDistance G r x i≤cappedGraphDistance G r x u+cappedGraphDistance G r u i:=by
  by_cases hxu:G.Reachable x u
  · by_cases hui:G.Reachable u i
    · have hxi:=hxu.trans hui
      have hxu':(G.dist x u:ℕ∞)=G.edist x u:=ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr hxu)
      have hui':(G.dist u i:ℕ∞)=G.edist u i:=ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr hui)
      have hxi':(G.dist x i:ℕ∞)=G.edist x i:=ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr hxi)
      have htri:G.dist x i≤G.dist x u+G.dist u i:=by
        apply ENat.coe_le_coe.mp
        rw[ENat.coe_add,hxi',hxu',hui']
        exact G.edist_triangle
      simp only[cappedGraphDistance,if_pos hxu,if_pos hui,if_pos hxi]
      omega
    · have huicap:cappedGraphDistance G r u i=r:=by simp only[cappedGraphDistance,if_neg hui]
      rw[huicap]
      exact (cappedGraphDistance_le G r x i).trans (Nat.le_add_left _ _)
  · have hxcap:cappedGraphDistance G r x u=r:=by simp only[cappedGraphDistance,if_neg hxu]
    rw[hxcap]
    exact (cappedGraphDistance_le G r x i).trans (Nat.le_add_right _ _)

theorem cappedGraphDistance_le_of_near (G:SimpleGraph V)(r loss:ℕ)(x u:V)
    (hu:G.edist x u≤(loss:ℕ∞)) : cappedGraphDistance G r x u≤loss:=
  ENat.coe_le_coe.mp ((cappedGraphDistance_coe_le_edist G r x u).trans hu)

theorem remainingPairRadius_lower_of_near (G:SimpleGraph V)(r loss:ℕ)(x y u:V)
    (hu:G.edist x u≤(loss:ℕ∞) ∨ G.edist y u≤(loss:ℕ∞)):
    r-loss≤remainingPairRadius G r x y u:=by
  rcases hu with hx|hy
  · have hh:=cappedGraphDistance_le_of_near G r loss x u hx
    have hr:=(remainingPairRadius_recovery G r x y u).1
    omega
  · have hh:=cappedGraphDistance_le_of_near G r loss y u hy
    have hr:=(remainingPairRadius_recovery G r x y u).2
    omega

theorem remainingPairRadius_shifted_recovery (G:SimpleGraph V)(r loss:ℕ)(x y u i:V)
    (hu:G.edist x u≤(loss:ℕ∞) ∨ G.edist y u≤(loss:ℕ∞)):
    r-loss≤remainingPairRadius G r x y i+cappedGraphDistance G r u i:=by
  rcases hu with hx|hy
  · have hnear:=cappedGraphDistance_le_of_near G r loss x u hx
    have htri:=cappedGraphDistance_triangle G r x u i
    have hr:=(remainingPairRadius_recovery G r x y i).1
    omega
  · have hnear:=cappedGraphDistance_le_of_near G r loss y u hy
    have htri:=cappedGraphDistance_triangle G r y u i
    have hr:=(remainingPairRadius_recovery G r x y i).2
    omega

end LocalLaw
