import LocalLaw.CappedPairCapture

/-! # The remaining radius has an actual mixed-center certificate -/

noncomputable section
namespace LocalLaw
local instance remainingPairMixedRadiusDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type*}

theorem remainingPairRadius_le (G:SimpleGraph V)(r:ℕ)(x y u:V) :
    remainingPairRadius G r x y u≤r:=by
  exact max_le (Nat.sub_le _ _) (Nat.sub_le _ _)

theorem remainingRadius_center_or_zero (G:SimpleGraph V)(r:ℕ)(x u:V) :
    r-cappedGraphDistance G r x u=0 ∨
      G.edist x u≤((r-(r-cappedGraphDistance G r x u):ℕ):ℕ∞) := by
  by_cases hr:G.Reachable x u
  · rw [cappedGraphDistance,if_pos hr]
    by_cases hd:G.dist x u≤r
    · right
      rw [min_eq_right hd,Nat.sub_sub_self hd]
      exact (ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr hr)).ge
    · left
      rw [min_eq_left (by omega:r≤G.dist x u),Nat.sub_self]
  · left
    rw [cappedGraphDistance,if_neg hr,Nat.sub_self]

theorem remainingPairRadius_mixed (G:SimpleGraph V)(r:ℕ)(x y u:V) :
    remainingPairRadius G r x y u=0 ∨
      G.edist x u≤((r-remainingPairRadius G r x y u:ℕ):ℕ∞) ∨
      G.edist y u≤((r-remainingPairRadius G r x y u:ℕ):ℕ∞) := by
  unfold remainingPairRadius
  by_cases hh:r-cappedGraphDistance G r x u≤r-cappedGraphDistance G r y u
  · rw [max_eq_right hh]
    rcases remainingRadius_center_or_zero G r y u with h|h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rw [max_eq_left (by omega:r-cappedGraphDistance G r y u≤r-cappedGraphDistance G r x u)]
    rcases remainingRadius_center_or_zero G r x u with h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end LocalLaw
