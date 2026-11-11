import LocalLaw.SelectedCommonMixedCapture
import LocalLaw.FullOutsideReplacement
import LocalLaw.RemainingPairMixedRadius

/-! # Mixed full-center captures in the actual common B-deleted graph -/
noncomputable section
namespace LocalLaw
local instance fullSelectedCommonCaptureDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type}{T:Set V}{ι:Type}[Fintype ι]

theorem selectedCommon_full_mixed_shifted_capture (s:LabelledResamplingState V T ι)
    (selector r ri:ℕ)(hri:ri≤r)(A:Set (Tᶜ:Set V))(x y:V)
    (u:((s.partialFirstRemovedSet selector A)ᶜ:Set A))
    (hS:u.val.val.val∈pairBallVertices (s.fullResample selector).graph x y r)
    (hu:ri=0 ∨ (s.fullResample selector).graph.edist x u.val.val.val≤((r-ri:ℕ):ℕ∞) ∨
      (s.fullResample selector).graph.edist y u.val.val.val≤((r-ri:ℕ):ℕ∞)):
    graphBallVertices (outsideGraph ((outsideGraph s.graph T).induce A)
      (s.partialFirstRemovedSet selector A)) u ri⊆
      {v:((s.partialFirstRemovedSet selector A)ᶜ:Set A)|
        v.val.val.val∈pairBallVertices (s.fullResample selector).graph x y r}:=by
  have hmetric (v:((s.partialFirstRemovedSet selector A)ᶜ:Set A)):
      (s.fullResample selector).graph.edist u.val.val.val v.val.val.val≤
        (outsideGraph ((outsideGraph s.graph T).induce A)
          (s.partialFirstRemovedSet selector A)).edist u v:=
    (ambient_edist_le_induced_edist (s.fullResample selector).graph Tᶜ u.val.val v.val.val).trans
      (graphHom_edist_le (s.selectedCommonRegionNewHom selector A) u v)
  have hleft (a:V)(hau:(s.fullResample selector).graph.edist a u.val.val.val≤((r-ri:ℕ):ℕ∞))
      (v:((s.partialFirstRemovedSet selector A)ᶜ:Set A))
      (hv:v∈graphBallVertices (outsideGraph ((outsideGraph s.graph T).induce A)
        (s.partialFirstRemovedSet selector A)) u ri):
      (s.fullResample selector).graph.edist a v.val.val.val≤(r:ℕ∞):=by
    calc
      _≤(s.fullResample selector).graph.edist a u.val.val.val+
        (s.fullResample selector).graph.edist u.val.val.val v.val.val.val:=SimpleGraph.edist_triangle
      _≤((r-ri:ℕ):ℕ∞)+(ri:ℕ∞):=add_le_add hau ((hmetric v).trans hv)
      _=(r:ℕ∞):=by norm_cast;omega
  intro v hv
  rcases hu with hzero|hx|hy
  · subst ri
    have he:u=v:=SimpleGraph.edist_eq_zero_iff.mp (le_antisymm hv bot_le)
    exact he ▸ hS
  · exact Or.inl (hleft x hx v hv)
  · exact Or.inr (hleft y hy v hv)

theorem selectedCommon_full_remaining_radius_capture (s:LabelledResamplingState V T ι)
    (selector r:ℕ)(A:Set (Tᶜ:Set V))(x y:V)
    (u:((s.partialFirstRemovedSet selector A)ᶜ:Set A))
    (hS:u.val.val.val∈pairBallVertices (s.fullResample selector).graph x y r):
    graphBallVertices (outsideGraph ((outsideGraph s.graph T).induce A)
      (s.partialFirstRemovedSet selector A)) u
        (remainingPairRadius (s.fullResample selector).graph r x y u.val.val.val)⊆
      {v:((s.partialFirstRemovedSet selector A)ᶜ:Set A)|
        v.val.val.val∈pairBallVertices (s.fullResample selector).graph x y r}:=
  s.selectedCommon_full_mixed_shifted_capture selector r _ (remainingPairRadius_le _ _ _ _ _) A x y u hS
    (remainingPairRadius_mixed _ _ _ _ _)

end LabelledResamplingState
end LocalLaw
