import LocalLaw.SelectedCommonCapture

/-! # Original pair centers capture shifted common-deleted balls

The centers may themselves be selected B vertices. Only the secondary
common target and its actual NEW distance to the original center enter.
-/

noncomputable section
namespace LocalLaw
local instance selectedCommonShiftedCaptureDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type}{T:Set V}{ι:Type}[Fintype ι]

def selectedCommonRegionNewHom (s:LabelledResamplingState V T ι)(selector:ℕ)(A:Set (Tᶜ:Set V)) :
    outsideGraph ((outsideGraph s.graph T).induce A) (s.partialFirstRemovedSet selector A) →g
      outsideGraph (s.fullResample selector).graph T where
  toFun v:=v.val.val
  map_rel':=fun {u v} h=>(s.fullResample_without_selectedFirst_adj selector
    ⟨u.val.val,u.property⟩ ⟨v.val.val,v.property⟩).mpr h

theorem selectedCommon_left_shifted_capture (s:LabelledResamplingState V T ι)(selector r ri:ℕ)
    (hri:ri≤r)(A:Set (Tᶜ:Set V))(x y:(Tᶜ:Set V))
    (u:((s.partialFirstRemovedSet selector A)ᶜ:Set A))
    (hu:(outsideGraph (s.fullResample selector).graph T).edist x u.val.val≤((r-ri:ℕ):ℕ∞)) :
    graphBallVertices (outsideGraph ((outsideGraph s.graph T).induce A)
      (s.partialFirstRemovedSet selector A)) u ri ⊆
        {v:((s.partialFirstRemovedSet selector A)ᶜ:Set A) |
          v.val.val∈pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r} := by
  intro v hv
  apply Or.inl
  calc
    _≤(outsideGraph (s.fullResample selector).graph T).edist x u.val.val+
      (outsideGraph (s.fullResample selector).graph T).edist u.val.val v.val.val:=
        SimpleGraph.edist_triangle
    _≤((r-ri:ℕ):ℕ∞)+(ri:ℕ∞):=add_le_add hu
      ((graphHom_edist_le (s.selectedCommonRegionNewHom selector A) u v).trans hv)
    _=(r:ℕ∞):=by norm_cast;omega

theorem selectedCommon_right_shifted_capture (s:LabelledResamplingState V T ι)(selector r ri:ℕ)
    (hri:ri≤r)(A:Set (Tᶜ:Set V))(x y:(Tᶜ:Set V))
    (u:((s.partialFirstRemovedSet selector A)ᶜ:Set A))
    (hu:(outsideGraph (s.fullResample selector).graph T).edist y u.val.val≤((r-ri:ℕ):ℕ∞)) :
    graphBallVertices (outsideGraph ((outsideGraph s.graph T).induce A)
      (s.partialFirstRemovedSet selector A)) u ri ⊆
        {v:((s.partialFirstRemovedSet selector A)ᶜ:Set A) |
          v.val.val∈pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r} := by
  intro v hv
  apply Or.inr
  calc
    _≤(outsideGraph (s.fullResample selector).graph T).edist y u.val.val+
      (outsideGraph (s.fullResample selector).graph T).edist u.val.val v.val.val:=
        SimpleGraph.edist_triangle
    _≤((r-ri:ℕ):ℕ∞)+(ri:ℕ∞):=add_le_add hu
      ((graphHom_edist_le (s.selectedCommonRegionNewHom selector A) u v).trans hv)
    _=(r:ℕ∞):=by norm_cast;omega

end LabelledResamplingState
end LocalLaw
