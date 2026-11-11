import LocalLaw.FullRegionStarLayout

/-! # Boundary-root containment and the full-metric far annulus of the star -/

noncomputable section
namespace LocalLaw
local instance fullRegionSupportDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type}{T:Set V}{ι:Type}[Fintype ι]

omit [Fintype ι] in
theorem admissibleBoundaryVertex_mem_fullRegion (s:LabelledResamplingState V T ι)(selector r:ℕ)(x y:V)
    (i:s.AdmissibleSampleIndex selector) :
    s.admissibleBoundaryVertex selector i∈s.fullSliceOutside (s.fullTwoTargetVertices selector r x y):=by
  apply Or.inl
  apply Or.inr
  refine ⟨s.admissibleBoundaryVertex selector i,?_,rfl⟩
  exact ⟨s.admissibleBoundaryVertex selector i,Or.inl ⟨s.boundary i.val,rfl⟩,by
    change (outsideGraph s.graph T).edist (s.admissibleBoundaryVertex selector i)
      (s.admissibleBoundaryVertex selector i)≤(r:ℕ∞)
    rw[SimpleGraph.edist_self]
    exact bot_le⟩

theorem fullRegion_near_not_outer (s:LabelledResamplingState V T ι)(selector r loss:ℕ)(x y:V)
    (hloss:loss≤r-2)(u:(Tᶜ:Set V))
    (hu:(s.fullResample selector).graph.edist x u.val≤(loss:ℕ∞) ∨
      (s.fullResample selector).graph.edist y u.val≤(loss:ℕ∞)) :
    u∉s.fullRegionOuterFirst selector r x y:=by
  intro hout
  apply hout.2
  rcases hu with hx|hy
  · exact Or.inl (hx.trans (ENat.coe_le_coe.mpr hloss))
  · exact Or.inr (hy.trans (ENat.coe_le_coe.mpr hloss))

theorem fullRegion_outer_far_of_near (s:LabelledResamplingState V T ι)(selector r loss:ℕ)(x y:V)
    (hloss:loss≤r-2)(hr:2≤r)(u b:(Tᶜ:Set V))
    (hu:(s.fullResample selector).graph.edist x u.val≤(loss:ℕ∞) ∨
      (s.fullResample selector).graph.edist y u.val≤(loss:ℕ∞))
    (hb:b∈s.fullRegionOuterFirst selector r x y) :
    (((r-loss-2)+1:ℕ):ℕ∞)≤(s.fullResample selector).graph.edist u.val b.val:=by
  let G:=(s.fullResample selector).graph
  have hone (a:V)(ha:G.edist a u.val≤(loss:ℕ∞))
      (hnot:¬G.edist a b.val≤((r-2:ℕ):ℕ∞)) :
      (((r-loss-2)+1:ℕ):ℕ∞)≤G.edist u.val b.val:=by
    have hbfar:(((r-2)+1:ℕ):ℕ∞)≤G.edist a b.val:=by
      have hh:((r-2:ℕ):ℕ∞)<G.edist a b.val:=lt_of_not_ge hnot
      exact_mod_cast (ENat.add_one_le_iff (ENat.coe_ne_top (r-2))).mpr hh
    have htri:G.edist a b.val≤(loss:ℕ∞)+G.edist u.val b.val:=by
      calc
        _≤G.edist a u.val+G.edist u.val b.val:=G.edist_triangle
        _≤_:=add_le_add_right ha _
    have he:(((r-loss-2)+1:ℕ):ℕ∞)+(loss:ℕ∞)=(((r-2)+1:ℕ):ℕ∞):=by
      norm_cast
      omega
    have hh:(((r-loss-2)+1:ℕ):ℕ∞)+(loss:ℕ∞)≤G.edist u.val b.val+(loss:ℕ∞):=by
      rw[he,add_comm (G.edist u.val b.val)]
      exact hbfar.trans htri
    exact (WithTop.add_le_add_iff_right (ENat.coe_ne_top loss)).mp hh
  rcases hu with hx|hy
  · exact hone x hx (fun hh=>hb.2 (Or.inl hh))
  · exact hone y hy (fun hh=>hb.2 (Or.inr hh))

end LabelledResamplingState
end LocalLaw
