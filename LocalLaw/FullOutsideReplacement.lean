import LocalLaw.FullOutsideAugmentation
import LocalLaw.ResamplingRadiusGrowth
import LocalLaw.AdmissibleGreenBlock

/-! # Exterior augmentation for arbitrary full-pair centers

An inner center contributes no exterior vertices beyond the already filled
central model. Replacing it by any outside point can only enlarge the old
augmentation. This extends all subset-based exterior factories to full
pairs whose original targets are allowed inside T.
-/
noncomputable section
namespace LocalLaw
local instance fullOutsideReplacementDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type}{T:Set V}{ι:Type}

def outsideReplacement (_s:LabelledResamplingState V T ι)(w:(Tᶜ:Set V))(x:V):(Tᶜ:Set V):=
  if hx:x∈T then w else ⟨x,hx⟩

theorem fullTwoTarget_subset_outside_replacements (s:LabelledResamplingState V T ι)
    (selector r:ℕ)(w:(Tᶜ:Set V))(x y:V):
    s.fullTwoTargetVertices selector r x y⊆s.fullTwoTargetVertices selector r
      (s.outsideReplacement w x).val (s.outsideReplacement w y).val:=by
  have hcenter (a:V):graphBallVertices s.graph a r⊆
      filledExteriorVertices T (s.endpointModelVertices selector r)∪
        graphBallVertices s.graph (s.outsideReplacement w a).val r:=by
    by_cases ha:a∈T
    · intro v hv
      left
      rw[s.fullEndpointVertices_eq_setBall selector r]
      exact ⟨a,Or.inl ha,hv⟩
    · intro v hv
      right
      simpa only[outsideReplacement,dif_neg ha] using hv
  rintro v (hv|hv|hv)
  · exact Or.inl hv
  · exact (hcenter x hv).elim Or.inl (fun h=>Or.inr (Or.inl h))
  · exact (hcenter y hv).elim Or.inl (fun h=>Or.inr (Or.inr h))

theorem fullTwoTarget_outside_subset_replacements (s:LabelledResamplingState V T ι)
    (selector r:ℕ)(w:(Tᶜ:Set V))(x y:V):
    s.fullSliceOutside (s.fullTwoTargetVertices selector r x y)⊆
      s.twoTargetEndpointVertices selector r (s.outsideReplacement w x) (s.outsideReplacement w y):=by
  intro v hv
  have hh:=s.fullTwoTarget_subset_outside_replacements selector r w x y hv
  change v∈s.fullSliceOutside (s.fullTwoTargetVertices selector r
    (s.outsideReplacement w x).val (s.outsideReplacement w y).val) at hh
  rw[s.fullTwoTarget_outside_slice selector r (s.outsideReplacement w x) (s.outsideReplacement w y)] at hh
  exact hh

variable [Fintype ι]
theorem switched_full_pair_outside_subset_replacements (s:LabelledResamplingState V T ι)
    (selector r:ℕ)(w:(Tᶜ:Set V))(x y:V):
    s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r)⊆
      s.twoTargetEndpointVertices selector r (s.outsideReplacement w x) (s.outsideReplacement w y):=by
  intro v hv
  exact s.fullTwoTarget_outside_subset_replacements selector r w x y
    (s.switched_full_pair_subset_old_augmentation selector r x y hv)

end LabelledResamplingState
namespace RegularGraph

theorem eventually_actual_inner_complement_nonempty (a d:ℕ)(ha:0<a)(hd:3≤d):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:RegularGraph N d)(o:Fin N)(z:ℂ),
      Nonempty ((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N)):=by
  have hdepth:=(lowerLogLogRadius_tendsto a d ha hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_resampling_ball_budget a d hd,hdepth,Filter.eventually_ge_atTop 1]
    with N hbudget hdepthN hN
  intro g o z
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  have hell:actualCavityDepth a d N z-1≤doubleLogRadius a d N:=
    (actualCavityDepth_radius_bounds a d N z hdepthN).2
  have hsmall:4*Nat.card T≤N:=g.ball_small o _
    ((Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by omega:0<d+1) hell)).trans hbudget)
  by_contra hnonempty
  have hall:∀v:Fin N,v∈T:=by
    intro v
    by_contra hv
    exact hnonempty ⟨⟨v,hv⟩⟩
  let f:Fin N→T:=fun v=>⟨v,hall v⟩
  have hf:Function.Injective f:=fun _ _ h=>congrArg (fun t:T=>t.val) h
  have hcard:N≤Nat.card T:=by
    simpa only[Nat.card_eq_fintype_card,Fintype.card_fin] using Nat.card_le_card_of_injective f hf
  omega

end RegularGraph
end LocalLaw
