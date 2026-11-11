import LocalLaw.PartialSwitchCharges
import LocalLaw.PartialTripleSurgery

/-! # Exact actual coupling on the independent partial endpoint masks -/

noncomputable section
namespace LocalLaw
local instance partialSurgeryCouplingDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} [Fintype V] {T:Set V} {ι:Type} [Fintype ι]

instance partialEndpointIndexFintype (s:LabelledResamplingState V T ι) (selector:ℕ)
    (S:Set (Tᶜ:Set V)) : Fintype (s.PartialEndpointIndex selector S) := by
  unfold PartialEndpointIndex
  infer_instance

omit [Fintype V] [Fintype ι] in
theorem admissibleTripleVertex_eq_iff (s:LabelledResamplingState V T ι) (selector:ℕ)
    (i j:s.AdmissibleSampleIndex selector × Fin 3) :
    s.admissibleTripleVertex selector i=s.admissibleTripleVertex selector j↔i=j :=
  (s.admissibleTripleVertex_injective selector).eq_iff

omit [Fintype V] [Fintype ι] in
theorem admissibleBoundary_eq_first_false (s:LabelledResamplingState V T ι) (selector:ℕ)
    (i j:s.AdmissibleSampleIndex selector) :
    s.admissibleBoundaryVertex selector i≠s.admissibleSampleVertex selector j := by
  intro h
  have ht:s.admissibleTripleVertex selector (i,0)=s.admissibleTripleVertex selector (j,1):=h
  have hh:=congrArg (fun p:s.AdmissibleSampleIndex selector × Fin 3=>p.2.val)
    ((s.admissibleTripleVertex_injective selector) ht)
  norm_num at hh

omit [Fintype V] [Fintype ι] in
theorem admissibleBoundary_eq_second_false (s:LabelledResamplingState V T ι) (selector:ℕ)
    (i j:s.AdmissibleSampleIndex selector) :
    s.admissibleBoundaryVertex selector i≠s.admissibleSecondVertex selector j := by
  intro h
  have ht:s.admissibleTripleVertex selector (i,0)=s.admissibleTripleVertex selector (j,2):=h
  have hh:=congrArg (fun p:s.AdmissibleSampleIndex selector × Fin 3=>p.2.val)
    ((s.admissibleTripleVertex_injective selector) ht)
  norm_num at hh

omit [Fintype V] [Fintype ι] in
theorem admissibleFirst_eq_second_false (s:LabelledResamplingState V T ι) (selector:ℕ)
    (i j:s.AdmissibleSampleIndex selector) :
    s.admissibleSampleVertex selector i≠s.admissibleSecondVertex selector j := by
  intro h
  have ht:s.admissibleTripleVertex selector (i,1)=s.admissibleTripleVertex selector (j,2):=h
  have hh:=congrArg (fun p:s.AdmissibleSampleIndex selector × Fin 3=>p.2.val)
    ((s.admissibleTripleVertex_injective selector) ht)
  norm_num at hh

omit [Fintype V] [Fintype ι] in
theorem admissibleBoundary_eq_iff (s:LabelledResamplingState V T ι) (selector:ℕ)
    (i j:s.AdmissibleSampleIndex selector) :
    s.admissibleBoundaryVertex selector i=s.admissibleBoundaryVertex selector j↔i=j := by
  exact ⟨fun h=>congrArg Prod.fst ((s.admissibleTripleVertex_injective selector)
    (show s.admissibleTripleVertex selector (i,0)=s.admissibleTripleVertex selector (j,0) from h)),congrArg _⟩

omit [Fintype V] [Fintype ι] in
theorem admissibleFirst_eq_iff (s:LabelledResamplingState V T ι) (selector:ℕ)
    (i j:s.AdmissibleSampleIndex selector) :
    s.admissibleSampleVertex selector i=s.admissibleSampleVertex selector j↔i=j :=
  (s.admissibleSampleVertex_injective selector).eq_iff

omit [Fintype V] [Fintype ι] in
theorem admissibleSecond_eq_iff (s:LabelledResamplingState V T ι) (selector:ℕ)
    (i j:s.AdmissibleSampleIndex selector) :
    s.admissibleSecondVertex selector i=s.admissibleSecondVertex selector j↔i=j := by
  exact ⟨fun h=>congrArg Prod.fst ((s.admissibleTripleVertex_injective selector)
    (show s.admissibleTripleVertex selector (i,2)=s.admissibleTripleVertex selector (j,2) from h)),congrArg _⟩

def partialActualCoupling (s:LabelledResamplingState V T ι) (selector:ℕ)
    (S:Set (Tᶜ:Set V)) (m α:ℂ) :
    Matrix (s.PartialEndpointIndex selector S) (s.PartialEndpointIndex selector S) ℂ :=
  fun u v=>
    α*((if (outsideGraph (s.fullResample selector).graph T).Adj
        (s.partialEndpointEmbedding selector S u).val (s.partialEndpointEmbedding selector S v).val then 1 else 0)-
      (if (outsideGraph s.graph T).Adj
        (s.partialEndpointEmbedding selector S u).val (s.partialEndpointEmbedding selector S v).val then 1 else 0))-
      m*α^2*(if u=v then s.outsideCrossingDelta selector S
        (s.partialEndpointEmbedding selector S u).val else 0)

theorem partialActualCoupling_eq (s:LabelledResamplingState V T ι) (selector:ℕ)
    (S:Set (Tᶜ:Set V)) (m α:ℂ) :
    s.partialActualCoupling selector S m α=
      partialTripleEdgeUpdate (s.partialBoundaryMask selector S) (s.partialFirstMask selector S)
        (s.partialSecondMask selector S) α+
      partialTripleCharge (s.partialBoundaryMask selector S) (s.partialFirstMask selector S)
        (s.partialSecondMask selector S) m α := by
  ext u v
  rcases u with a | (b | c) <;> rcases v with a' | (b' | c')
  all_goals simp only [partialActualCoupling,partialEndpointEmbedding,partialEndpointVertex,
    Function.Embedding.coeFn_mk,partialTripleEdgeUpdate,partialTripleCharge,
    Matrix.add_apply,Matrix.diagonal_apply,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq]
  all_goals simp only [s.fullResample_outside_boundary_indicator,s.fullResample_outside_first_indicator,
    s.fullResample_outside_second_indicator,s.outsideCrossingDelta_boundary,
    s.outsideCrossingDelta_first,s.outsideCrossingDelta_second,
    s.admissibleBoundary_eq_first_false,s.admissibleBoundary_eq_second_false,
    s.admissibleFirst_eq_second_false,
    Ne.symm (s.admissibleBoundary_eq_first_false selector _ _),
    Ne.symm (s.admissibleBoundary_eq_second_false selector _ _),
    Ne.symm (s.admissibleFirst_eq_second_false selector _ _),
    s.admissibleBoundary_eq_iff,s.admissibleFirst_eq_iff,s.admissibleSecond_eq_iff,
    partialMatchingCoupling,partialBoundaryMask,partialFirstMask,partialSecondMask,
    Set.mem_setOf_eq,if_false,mul_zero,sub_zero,zero_sub,zero_add,add_zero]
  all_goals (try split_ifs) <;> (try simp_all only [Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq])
  all_goals (try simp_all) <;> ring_nf
  all_goals (try injections) <;> contradiction

end LabelledResamplingState
end LocalLaw
