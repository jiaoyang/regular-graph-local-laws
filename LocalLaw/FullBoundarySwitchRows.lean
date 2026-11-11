import LocalLaw.FullSwitchRows
import LocalLaw.PartialSwitchCharges

/-! Full accepted outer-boundary row and exact retained row sums. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance fullBoundarySwitchRowsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type}

theorem SwitchingQuad.boundary_indicator_difference (q:SwitchingQuad V)(G:SimpleGraph V)
    (h:q.Admissible G)(y:V):
    (if (q.apply G).Adj q.b y then (1:ℂ) else 0)-(if G.Adj q.b y then 1 else 0)=
      (if y=q.c then 1 else 0)-(if y=q.a then 1 else 0):=by
  rw [show (q.apply G).Adj q.b y↔(G.Adj q.b y∧y≠q.a)∨y=q.c from h.adj_b y]
  by_cases hyc:y=q.c
  · subst y
    have hold:¬G.Adj q.b q.c:=h.new_bc
    simp [hold,h.ac_ne.symm]
  · by_cases hya:y=q.a
    · subst y
      simp [h.old_ab.symm,hyc]
    · simp [hyc,hya]

theorem sum_retained_point [Fintype V] (S:Set V)(x:V):
    (∑v:S,if v.val=x then (1:ℂ) else 0)=if x∈S then 1 else 0:=by
  by_cases hx:x∈S
  · let x0:S:=⟨x,hx⟩
    rw [if_pos hx,Finset.sum_eq_single x0]
    · simp [x0]
    · intro v _ hv
      have hne:v.val≠x:=fun hh=>hv (Subtype.ext hh)
      simp [hne]
    · intro hn
      exact False.elim (hn (Finset.mem_univ x0))
  · have hne:∀v:S,v.val≠x:=fun v hh=>hx (hh ▸ v.property)
    simp [hx,hne]

namespace LabelledResamplingState
variable {T:Set V}{ι:Type}[Fintype ι]

theorem full_boundary_indicator_difference (s:LabelledResamplingState V T ι)
    (selector:ℕ)(i:s.AdmissibleSampleIndex selector)(y:V):
    (if (s.fullResample selector).graph.Adj (s.admissibleBoundaryVertex selector i).val y then (1:ℂ) else 0)-
      (if s.graph.Adj (s.admissibleBoundaryVertex selector i).val y then 1 else 0)=
      (if y=(s.quad i.val).c then 1 else 0)-(if y=(s.quad i.val).a then 1 else 0):=by
  change (if (s.fullResample selector).graph.Adj (s.quad i.val).b y then (1:ℂ) else 0)-_= _
  rw [s.fullResample_eligible_exterior_incident selector i (s.quad i.val).b y (Or.inl rfl)]
  exact (s.quad i.val).boundary_indicator_difference s.graph
    (sampledSwitching_admissible s.graph T selector s.samples (s.boundary i.val) i.property.1 i.property.2) y

variable [Fintype V]

def fullRetainedRowDelta (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set V)(x:V):ℂ:=
  ∑v:S,((if (s.fullResample selector).graph.Adj x v.val then (1:ℂ) else 0)-
    (if s.graph.Adj x v.val then 1 else 0))

theorem fullRetainedRowDelta_boundary (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set V)
    (i:s.AdmissibleSampleIndex selector):
    s.fullRetainedRowDelta selector S (s.admissibleBoundaryVertex selector i).val=
      (if (s.admissibleSampleVertex selector i).val∈S then 1 else 0)-
        (if (s.quad i.val).a∈S then 1 else 0):=by
  unfold fullRetainedRowDelta
  simp_rw [s.full_boundary_indicator_difference selector i]
  rw [Finset.sum_sub_distrib,sum_retained_point,sum_retained_point]
  rfl

theorem fullRetainedRowDelta_first (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set V)
    (i:s.AdmissibleSampleIndex selector):
    s.fullRetainedRowDelta selector S (s.admissibleSampleVertex selector i).val=
      (if (s.admissibleBoundaryVertex selector i).val∈S then 1 else 0)-
        (if (s.admissibleSecondVertex selector i).val∈S then 1 else 0):=by
  unfold fullRetainedRowDelta
  simp_rw [s.full_first_indicator_difference selector i]
  rw [Finset.sum_sub_distrib,sum_retained_point,sum_retained_point]
  rfl

theorem fullRetainedRowDelta_second (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set V)
    (i:s.AdmissibleSampleIndex selector):
    s.fullRetainedRowDelta selector S (s.admissibleSecondVertex selector i).val=
      (if (s.quad i.val).a∈S then 1 else 0)-
        (if (s.admissibleSampleVertex selector i).val∈S then 1 else 0):=by
  unfold fullRetainedRowDelta
  simp_rw [s.full_second_indicator_difference selector i]
  rw [Finset.sum_sub_distrib,sum_retained_point,sum_retained_point]
  rfl

end LabelledResamplingState
end LocalLaw
