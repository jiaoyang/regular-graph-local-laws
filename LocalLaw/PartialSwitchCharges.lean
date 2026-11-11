import LocalLaw.PartialSwitchRows
import LocalLaw.PartialSurgeryIdentity

/-! # The exact crossing-neighbor charges of a partial switching -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance partialSwitchChargesDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem sum_complement_point {X : Type} [Fintype X] [DecidableEq X] (S:Set X) (x:X) :
    (∑ w:(Sᶜ:Set X),if w.val=x then (1:ℂ) else 0)=if x∈S then 0 else 1 := by
  by_cases hx:x∈S
  · have hn:∀w:(Sᶜ:Set X),w.val≠x:=fun w h=>w.property (h.symm ▸ hx)
    simp [hx,hn]
  · let w0:(Sᶜ:Set X):=⟨x,hx⟩
    have he:(∑ w:(Sᶜ:Set X),if w.val=x then (1:ℂ) else 0)=1 := by
      rw [Finset.sum_eq_single w0]
      · simp [w0]
      · intro w _ hne
        have hw:w.val≠x:=fun h=>hne (Subtype.ext h)
        simp [hw]
      · intro hn;exact False.elim (hn (Finset.mem_univ _))
    simp [hx,he]

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d:ℕ}

omit [DecidableEq V] in
theorem crossingChargeDifference_cast_sum (g h:DeficientGraph V d) (S:Set V) (x:S) :
    (g.crossingChargeDifference h S x:ℂ)=
      (∑ w:(Sᶜ:Set V), ((if h.graph.Adj x.val w.val then (1:ℂ) else 0)-
        (if g.graph.Adj x.val w.val then 1 else 0)))/(((d:ℝ)-1:ℝ):ℂ) := by
  have hc (G:SimpleGraph V) : (Nat.card {w:(Sᶜ:Set V)//G.Adj w.val x.val}:ℂ)=
      ∑ w:(Sᶜ:Set V),if G.Adj x.val w.val then (1:ℂ) else 0 := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype]
    rw [Finset.sum_boole]
    simp only [G.adj_comm]
  unfold crossingChargeDifference
  rw [Complex.ofReal_div,Complex.ofReal_sub]
  simp only [Complex.ofReal_natCast]
  rw [hc h.graph,hc g.graph,Finset.sum_sub_distrib]

end DeficientGraph
namespace LabelledResamplingState
variable {V : Type} [Fintype V] {T:Set V} {ι:Type} [Fintype ι]

def outsideCrossingDelta (s:LabelledResamplingState V T ι) (selector:ℕ)
    (S:Set (Tᶜ:Set V)) (x:(Tᶜ:Set V)) : ℂ :=
  ∑ w:(Sᶜ:Set (Tᶜ:Set V)),
    ((if (outsideGraph (s.fullResample selector).graph T).Adj x w.val then (1:ℂ) else 0)-
      (if (outsideGraph s.graph T).Adj x w.val then 1 else 0))

theorem outsideCrossingDelta_boundary (s:LabelledResamplingState V T ι) (selector:ℕ)
    (S:Set (Tᶜ:Set V)) (i:s.AdmissibleSampleIndex selector) :
    s.outsideCrossingDelta selector S (s.admissibleBoundaryVertex selector i)=
      if s.admissibleSampleVertex selector i∈S then 0 else 1 := by
  unfold outsideCrossingDelta
  simp_rw [s.fullResample_outside_boundary_indicator selector i]
  exact sum_complement_point S (s.admissibleSampleVertex selector i)

theorem outsideCrossingDelta_first (s:LabelledResamplingState V T ι) (selector:ℕ)
    (S:Set (Tᶜ:Set V)) (i:s.AdmissibleSampleIndex selector) :
    s.outsideCrossingDelta selector S (s.admissibleSampleVertex selector i)=
      (if s.admissibleSecondVertex selector i∈S then 1 else 0)-
        (if s.admissibleBoundaryVertex selector i∈S then 1 else 0) := by
  unfold outsideCrossingDelta
  simp_rw [s.fullResample_outside_first_indicator selector i]
  rw [Finset.sum_sub_distrib,sum_complement_point,sum_complement_point]
  split_ifs <;> norm_num

theorem outsideCrossingDelta_second (s:LabelledResamplingState V T ι) (selector:ℕ)
    (S:Set (Tᶜ:Set V)) (i:s.AdmissibleSampleIndex selector) :
    s.outsideCrossingDelta selector S (s.admissibleSecondVertex selector i)=
      -(if s.admissibleSampleVertex selector i∈S then 0 else 1) := by
  unfold outsideCrossingDelta
  simp_rw [s.fullResample_outside_second_indicator selector i]
  rw [Finset.sum_neg_distrib,sum_complement_point]

theorem outsideCrossingDelta_eq_zero_away (s:LabelledResamplingState V T ι) (selector:ℕ)
    (S:Set (Tᶜ:Set V)) (x:(Tᶜ:Set V)) (hx:x∉s.fullResampleOutsideEndpoints selector) :
    s.outsideCrossingDelta selector S x=0 := by
  unfold outsideCrossingDelta
  apply Finset.sum_eq_zero
  intro w _
  rw [s.fullResample_outside_adj_of_away_left selector x w.val hx,sub_self]

end LabelledResamplingState
end LocalLaw
