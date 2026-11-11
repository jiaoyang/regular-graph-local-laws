import LocalLaw.FullSwitchIndicator

/-! # Exact full adjacency changes at the two sampled vertices -/

noncomputable section
namespace LocalLaw
local instance fullSwitchRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type}

theorem SwitchingQuad.first_indicator_difference (q : SwitchingQuad V) (G : SimpleGraph V)
    (h : q.Admissible G) (y : V) :
    (if (q.apply G).Adj q.c y then (1 : ℂ) else 0) - (if G.Adj q.c y then 1 else 0) =
      (if y = q.b then 1 else 0) - (if y = q.d then 1 else 0) := by
  rw [show (q.apply G).Adj q.c y ↔ (G.Adj q.c y ∧ y ≠ q.d) ∨ y = q.b from h.adj_c y]
  by_cases hyb : y = q.b
  · subst y
    have hold : ¬G.Adj q.c q.b := fun hh => h.new_bc hh.symm
    simp [hold, h.bd_ne]
  · by_cases hyd : y = q.d
    · subst y
      simp [h.old_cd, hyb]
    · simp [hyb, hyd]

theorem SwitchingQuad.second_indicator_difference (q : SwitchingQuad V) (G : SimpleGraph V)
    (h : q.Admissible G) (y : V) :
    (if (q.apply G).Adj q.d y then (1 : ℂ) else 0) - (if G.Adj q.d y then 1 else 0) =
      (if y = q.a then 1 else 0) - (if y = q.c then 1 else 0) := by
  rw [show (q.apply G).Adj q.d y ↔ (G.Adj q.d y ∧ y ≠ q.c) ∨ y = q.a from h.adj_d y]
  by_cases hya : y = q.a
  · subst y
    have hold : ¬G.Adj q.d q.a := fun hh => h.new_ad hh.symm
    simp [hold, h.ac_ne]
  · by_cases hyc : y = q.c
    · subst y
      simp [h.old_cd.symm, hya]
    · simp [hya, hyc]

namespace LabelledResamplingState
variable {T : Set V} {ι : Type} [Fintype ι]

theorem full_first_indicator_difference (s : LabelledResamplingState V T ι)
    (selector : ℕ) (i : s.AdmissibleSampleIndex selector) (y : V) :
    (if (s.fullResample selector).graph.Adj (s.admissibleSampleVertex selector i).val y then (1 : ℂ) else 0) -
      (if s.graph.Adj (s.admissibleSampleVertex selector i).val y then 1 else 0) =
      (if y = (s.quad i.val).b then 1 else 0) - (if y = (s.quad i.val).d then 1 else 0) := by
  change (if (s.fullResample selector).graph.Adj (s.quad i.val).c y then (1 : ℂ) else 0) - _ = _
  rw [s.fullResample_eligible_exterior_incident selector i (s.quad i.val).c y (Or.inr (Or.inl rfl))]
  exact (s.quad i.val).first_indicator_difference s.graph
    (sampledSwitching_admissible s.graph T selector s.samples (s.boundary i.val) i.property.1 i.property.2) y

theorem full_second_indicator_difference (s : LabelledResamplingState V T ι)
    (selector : ℕ) (i : s.AdmissibleSampleIndex selector) (y : V) :
    (if (s.fullResample selector).graph.Adj (s.admissibleSecondVertex selector i).val y then (1 : ℂ) else 0) -
      (if s.graph.Adj (s.admissibleSecondVertex selector i).val y then 1 else 0) =
      (if y = (s.quad i.val).a then 1 else 0) - (if y = (s.quad i.val).c then 1 else 0) := by
  change (if (s.fullResample selector).graph.Adj (s.quad i.val).d y then (1 : ℂ) else 0) - _ = _
  rw [s.fullResample_eligible_exterior_incident selector i (s.quad i.val).d y (Or.inr (Or.inr rfl))]
  exact (s.quad i.val).second_indicator_difference s.graph
    (sampledSwitching_admissible s.graph T selector s.samples (s.boundary i.val) i.property.1 i.property.2) y

end LabelledResamplingState
end LocalLaw
