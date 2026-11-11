import LocalLaw.ResamplingSchedule

/-!
# The literal old/new boundary-label swap

Every eligible coordinate is inverted exactly once in the actual full
labelled schedule. Consequently its outside boundary endpoint changes to
the sampled second endpoint; every rejected label stays unchanged.
-/

noncomputable section
namespace LocalLaw
local instance resamplingBoundaryLabelsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type*} {T : Set V} {ι : Type*}

theorem flip_quad_self (s : LabelledResamplingState V T ι) (selector : ℕ) (i : ι) :
    (s.flip selector i).quad i = if s.Eligible selector i then (s.quad i).inverse else s.quad i := by
  by_cases hi : s.Eligible selector i
  · rw [if_pos hi, s.flip_eq_perform selector i hi, s.perform_quad selector i i hi.1 hi.2, if_pos rfl]
  · rw [if_neg hi, s.flip_eq_self selector i hi]

theorem flips_quad_nodup (s : LabelledResamplingState V T ι) (selector : ℕ)
    (L : List ι) (hL : L.Nodup) (j : ι) :
    (s.flips selector L).quad j =
      if j ∈ L ∧ s.Eligible selector j then (s.quad j).inverse else s.quad j := by
  induction L generalizing s with
  | nil => simp only [flips, List.not_mem_nil, false_and, if_false]
  | cons i L ih =>
    obtain ⟨hi, htail⟩ := List.nodup_cons.mp hL
    change ((s.flip selector i).flips selector L).quad j = _
    rw [ih (s.flip selector i) htail]
    by_cases hji : j = i
    · subst j
      rw [if_neg (fun h => hi h.1)]
      simpa only [List.mem_cons_self, true_and] using s.flip_quad_self selector i
    · rw [s.flip_eligible selector i j, s.flip_quad_of_ne selector hji]
      simp only [List.mem_cons, hji, false_or]

variable [Fintype ι]

theorem fullResample_quad_at_label (s : LabelledResamplingState V T ι) (selector : ℕ) (i : ι) :
    (s.fullResample selector).quad i = if s.Eligible selector i then (s.quad i).inverse else s.quad i := by
  have hh := s.flips_quad_nodup selector (Finset.univ : Finset ι).toList (Finset.nodup_toList _) i
  simpa only [Finset.mem_toList, Finset.mem_univ, true_and] using hh

theorem fullResample_boundary_outer (s : LabelledResamplingState V T ι) (selector : ℕ) (i : ι) :
    ((s.fullResample selector).boundary i).val.2 =
      if s.Eligible selector i then (s.samples (s.boundary i)).val.2 else (s.boundary i).val.2 := by
  have hh := congrArg SwitchingQuad.b (s.fullResample_quad_at_label selector i)
  simpa only [apply_ite, quad, sampledSwitchingQuad, SwitchingQuad.inverse] using hh

end LabelledResamplingState
end LocalLaw
