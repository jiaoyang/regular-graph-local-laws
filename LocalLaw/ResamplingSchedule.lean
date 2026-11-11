import LocalLaw.LocalResamplingInvolution
import LocalLaw.ResamplingBadCenters

/-!
# The labelled involution as a simultaneous original-data switching schedule

The actual labelled resampling updates its dependent sample data after each
flip. For a schedule without repeated labels, the graph nevertheless equals
the switches at the initially eligible original quadruples. This links the
stationary labelled sampling construction to deterministic graph-locality
and bad-center bounds, without postulating a compatibility equality.
-/

noncomputable section
namespace LocalLaw
namespace LabelledResamplingState

local instance resamplingScheduleDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {V : Type*} {T : Set V} {ι : Type*}

/-- Original quadruples at the originally eligible coordinates in L. -/
def selectedQuads (s : LabelledResamplingState V T ι) (radius : ℕ) (L : List ι) :
    List (SwitchingQuad V) :=
  (L.filter (fun i => decide (s.Eligible radius i))).map s.quad

@[simp] theorem selectedQuads_nil (s : LabelledResamplingState V T ι) (radius : ℕ) :
    s.selectedQuads radius [] = [] := rfl

theorem selectedQuads_cons (s : LabelledResamplingState V T ι) (radius : ℕ)
    (i : ι) (L : List ι) :
    s.selectedQuads radius (i :: L) =
      if s.Eligible radius i then s.quad i :: s.selectedQuads radius L
      else s.selectedQuads radius L := by
  by_cases hi : s.Eligible radius i <;> simp [selectedQuads, hi]

theorem flip_quad_of_ne (s : LabelledResamplingState V T ι) (radius : ℕ)
    {i j : ι} (hji : j ≠ i) : (s.flip radius i).quad j = s.quad j := by
  by_cases hi : s.Eligible radius i
  · rw [s.flip_eq_perform radius i hi, s.perform_quad radius i j hi.1 hi.2, if_neg hji]
  · rw [s.flip_eq_self radius i hi]

theorem selectedQuads_flip_of_not_mem (s : LabelledResamplingState V T ι)
    (radius : ℕ) (i : ι) (L : List ι) (hi : i ∉ L) :
    (s.flip radius i).selectedQuads radius L = s.selectedQuads radius L := by
  have hfilter : L.filter (fun j => decide ((s.flip radius i).Eligible radius j)) =
      L.filter (fun j => decide (s.Eligible radius j)) := by
    apply List.filter_congr
    intro j _
    simp only [s.flip_eligible radius i j]
  unfold selectedQuads
  rw [hfilter]
  apply List.map_congr_left
  intro j hj
  have hjL := (List.mem_filter.mp hj).1
  exact s.flip_quad_of_ne radius (fun h => hi (h ▸ hjL))

/-- This is the graph compatibility theorem for the actual sequential
involution; no equality of graph constructions is an input. -/
theorem flips_graph_eq_applySwitches (s : LabelledResamplingState V T ι)
    (radius : ℕ) (L : List ι) (hL : L.Nodup) :
    (s.flips radius L).graph = applySwitches (s.selectedQuads radius L) s.graph := by
  induction L generalizing s with
  | nil => rfl
  | cons i L ih =>
      obtain ⟨hi, htail⟩ := List.nodup_cons.mp hL
      change ((s.flip radius i).flips radius L).graph = _
      rw [ih (s.flip radius i) htail, s.selectedQuads_flip_of_not_mem radius i L hi,
        s.selectedQuads_cons]
      by_cases he : s.Eligible radius i
      · rw [if_pos he, applySwitches_cons, s.flip_eq_perform radius i he]
        rfl
      · rw [if_neg he, s.flip_eq_self radius i he]

theorem selectedQuads_length_le (s : LabelledResamplingState V T ι)
    (radius : ℕ) (L : List ι) : (s.selectedQuads radius L).length ≤ L.length := by
  simp only [selectedQuads, List.length_map]
  exact List.length_filter_le _ _

variable [Fintype ι]

theorem fullResample_graph_eq_applySwitches (s : LabelledResamplingState V T ι)
    (radius : ℕ) :
    (s.fullResample radius).graph =
      applySwitches (s.selectedQuads radius (Finset.univ : Finset ι).toList) s.graph :=
  s.flips_graph_eq_applySwitches radius _ (Finset.nodup_toList _)

theorem fullResample_selectedQuads_length (s : LabelledResamplingState V T ι)
    (radius : ℕ) :
    (s.selectedQuads radius (Finset.univ : Finset ι).toList).length ≤
      Nat.card (BoundaryOrientedEdge s.graph T) := by
  calc
    _ ≤ ((Finset.univ : Finset ι).toList).length := s.selectedQuads_length_le radius _
    _ = Nat.card ι := by simp
    _ = _ := Nat.card_congr s.boundary

variable [Fintype V]

/-- Bad-center inflation for the very same full labelled involution used by
the measure-preservation construction. -/
theorem fullResample_nonTreeCenters_card (s : LabelledResamplingState V T ι)
    (radius d R : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, s.graph.degree v ≤ d) :
    (nonTreeCenters (s.fullResample radius).graph R).card ≤
      (nonTreeCenters s.graph R).card +
        4 * Nat.card (BoundaryOrientedEdge s.graph T) * ((d + 1) * (d - 1) ^ R) := by
  rw [s.fullResample_graph_eq_applySwitches radius]
  apply (applySwitches_nonTreeCenters_card _ s.graph d R hd hdegree).trans
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 (s.fullResample_selectedQuads_length radius))) _

theorem fullResample_badCount_twice (s : LabelledResamplingState V T ι)
    (radius d R badCount : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, s.graph.degree v ≤ d)
    (hbad : (nonTreeCenters s.graph R).card ≤ badCount)
    (hbudget : 4 * Nat.card (BoundaryOrientedEdge s.graph T) *
      ((d + 1) * (d - 1) ^ R) ≤ badCount) :
    (nonTreeCenters (s.fullResample radius).graph R).card ≤ 2 * badCount := by
  have h := s.fullResample_nonTreeCenters_card radius d R hd hdegree
  omega

end LabelledResamplingState
end LocalLaw
