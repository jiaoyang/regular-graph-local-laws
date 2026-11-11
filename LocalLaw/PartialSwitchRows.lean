import LocalLaw.PartialEndpointMasks
import LocalLaw.SourceOutsideSwitchFormula

/-! # Literal exterior adjacency rows at accepted switching triples -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance partialSwitchRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type} [Fintype ι]

theorem fullResample_eligible_exterior_incident (s : LabelledResamplingState V T ι)
    (selector:ℕ) (i:s.AdmissibleSampleIndex selector) (x y:V)
    (hx:x∈(s.quad i.val).exterior) :
    (s.fullResample selector).graph.Adj x y↔((s.quad i.val).apply s.graph).Adj x y := by
  apply s.fullResample_incident_eq_single selector i.val i.property (s.quad i.val).exterior
    (sampledSwitching_exterior_disjoint s.graph T s.samples (s.boundary i.val)) _ hx
  intro j hji
  exact isolation_exterior_disjoint s.graph T selector s.samples (s.boundary i.val) (s.boundary j)
    i.property.2 (fun h=>hji (s.boundary.injective h))

theorem fullResample_outside_boundary_row (s : LabelledResamplingState V T ι)
    (selector:ℕ) (i:s.AdmissibleSampleIndex selector) (y:(Tᶜ:Set V)) :
    (outsideGraph (s.fullResample selector).graph T).Adj (s.admissibleBoundaryVertex selector i) y↔
      (outsideGraph s.graph T).Adj (s.admissibleBoundaryVertex selector i) y∨
        y=s.admissibleSampleVertex selector i := by
  have hi:=sampledSwitching_admissible s.graph T selector s.samples (s.boundary i.val) i.property.1 i.property.2
  have hrow:=s.fullResample_eligible_exterior_incident selector i (s.quad i.val).b y.val (Or.inl rfl)
  have hy:y.val≠(s.quad i.val).a:=fun h=>y.property
    (h ▸ sampledSwitching_root_mem s.graph T s.samples (s.boundary i.val))
  rw [show ((s.quad i.val).apply s.graph).Adj (s.quad i.val).b y.val↔
    (s.graph.Adj (s.quad i.val).b y.val∧y.val≠(s.quad i.val).a)∨y.val=(s.quad i.val).c
      from hi.adj_b y.val] at hrow
  simp only [Subtype.ext_iff]
  change (s.fullResample selector).graph.Adj (s.quad i.val).b y.val↔
    s.graph.Adj (s.quad i.val).b y.val∨y.val=(s.quad i.val).c
  exact hrow.trans (or_congr (and_iff_left hy) Iff.rfl)

theorem fullResample_outside_first_row (s : LabelledResamplingState V T ι)
    (selector:ℕ) (i:s.AdmissibleSampleIndex selector) (y:(Tᶜ:Set V)) :
    (outsideGraph (s.fullResample selector).graph T).Adj (s.admissibleSampleVertex selector i) y↔
      ((outsideGraph s.graph T).Adj (s.admissibleSampleVertex selector i) y∧
        y≠s.admissibleSecondVertex selector i)∨y=s.admissibleBoundaryVertex selector i := by
  have hi:=sampledSwitching_admissible s.graph T selector s.samples (s.boundary i.val) i.property.1 i.property.2
  have hrow:=s.fullResample_eligible_exterior_incident selector i (s.quad i.val).c y.val (Or.inr (Or.inl rfl))
  rw [show ((s.quad i.val).apply s.graph).Adj (s.quad i.val).c y.val↔
    (s.graph.Adj (s.quad i.val).c y.val∧y.val≠(s.quad i.val).d)∨y.val=(s.quad i.val).b
      from hi.adj_c y.val] at hrow
  simp only [ne_eq,Subtype.ext_iff]
  exact hrow

theorem fullResample_outside_second_row (s : LabelledResamplingState V T ι)
    (selector:ℕ) (i:s.AdmissibleSampleIndex selector) (y:(Tᶜ:Set V)) :
    (outsideGraph (s.fullResample selector).graph T).Adj (s.admissibleSecondVertex selector i) y↔
      (outsideGraph s.graph T).Adj (s.admissibleSecondVertex selector i) y∧
        y≠s.admissibleSampleVertex selector i := by
  have hi:=sampledSwitching_admissible s.graph T selector s.samples (s.boundary i.val) i.property.1 i.property.2
  have hrow:=s.fullResample_eligible_exterior_incident selector i (s.quad i.val).d y.val (Or.inr (Or.inr rfl))
  have hy:y.val≠(s.quad i.val).a:=fun h=>y.property
    (h ▸ sampledSwitching_root_mem s.graph T s.samples (s.boundary i.val))
  rw [show ((s.quad i.val).apply s.graph).Adj (s.quad i.val).d y.val↔
    (s.graph.Adj (s.quad i.val).d y.val∧y.val≠(s.quad i.val).c)∨y.val=(s.quad i.val).a
      from hi.adj_d y.val] at hrow
  simp only [ne_eq,Subtype.ext_iff]
  change (s.fullResample selector).graph.Adj (s.quad i.val).d y.val↔
    s.graph.Adj (s.quad i.val).d y.val∧y.val≠(s.quad i.val).c
  exact hrow.trans (or_iff_left hy)

theorem fullResample_outside_boundary_indicator (s : LabelledResamplingState V T ι)
    (selector:ℕ) (i:s.AdmissibleSampleIndex selector) (y:(Tᶜ:Set V)) :
    (if (outsideGraph (s.fullResample selector).graph T).Adj (s.admissibleBoundaryVertex selector i) y then (1:ℂ) else 0)-
      (if (outsideGraph s.graph T).Adj (s.admissibleBoundaryVertex selector i) y then 1 else 0)=
        if y=s.admissibleSampleVertex selector i then 1 else 0 := by
  rw [s.fullResample_outside_boundary_row selector i y]
  have hi:=sampledSwitching_admissible s.graph T selector s.samples (s.boundary i.val) i.property.1 i.property.2
  by_cases hy:y=s.admissibleSampleVertex selector i
  · subst y
    have hh:¬(outsideGraph s.graph T).Adj (s.admissibleBoundaryVertex selector i) (s.admissibleSampleVertex selector i):=hi.new_bc
    simp [hh]
  · simp [hy]

theorem fullResample_outside_first_indicator (s : LabelledResamplingState V T ι)
    (selector:ℕ) (i:s.AdmissibleSampleIndex selector) (y:(Tᶜ:Set V)) :
    (if (outsideGraph (s.fullResample selector).graph T).Adj (s.admissibleSampleVertex selector i) y then (1:ℂ) else 0)-
      (if (outsideGraph s.graph T).Adj (s.admissibleSampleVertex selector i) y then 1 else 0)=
        (if y=s.admissibleBoundaryVertex selector i then 1 else 0)-
          (if y=s.admissibleSecondVertex selector i then 1 else 0) := by
  rw [s.fullResample_outside_first_row selector i y]
  have hi:=sampledSwitching_admissible s.graph T selector s.samples (s.boundary i.val) i.property.1 i.property.2
  have hac:s.admissibleBoundaryVertex selector i≠s.admissibleSecondVertex selector i:=
    fun h=>hi.bd_ne (congrArg Subtype.val h)
  by_cases ha:y=s.admissibleBoundaryVertex selector i
  · subst y
    have hh:¬(outsideGraph s.graph T).Adj (s.admissibleSampleVertex selector i) (s.admissibleBoundaryVertex selector i):=
      fun h=>hi.new_bc h.symm
    simp [hh,hac]
  · by_cases hc:y=s.admissibleSecondVertex selector i
    · subst y
      have hh:(outsideGraph s.graph T).Adj (s.admissibleSampleVertex selector i) (s.admissibleSecondVertex selector i):=hi.old_cd
      simp [hh,ha]
    · simp [ha,hc]

theorem fullResample_outside_second_indicator (s : LabelledResamplingState V T ι)
    (selector:ℕ) (i:s.AdmissibleSampleIndex selector) (y:(Tᶜ:Set V)) :
    (if (outsideGraph (s.fullResample selector).graph T).Adj (s.admissibleSecondVertex selector i) y then (1:ℂ) else 0)-
      (if (outsideGraph s.graph T).Adj (s.admissibleSecondVertex selector i) y then 1 else 0)=
        -(if y=s.admissibleSampleVertex selector i then 1 else 0) := by
  rw [s.fullResample_outside_second_row selector i y]
  have hi:=sampledSwitching_admissible s.graph T selector s.samples (s.boundary i.val) i.property.1 i.property.2
  by_cases hy:y=s.admissibleSampleVertex selector i
  · subst y
    have hh:(outsideGraph s.graph T).Adj (s.admissibleSecondVertex selector i) (s.admissibleSampleVertex selector i):=hi.old_cd.symm
    simp [hh]
  · simp [hy]

end LabelledResamplingState
end LocalLaw
