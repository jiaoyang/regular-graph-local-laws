import LocalLaw.SourceMinorPerturbation
import LocalLaw.AdmissibleSampleGeometry
import LocalLaw.GuardedObservationBias

/-!
# Accepted sampled first endpoints stay in the new physical guard

The sampled first endpoint is the third coordinate of a switching
quadruple. It is unchanged by both its inverse and every other coordinate
flip. Selector invariance therefore puts the same actual vertex far from
all new boundary labels, giving its new deleted pivot from guarded caps.
-/

noncomputable section
namespace LocalLaw
local instance newSampleGuardCapsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type*} {T : Set V} {ι : Type*}

theorem flip_sampledOutsideFirst (s : LabelledResamplingState V T ι) (selector : ℕ) (i j : ι) :
    (s.flip selector i).sampledOutsideFirst j = s.sampledOutsideFirst j := by
  by_cases hi : s.Eligible selector i
  · rw [s.flip_eq_perform selector i hi]
    apply Subtype.ext
    change ((s.perform selector i hi.1 hi.2).quad j).c = (s.quad j).c
    rw [s.perform_quad selector i j hi.1 hi.2]
    split_ifs with h
    · subst j; rfl
    · rfl
  · rw [s.flip_eq_self selector i hi]

theorem flips_sampledOutsideFirst (s : LabelledResamplingState V T ι) (selector : ℕ)
    (L : List ι) (j : ι) : (s.flips selector L).sampledOutsideFirst j = s.sampledOutsideFirst j := by
  induction L generalizing s with
  | nil => rfl
  | cons i L ih => exact (ih (s.flip selector i)).trans (s.flip_sampledOutsideFirst selector i j)

variable [Fintype ι]

theorem fullResample_sampledOutsideFirst (s : LabelledResamplingState V T ι) (selector : ℕ) (i : ι) :
    (s.fullResample selector).sampledOutsideFirst i = s.sampledOutsideFirst i :=
  s.flips_sampledOutsideFirst selector _ i

theorem fullResample_first_mem_new_guard (s : LabelledResamplingState V T ι)
    (selector : ℕ) (hselector : 1 ≤ selector) (i : ι) (hi : s.Eligible selector i) :
    (s.sampledOutsideFirst i).val ∈ boundaryFarGuard (s.fullResample selector).graph T (selector - 1) := by
  let t := s.fullResample selector
  have hit : t.Eligible selector i := (s.fullResample_eligible selector i).mpr hi
  have hfar := t.admissibleSampleVertex_far_boundary selector ⟨i, hit⟩
  have hdiv : (4 * selector) / 4 = selector := by omega
  have hsafe := source_far_edge_guard t.graph T (4 * selector) (by omega)
    (t.samples (t.boundary i)) (by simpa only [hdiv] using hfar)
  have hb : (t.sampledOutsideFirst i).val ∈ boundaryFarGuard t.graph T (selector - 1) := by
    simpa only [hdiv] using hsafe.1
  rw [s.fullResample_sampledOutsideFirst selector i] at hb
  exact hb

end LabelledResamplingState

namespace LabelledResamplingState
variable {N d : ℕ} {T : Set (Fin N)} {ι : Type*} [Fintype ι]

theorem fullResample_first_pivot_of_guardedCaps (s : LabelledResamplingState (Fin N) T ι)
    (hregular : s.graph.IsRegularOfDegree d) (selector : ℕ) (hselector : 1 ≤ selector)
    (i : ι) (hi : s.Eligible selector i)
    (z : ℂ) (C P : ℝ)
    (caps : RegularGraph.GuardedDeletionCaps
      (⟨(s.fullResample selector).graph, s.fullResample_regular selector hregular⟩ : RegularGraph N d)
      T (boundaryFarGuard (s.fullResample selector).graph T (selector - 1)) z C P) :
    ‖(green (normalizedAdjacency (outsideGraph (s.fullResample selector).graph T) d) z
      (s.sampledOutsideFirst i) (s.sampledOutsideFirst i))⁻¹‖ ≤ P := by
  let g : RegularGraph N d := ⟨(s.fullResample selector).graph, s.fullResample_regular selector hregular⟩
  let A := boundaryFarGuard g.graph T (selector - 1)
  let b := s.sampledOutsideFirst i
  have hb : b.val ∈ A := s.fullResample_first_mem_new_guard selector hselector i hi
  have hh := guardedDeletedGreen_of_safe g.H T A (boundaryFarGuard_subset_complement g.graph T _)
    z ⟨b.val, hb⟩ ⟨b.val, hb⟩
  have hmatrix : g.H.submatrix (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)
      (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N) =
      normalizedAdjacency (outsideGraph g.graph T) d := (normalizedAdjacency_induce g.graph d Tᶜ).symm
  rw [hmatrix] at hh
  change guardedDeletedGreen g.H T A z b.val b.val = green
    (normalizedAdjacency (outsideGraph g.graph T) d) z b b at hh
  have hp := caps.guarded_pivot b.val
  change ‖(guardedDeletedGreen g.H T A z b.val b.val)⁻¹‖ ≤ P at hp
  rw [hh] at hp
  exact hp

end LabelledResamplingState
end LocalLaw
