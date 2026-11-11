import LocalLaw.Theorem42

/-!
# Spectral transport from local continuity and explicit budgets

This module derives the actual weak/strict event inclusions from pointwise
analytic comparisons. It does not assume that epsilon is continuous. The two
budget-comparison fields are indispensable when the error has a branch jump.
The input family contains no transport or continuum-cover conclusion.
-/

namespace LocalLaw

/-- Analytic data before any resampling, transport, or coverage theorem is
provided. It can be used to construct a `Theorem42Inputs` package. -/
structure LocalLawFamily (X V : Type*) where
  Q : X → ℂ → ℂ
  G : X → ℂ → V → V → ℂ
  P : X → ℂ → ℂ → V → V → ℂ
  m : ℂ → ℂ
  s : ℂ → ℝ
  ε : ℂ → ℝ

namespace LocalLawFamily

variable {X V : Type*}

def weak (F : LocalLawFamily X V) (z : ℂ) (x : X) : Prop :=
  WeakLocalLawAt (F.Q x z) (F.m z) (F.s z) (F.ε z) (F.G x z) (F.P x z)

def strict (F : LocalLawFamily X V) (z : ℂ) (x : X) : Prop :=
  StrictLocalLawAt (F.Q x z) (F.m z) (F.s z) (F.ε z) (F.G x z) (F.P x z)

noncomputable def cavityDefect (F : LocalLawFamily X V) (z : ℂ) (x : X) : ℝ :=
  ‖F.Q x z - F.m z‖

noncomputable def entryDefect (F : LocalLawFamily X V) (z : ℂ) (x : X) (i j : V) : ℝ :=
  ‖F.G x z i j - F.P x z (F.Q x z) i j‖

end LocalLawFamily

/-- One analytic step from a strict estimate at w to a weak estimate at z.
Continuity and budget comparison are separate local hypotheses. -/
structure LocalLawTransportStep {X V : Type*} (F : LocalLawFamily X V)
    (structural : X → Prop) (w z : ℂ) where
  cavityConstant : ℝ
  entryConstant : ℝ
  cavityConstantNonnegative : 0 ≤ cavityConstant
  entryConstantNonnegative : 0 ≤ entryConstant
  cavityLipschitz : ∀ x, structural x →
    |F.cavityDefect z x - F.cavityDefect w x| ≤ cavityConstant * dist z w
  entryLipschitz : ∀ x, structural x → ∀ i j,
    |F.entryDefect z x i j - F.entryDefect w x i j| ≤ entryConstant * dist z w
  cavityBudget : scalarScale (F.s w) (F.ε w) / 2 + cavityConstant * dist z w ≤
    scalarScale (F.s z) (F.ε z)
  entryBudget : F.ε w / 2 + entryConstant * dist z w ≤ F.ε z

namespace LocalLawTransportStep

variable {X V : Type*} {F : LocalLawFamily X V} {structural : X → Prop} {w z : ℂ}

/-- The event inclusion is a conclusion of analytic data, rather than an
assumption in the spectral-net construction. -/
theorem strict_to_weak (S : LocalLawTransportStep F structural w z)
    (x : X) (hx : structural x) (hstrict : F.strict w x) : F.weak z x := by
  change F.cavityDefect w x ≤ scalarScale (F.s w) (F.ε w) / 2 ∧
    ∀ i j, F.entryDefect w x i j ≤ F.ε w / 2 at hstrict
  change F.cavityDefect z x ≤ scalarScale (F.s z) (F.ε z) ∧
    ∀ i j, F.entryDefect z x i j ≤ F.ε z
  constructor
  · have hd := (le_abs_self _).trans (S.cavityLipschitz x hx)
    exact (show F.cavityDefect z x ≤
      scalarScale (F.s w) (F.ε w) / 2 + S.cavityConstant * dist z w by
        linarith [hstrict.1]).trans S.cavityBudget
  · intro i j
    have hd := (le_abs_self _).trans (S.entryLipschitz x hx i j)
    exact (show F.entryDefect z x i j ≤ F.ε w / 2 + S.entryConstant * dist z w by
      linarith [hstrict.2 i j]).trans S.entryBudget

end LocalLawTransportStep

/-- A reverse-triangle estimate for a difference of two complex-valued
observables. It converts component estimates into defect continuity. -/
theorem difference_norm_variation (a b c d : ℂ) :
    |‖a - b‖ - ‖c - d‖| ≤ ‖a - c‖ + ‖b - d‖ := by
  calc
    |‖a - b‖ - ‖c - d‖| ≤ ‖(a - b) - (c - d)‖ :=
      abs_norm_sub_norm_le _ _
    _ = ‖(a - c) - (b - d)‖ := by congr 1; ring
    _ ≤ ‖a - c‖ + ‖b - d‖ := norm_sub_le _ _

namespace LocalLawTransportStep

variable {X V : Type*}

/-- Build a step from estimates on Q, m, G and the full boundary model
P(z,Q(z)). No continuity of the error-budget functions is assumed. -/
noncomputable def ofComponents (F : LocalLawFamily X V) (structural : X → Prop)
    (w z : ℂ) (KQ Km KG KP : ℝ)
    (hKQ : 0 ≤ KQ) (hKm : 0 ≤ Km) (hKG : 0 ≤ KG) (hKP : 0 ≤ KP)
    (hQ : ∀ x, structural x → ‖F.Q x z - F.Q x w‖ ≤ KQ * dist z w)
    (hm : ‖F.m z - F.m w‖ ≤ Km * dist z w)
    (hG : ∀ x, structural x → ∀ i j,
      ‖F.G x z i j - F.G x w i j‖ ≤ KG * dist z w)
    (hP : ∀ x, structural x → ∀ i j,
      ‖F.P x z (F.Q x z) i j - F.P x w (F.Q x w) i j‖ ≤ KP * dist z w)
    (hbudgetQ : scalarScale (F.s w) (F.ε w) / 2 + (KQ + Km) * dist z w ≤
      scalarScale (F.s z) (F.ε z))
    (hbudgetE : F.ε w / 2 + (KG + KP) * dist z w ≤ F.ε z) :
    LocalLawTransportStep F structural w z where
  cavityConstant := KQ + Km
  entryConstant := KG + KP
  cavityConstantNonnegative := add_nonneg hKQ hKm
  entryConstantNonnegative := add_nonneg hKG hKP
  cavityLipschitz x hx := by
    have hnorm := difference_norm_variation (F.Q x z) (F.m z) (F.Q x w) (F.m w)
    exact hnorm.trans (by nlinarith [hQ x hx])
  entryLipschitz x hx i j := by
    have hnorm := difference_norm_variation (F.G x z i j) (F.P x z (F.Q x z) i j)
      (F.G x w i j) (F.P x w (F.Q x w) i j)
    exact hnorm.trans (by nlinarith [hG x hx i j, hP x hx i j])
  cavityBudget := hbudgetQ
  entryBudget := hbudgetE

end LocalLawTransportStep

/-- Ordered spectral transport from a deterministic anchor or an explicitly
chosen earlier node with a proved local analytic step. -/
theorem ordered_transport_from_steps {X V : Type*} {T : ℕ}
    (F : LocalLawFamily X V) (structural : X → Prop) (net : Fin T → ℂ)
    (steps : ∀ t,
      (∀ x, structural x → F.weak (net t) x) ∨
      ∃ p : Fin T, p < t ∧ Nonempty
        (LocalLawTransportStep F structural (net p) (net t))) :
    ∀ t x, structural x → (∀ k, k < t → F.strict (net k) x) →
      F.weak (net t) x := by
  intro t x hx previous
  rcases steps t with anchor | ⟨p, hpt, ⟨step⟩⟩
  · exact anchor x hx
  · exact step.strict_to_weak x hx (previous p hpt)

/-- A selected finite-net center and its local budget comparison imply a
continuum cover, even for discontinuous error budgets. -/
theorem continuum_cover_from_steps {X V : Type*} {T : ℕ}
    (F : LocalLawFamily X V) (structural : X → Prop) (net : Fin T → ℂ)
    (domain : Set ℂ)
    (cover : ∀ z ∈ domain, ∃ t : Fin T,
      Nonempty (LocalLawTransportStep F structural (net t) z)) :
    ∀ x, structural x → (∀ t, F.strict (net t) x) →
      ∀ z ∈ domain, F.weak z x := by
  intro x hx strict z hz
  obtain ⟨t, ⟨step⟩⟩ := cover z hz
  exact step.strict_to_weak x hx (strict t)

end LocalLaw
