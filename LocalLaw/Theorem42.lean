import LocalLaw.Assembly
import LocalLaw.LocalClosure
import LocalLaw.SpectralGap
import LocalLaw.Semicircle
import LocalLaw.ProbabilityBudget

/-!
# Generalized Theorem 4.2

This is a complete conditional local-law theorem with actual weak/strict
cavity and entrywise events. Deterministic tightening is derived from the
finite cavity certificates and the proved scalar closure theorem. The
model-specific resampling estimates and spectral-net inclusions are inputs.
It is not a proof of the random-regular-graph estimates in Sections 5 and 6.
-/

open scoped BigOperators

namespace LocalLaw

/-- Scalar parameters and quantitative hypotheses needed at one net node.
The weak-event prior has constant one. -/
structure ClosureBudget (z m : ℂ) (s ε : ℝ) where
  depth : ℕ
  L : ℝ
  gapConstant : ℝ
  spectralRadius : ℝ
  U : ℝ
  V : ℝ
  rowBase : ℝ
  rowFeedback : ℝ
  cavityError : ℝ
  exceptionalCavity : ℝ
  root : m ^ 2 + z * m + 1 = 0
  rootNorm : ‖m‖ ≤ 1
  spectralBound : ‖z‖ ≤ spectralRadius
  small : (depth : ℝ) * scalarScale s ε ≤ 1 / 2
  nonresonant : 1 / 2 ≤ ‖cavitySum m depth‖
  scalePositive : 0 < s
  errorPositive : 0 < ε
  gapNonnegative : 0 ≤ gapConstant
  UNonnegative : 0 ≤ U
  VNonnegative : 0 ≤ V
  large : 2 ≤ L
  gapLower : Real.sqrt s ≤ ‖m⁻¹ - m‖
  gapUpper : ‖m⁻¹ - m‖ ≤ gapConstant * Real.sqrt s
  regime : ε ≤ s / L ∨ L ^ 3 * s ≤ ε
  cavityErrorNonnegative : 0 ≤ cavityError
  rowBaseBound : rowBase ≤ U * ε / L
  rowFeedbackBound : rowFeedback ≤ V * L
  scalarLarge : 2 * localClosureConstant spectralRadius gapConstant ≤ L
  rowLarge : 2 * (U + V * (localClosureConstant spectralRadius gapConstant +
    localClosureConstant spectralRadius gapConstant ^ 2)) ≤ L

namespace ClosureBudget

/-- Build a closure budget at the actual semicircle edge scale κ+η. The
root-gap constants and positivity of the spectral scale are proved from the
quadratic equation and positive imaginary part, rather than assumed. -/
noncomputable def ofSpectral
    (z m : ℂ) (ε : ℝ) (depth : ℕ) (L B U V rowBase rowFeedback cavityError M₀ : ℝ)
    (hm : m ^ 2 + z * m + 1 = 0) (hmnorm : ‖m‖ ≤ 1)
    (hz : 0 < z.im) (hB : ‖z‖ ≤ B)
    (hsmall : (depth : ℝ) * scalarScale (spectralScale z) ε ≤ 1 / 2)
    (hnonresonant : 1 / 2 ≤ ‖cavitySum m depth‖)
    (hε : 0 < ε) (hU : 0 ≤ U) (hV : 0 ≤ V) (hL : 2 ≤ L)
    (hregime : ε ≤ spectralScale z / L ∨ L ^ 3 * spectralScale z ≤ ε)
    (ht : 0 ≤ cavityError) (hu : rowBase ≤ U * ε / L)
    (hv : rowFeedback ≤ V * L)
    (hscalar : 2 * localClosureConstant B (Real.sqrt (B + 2)) ≤ L)
    (hrow : 2 * (U + V * (localClosureConstant B (Real.sqrt (B + 2)) +
      localClosureConstant B (Real.sqrt (B + 2)) ^ 2)) ≤ L) :
    ClosureBudget z m (spectralScale z) ε where
  depth := depth
  L := L
  gapConstant := Real.sqrt (B + 2)
  spectralRadius := B
  U := U
  V := V
  rowBase := rowBase
  rowFeedback := rowFeedback
  cavityError := cavityError
  exceptionalCavity := M₀
  root := hm
  rootNorm := hmnorm
  spectralBound := hB
  small := hsmall
  nonresonant := hnonresonant
  scalePositive := spectralScale_pos hz
  errorPositive := hε
  gapNonnegative := Real.sqrt_nonneg _
  UNonnegative := hU
  VNonnegative := hV
  large := hL
  gapLower := (cavity_root_gap_bounds hm hz hB).1
  gapUpper := (cavity_root_gap_bounds hm hz hB).2
  regime := hregime
  cavityErrorNonnegative := ht
  rowBaseBound := hu
  rowFeedbackBound := hv
  scalarLarge := hscalar
  rowLarge := hrow


/-- A fully specified reference root: the quadratic equation, root norm and
gap inequalities are discharged by Semicircle and SpectralGap. The remaining
conditions are the finite-N error and row-feedback budgets of the instance. -/
noncomputable def ofSemicircle
    (z : ℂ) (ε : ℝ) (depth : ℕ) (L B U V rowBase rowFeedback cavityError M₀ : ℝ)
    (hz : 0 < z.im) (hB : ‖z‖ ≤ B)
    (hsmall : (depth : ℝ) * scalarScale (spectralScale z) ε ≤ 1 / 2)
    (hnonresonant : 1 / 2 ≤ ‖cavitySum (semicircleRoot z) depth‖)
    (hε : 0 < ε) (hU : 0 ≤ U) (hV : 0 ≤ V) (hL : 2 ≤ L)
    (hregime : ε ≤ spectralScale z / L ∨ L ^ 3 * spectralScale z ≤ ε)
    (ht : 0 ≤ cavityError) (hu : rowBase ≤ U * ε / L)
    (hv : rowFeedback ≤ V * L)
    (hscalar : 2 * localClosureConstant B (Real.sqrt (B + 2)) ≤ L)
    (hrow : 2 * (U + V * (localClosureConstant B (Real.sqrt (B + 2)) +
      localClosureConstant B (Real.sqrt (B + 2)) ^ 2)) ≤ L) :
    ClosureBudget z (semicircleRoot z) (spectralScale z) ε :=
  ofSpectral z (semicircleRoot z) ε depth L B U V rowBase rowFeedback cavityError M₀
    (semicircleRoot_equation z) (semicircleRoot_norm_le_one z) hz hB hsmall
    hnonresonant hε hU hV hL hregime ht hu hv hscalar hrow

end ClosureBudget

section ActualEvents

variable {V : Type*}

/-- Weak event: a cavity-variable prior and approximation at the random
boundary parameter. -/
def WeakLocalLawAt (q m : ℂ) (s ε : ℝ)
    (G : V → V → ℂ) (P : ℂ → V → V → ℂ) : Prop :=
  ‖q - m‖ ≤ scalarScale s ε ∧ ∀ i j, ‖G i j - P q i j‖ ≤ ε

/-- Strict event with both error budgets divided by two. -/
def StrictLocalLawAt (q m : ℂ) (s ε : ℝ)
    (G : V → V → ℂ) (P : ℂ → V → V → ℂ) : Prop :=
  ‖q - m‖ ≤ scalarScale s ε / 2 ∧ ∀ i j, ‖G i j - P q i j‖ ≤ ε / 2

variable [Fintype V] [DecidableEq V]

/-- One center supplies its local cavity and row certificates. The cavity
estimate is required only outside the explicitly retained exceptional set. -/
def CavityRowCertificate (q m z : ℂ) (s ε : ℝ)
    (D : ClosureBudget z m s ε) (G : V → V → ℂ) (P : ℂ → V → V → ℂ)
    (cavity : V → ℂ) (bad : Finset V) (i : V) : Prop :=
  (i ∉ bad → ‖cavity i - cavityIterate z q D.depth‖ ≤ D.cavityError) ∧
  ∀ j, ‖G i j - P q i j‖ ≤ D.rowBase + D.rowFeedback *
    (Real.sqrt s * ‖q - m‖ + ‖q - m‖ ^ 2)

/-- Concrete local certificate closure, rather than an assumed event
inclusion. It combines sparse cavity averaging, exact recursion, scalar
stability, and row feedback. -/
theorem actual_local_certificate_closure
    (q m z : ℂ) (s ε : ℝ) (D : ClosureBudget z m s ε)
    (G : V → V → ℂ) (P : ℂ → V → V → ℂ)
    (cavity : V → ℂ) (bad : Finset V) (hcard : 0 < Fintype.card V)
    (average : q = (Fintype.card V : ℝ)⁻¹ • ∑ i, cavity i)
    (exceptional : ∀ i, i ∈ bad →
      ‖cavity i - cavityIterate z q D.depth‖ ≤ D.exceptionalCavity)
    (absorption : D.cavityError + ((bad.card : ℝ) / (Fintype.card V : ℝ)) *
      D.exceptionalCavity ≤ ε / D.L ^ 2)
    (weak : WeakLocalLawAt q m s ε G P)
    (certificates : ∀ i, CavityRowCertificate q m z s ε D G P cavity bad i) :
    StrictLocalLawAt q m s ε G P := by
  have hsmall : (D.depth : ℝ) * ‖q - m‖ ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left weak.1 (Nat.cast_nonneg _)).trans D.small
  have hresidual : ‖q - cavityIterate z q D.depth‖ ≤ ε / D.L ^ 2 :=
    cavity_certificate_residual cavity q z D.depth bad D.cavityError
      D.exceptionalCavity ε D.L hcard D.cavityErrorNonnegative average
      (fun i hi => (certificates i).1 hi) exceptional absorption
  have result := local_certificate_closure q m z D.depth s ε D.L 1
    D.gapConstant D.spectralRadius D.U D.V D.rowBase D.rowFeedback
    (fun ij : V × V => ‖G ij.1 ij.2 - P q ij.1 ij.2‖)
    D.root D.rootNorm D.spectralBound hsmall D.nonresonant D.scalePositive
    D.errorPositive (by norm_num) D.gapNonnegative D.UNonnegative D.VNonnegative
    D.large (by simpa using D.large) D.gapLower D.gapUpper
    (by simpa using weak.1) hresidual D.regime
    (fun ij => (certificates ij.1).2 ij.2) D.rowBaseBound D.rowFeedbackBound
    D.scalarLarge D.rowLarge
  exact ⟨result.1, fun i j => result.2 (i, j)⟩

end ActualEvents

/-- Visible, model-specific contract for the generalized theorem. It gives
local resampling estimates against the actual weak event and actual analytic
certificates. The deterministic strict-event closure is deliberately absent:
it is proved below from these data. -/
structure Theorem42Inputs (X V : Type) [Fintype X] [Fintype V]
    [DecidableEq V] (T : ℕ) where
  weight : X → ℝ
  nonnegative : ∀ x, 0 ≤ weight x
  normalized : ∑ x, weight x = 1
  structural : X → Prop
  structuralPositive : 0 < eventMass weight structural
  vertexPositive : 0 < Fintype.card V
  net : Fin T → ℂ
  domain : Set ℂ
  Q : X → ℂ → ℂ
  G : X → ℂ → V → V → ℂ
  P : X → ℂ → ℂ → V → V → ℂ
  m : ℂ → ℂ
  md : ℂ → ℂ
  s : ℂ → ℝ
  ε : ℂ → ℝ
  budget : ∀ t, ClosureBudget (net t) (m (net t)) (s (net t)) (ε (net t))
  cavity : X → Fin T → V → ℂ
  badCavity : X → Fin T → Finset V
  cavityAverage : ∀ t x, structural x →
    Q x (net t) = (Fintype.card V : ℝ)⁻¹ • ∑ i, cavity x t i
  exceptionalCavity : ∀ t x, structural x →
    WeakLocalLawAt (Q x (net t)) (m (net t)) (s (net t)) (ε (net t))
      (G x (net t)) (P x (net t)) → ∀ i, i ∈ badCavity x t →
        ‖cavity x t i - cavityIterate (net t) (Q x (net t)) (budget t).depth‖
          ≤ (budget t).exceptionalCavity
  cavityAbsorption : ∀ t x, structural x →
    WeakLocalLawAt (Q x (net t)) (m (net t)) (s (net t)) (ε (net t))
      (G x (net t)) (P x (net t)) →
    (budget t).cavityError + (((badCavity x t).card : ℝ) / (Fintype.card V : ℝ)) *
      (budget t).exceptionalCavity ≤ ε (net t) / (budget t).L ^ 2
  intermediate : Fin T → V → X → Prop
  extension : Fin T → V → ReversibleExtension X weight
  firstBudget : Fin T → V → ℝ
  secondBudget : Fin T → V → ℝ
  firstEstimate : ∀ t o,
    eventMass (extension t o).weight (fun ω =>
      (structural ((extension t o).project ω) ∧
        WeakLocalLawAt (Q ((extension t o).project ω) (net t)) (m (net t))
          (s (net t)) (ε (net t)) (G ((extension t o).project ω) (net t))
          (P ((extension t o).project ω) (net t))) ∧
      ¬ intermediate t o ((extension t o).project ((extension t o).switching ω)))
        ≤ firstBudget t o
  secondEstimate : ∀ t o,
    eventMass (extension t o).weight (fun ω =>
      intermediate t o ((extension t o).project ω) ∧
      ¬ CavityRowCertificate
        (Q ((extension t o).project ((extension t o).switching ω)) (net t))
        (m (net t)) (net t) (s (net t)) (ε (net t)) (budget t)
        (G ((extension t o).project ((extension t o).switching ω)) (net t))
        (P ((extension t o).project ((extension t o).switching ω)) (net t))
        (cavity ((extension t o).project ((extension t o).switching ω)) t)
        (badCavity ((extension t o).project ((extension t o).switching ω)) t) o)
          ≤ secondBudget t o
  transport : ∀ t x, structural x →
    (∀ k, k < t → StrictLocalLawAt (Q x (net k)) (m (net k))
      (s (net k)) (ε (net k)) (G x (net k)) (P x (net k))) →
    WeakLocalLawAt (Q x (net t)) (m (net t)) (s (net t)) (ε (net t))
      (G x (net t)) (P x (net t))
  cover : ∀ x, structural x →
    (∀ t, StrictLocalLawAt (Q x (net t)) (m (net t)) (s (net t)) (ε (net t))
      (G x (net t)) (P x (net t))) → ∀ z ∈ domain,
    WeakLocalLawAt (Q x z) (m z) (s z) (ε z) (G x z) (P x z)
  modelLipschitz : ℂ → ℝ
  modelLipschitzNonnegative : ∀ z ∈ domain, 0 ≤ modelLipschitz z
  sensitivity : ∀ z ∈ domain, ∀ x, structural x →
    WeakLocalLawAt (Q x z) (m z) (s z) (ε z) (G x z) (P x z) →
    ∀ i j, ‖P x z (Q x z) i j - P x z (m z) i j‖ ≤
      modelLipschitz z * dist (Q x z) (m z)
  badDiagonal : X → ℂ → Finset V
  diagonalBound : ℂ → ℝ
  tree : ∀ z ∈ domain, ∀ x, structural x →
    WeakLocalLawAt (Q x z) (m z) (s z) (ε z) (G x z) (P x z) →
    ∀ i, i ∉ badDiagonal x z → P x z (m z) i i = md z
  exceptionalDiagonal : ∀ z ∈ domain, ∀ x, structural x →
    WeakLocalLawAt (Q x z) (m z) (s z) (ε z) (G x z) (P x z) →
    ∀ i, i ∈ badDiagonal x z → ‖P x z (m z) i i - md z‖ ≤ diagonalBound z

namespace Theorem42Inputs

variable {X V : Type} [Fintype X] [Fintype V] [DecidableEq V] {T : ℕ}

/-- The assembly structure is constructed from actual analytic certificates;
its deterministic closure field is proved, not provided by the caller. -/
noncomputable def assembly (D : Theorem42Inputs X V T) : AssemblyInputs X V ℂ T where
  weight := D.weight
  nonnegative := D.nonnegative
  normalized := D.normalized
  structural := D.structural
  structuralPositive := D.structuralPositive
  weak t x := D.structural x ∧ WeakLocalLawAt (D.Q x (D.net t)) (D.m (D.net t))
    (D.s (D.net t)) (D.ε (D.net t)) (D.G x (D.net t)) (D.P x (D.net t))
  strict t x := D.structural x ∧ StrictLocalLawAt (D.Q x (D.net t)) (D.m (D.net t))
    (D.s (D.net t)) (D.ε (D.net t)) (D.G x (D.net t)) (D.P x (D.net t))
  centers _ := Finset.univ
  intermediate := D.intermediate
  certificate t o x := CavityRowCertificate (D.Q x (D.net t)) (D.m (D.net t))
    (D.net t) (D.s (D.net t)) (D.ε (D.net t)) (D.budget t)
    (D.G x (D.net t)) (D.P x (D.net t)) (D.cavity x t) (D.badCavity x t) o
  extension := D.extension
  firstBudget := D.firstBudget
  secondBudget := D.secondBudget
  firstEstimate t o _ := D.firstEstimate t o
  secondEstimate t o _ := D.secondEstimate t o
  closure t x hx certificates := ⟨hx.1,
    actual_local_certificate_closure _ _ _ _ _ (D.budget t) _ _ _ _
      D.vertexPositive (D.cavityAverage t x hx.1)
      (D.exceptionalCavity t x hx.1 hx.2) (D.cavityAbsorption t x hx.1 hx.2)
      hx.2 (fun o => certificates o (Finset.mem_univ _))⟩
  transport t x hx previous := ⟨hx, D.transport t x hx (fun k hk => (previous k hk).2)⟩
  domain := D.domain
  regular z x := D.structural x ∧
    WeakLocalLawAt (D.Q x z) (D.m z) (D.s z) (D.ε z) (D.G x z) (D.P x z)
  cover x hx previous z hz :=
    ⟨hx, D.cover x hx (fun t => (previous t).2) z hz⟩

/-- The proved generalized Theorem 4.2. The entry error is exactly
`ε + K_model * (ε / sqrt(s+ε))`; the trace error retains the density of
exceptional diagonals. The conditional failure budget is the sum of the two
local resampling errors over every net node and every center, divided by the
positive structural-event probability. -/
theorem generalized_theorem_4_2 (D : Theorem42Inputs X V T) :
    eventMass D.weight (fun x => D.structural x ∧ ¬ ∀ z ∈ D.domain,
      EntryTraceAt D.G (fun x z => D.P x z (D.m z)) D.md D.badDiagonal
        (fun z => D.ε z + D.modelLipschitz z * scalarScale (D.s z) (D.ε z))
        D.diagonalBound z x) / eventMass D.weight D.structural ≤
      (∑ t, ∑ o, (D.firstBudget t o + D.secondBudget t o)) /
        eventMass D.weight D.structural := by
  apply AssemblyInputs.uniform_entry_trace_local_law D.assembly D.G D.P D.Q D.m D.md
    D.badDiagonal D.ε (fun z => scalarScale (D.s z) (D.ε z))
    D.modelLipschitz D.diagonalBound D.modelLipschitzNonnegative D.vertexPositive
  · intro z hz x hx
    exact hx.2.2
  · intro z hz x hx
    simpa only [Complex.dist_eq] using hx.2.1
  · intro z hz x hx
    exact D.sensitivity z hz x hx.1 hx.2
  · intro z hz x hx
    exact D.tree z hz x hx.1 hx.2
  · intro z hz x hx
    exact D.exceptionalDiagonal z hz x hx.1 hx.2


/-- Simplified rate event with one coefficient for entries and one for the
empirical Stieltjes transform. -/
def RateLocalLawAt (D : Theorem42Inputs X V T) (Centry Ctrace : ℝ)
    (z : ℂ) (x : X) : Prop :=
  (∀ i j, ‖D.G x z i j - D.P x z (D.m z) i j‖ ≤
    Centry * scalarScale (D.s z) (D.ε z)) ∧
  ‖(Fintype.card V : ℝ)⁻¹ • ∑ i, (D.G x z i i - D.md z)‖ ≤
    Ctrace * scalarScale (D.s z) (D.ε z)

/-- The exact Theorem-4.2-shaped rate on a bounded control domain. The three
explicit absorption hypotheses convert ε, boundary sensitivity, and sparse
exceptional diagonals to the common scale ε/sqrt(s+ε). -/
theorem generalized_theorem_4_2_rate (D : Theorem42Inputs X V T)
    (A₀ K₀ D₀ : ℝ)
    (hs : ∀ z ∈ D.domain, 0 < D.s z)
    (hε : ∀ z ∈ D.domain, 0 ≤ D.ε z)
    (width : ∀ z ∈ D.domain, Real.sqrt (D.s z + D.ε z) ≤ A₀)
    (model : ∀ z ∈ D.domain, D.modelLipschitz z ≤ K₀)
    (sparse : ∀ z ∈ D.domain, ∀ x, D.structural x →
      (((D.badDiagonal x z).card : ℝ) / (Fintype.card V : ℝ)) * D.diagonalBound z ≤
        D₀ * scalarScale (D.s z) (D.ε z)) :
    eventMass D.weight (fun x => D.structural x ∧ ¬ ∀ z ∈ D.domain,
      D.RateLocalLawAt (A₀ + K₀) (A₀ + K₀ + D₀) z x) /
        eventMass D.weight D.structural ≤
      (∑ t, ∑ o, (D.firstBudget t o + D.secondBudget t o)) /
        eventMass D.weight D.structural := by
  have hpointwise : ∀ z ∈ D.domain, ∀ x, D.structural x →
      EntryTraceAt D.G (fun x z => D.P x z (D.m z)) D.md D.badDiagonal
        (fun z => D.ε z + D.modelLipschitz z * scalarScale (D.s z) (D.ε z))
        D.diagonalBound z x →
      D.RateLocalLawAt (A₀ + K₀) (A₀ + K₀ + D₀) z x := by
    intro z hz x hx hlocal
    have hΨ := scalarScale_nonneg (s := D.s z) (hε z hz)
    have hsqrt : 0 < Real.sqrt (D.s z + D.ε z) :=
      Real.sqrt_pos.2 (by linarith [hs z hz, hε z hz])
    have hidentity : D.ε z =
        scalarScale (D.s z) (D.ε z) * Real.sqrt (D.s z + D.ε z) := by
      unfold scalarScale
      field_simp
    have heps : D.ε z ≤ A₀ * scalarScale (D.s z) (D.ε z) := by
      calc
        D.ε z = scalarScale (D.s z) (D.ε z) * Real.sqrt (D.s z + D.ε z) := hidentity
        _ ≤ scalarScale (D.s z) (D.ε z) * A₀ :=
          mul_le_mul_of_nonneg_left (width z hz) hΨ
        _ = A₀ * scalarScale (D.s z) (D.ε z) := mul_comm _ _
    have hmodel := mul_le_mul_of_nonneg_right (model z hz) hΨ
    have hentry : D.ε z + D.modelLipschitz z * scalarScale (D.s z) (D.ε z) ≤
        (A₀ + K₀) * scalarScale (D.s z) (D.ε z) := by
      nlinarith
    refine ⟨fun i j => (hlocal.1 i j).trans hentry, ?_⟩
    have hsum := add_le_add hentry (sparse z hz x hx)
    have htrace := hlocal.2.trans hsum
    simpa only [add_mul] using htrace
  calc
    eventMass D.weight (fun x => D.structural x ∧ ¬ ∀ z ∈ D.domain,
        D.RateLocalLawAt (A₀ + K₀) (A₀ + K₀ + D₀) z x) /
          eventMass D.weight D.structural
        ≤ eventMass D.weight (fun x => D.structural x ∧ ¬ ∀ z ∈ D.domain,
          EntryTraceAt D.G (fun x z => D.P x z (D.m z)) D.md D.badDiagonal
            (fun z => D.ε z + D.modelLipschitz z * scalarScale (D.s z) (D.ε z))
            D.diagonalBound z x) / eventMass D.weight D.structural := by
      apply div_le_div_of_nonneg_right _ D.structuralPositive.le
      apply eventMass_mono D.weight D.nonnegative
      intro x hx
      refine ⟨hx.1, ?_⟩
      intro hall
      apply hx.2
      intro z hz
      exact hpointwise z hz x hx.1 (hall z hz)
    _ ≤ _ := D.generalized_theorem_4_2


/-- Polynomial high-probability version of the rate theorem. With O(N²) net
nodes, O(N) centers, and local errors at most Dlocal/N^q, the conditional
failure probability is at most 4*Cgrid*Ccenter*Dlocal/N^(q-3). -/
theorem generalized_theorem_4_2_polynomial_rate (D : Theorem42Inputs X V T)
    (A₀ K₀ D₀ : ℝ)
    (hs : ∀ z ∈ D.domain, 0 < D.s z)
    (hε : ∀ z ∈ D.domain, 0 ≤ D.ε z)
    (width : ∀ z ∈ D.domain, Real.sqrt (D.s z + D.ε z) ≤ A₀)
    (model : ∀ z ∈ D.domain, D.modelLipschitz z ≤ K₀)
    (sparse : ∀ z ∈ D.domain, ∀ x, D.structural x →
      (((D.badDiagonal x z).card : ℝ) / (Fintype.card V : ℝ)) * D.diagonalBound z ≤
        D₀ * scalarScale (D.s z) (D.ε z))
    (N q : ℕ) (hN : 0 < N) (hq : 3 ≤ q)
    (Cgrid Ccenter Dlocal : ℝ) (hCgrid : 0 ≤ Cgrid) (hCcenter : 0 ≤ Ccenter)
    (hDlocal : 0 ≤ Dlocal) (hmass : 1 / 2 ≤ eventMass D.weight D.structural)
    (hnode : (T : ℝ) ≤ Cgrid * (N : ℝ) ^ 2)
    (hcenter : (Fintype.card V : ℝ) ≤ Ccenter * (N : ℝ))
    (hα : ∀ t o, D.firstBudget t o ≤ Dlocal / (N : ℝ) ^ q)
    (hγ : ∀ t o, D.secondBudget t o ≤ Dlocal / (N : ℝ) ^ q) :
    eventMass D.weight (fun x => D.structural x ∧ ¬ ∀ z ∈ D.domain,
      D.RateLocalLawAt (A₀ + K₀) (A₀ + K₀ + D₀) z x) /
        eventMass D.weight D.structural ≤
      4 * Cgrid * Ccenter * Dlocal / (N : ℝ) ^ (q - 3) := by
  have htotal : (∑ t, ∑ o, (D.firstBudget t o + D.secondBudget t o)) ≤
      2 * Cgrid * Ccenter * Dlocal / (N : ℝ) ^ (q - 3) := by
    apply cubic_probability_budget (fun _ : Fin T => (Finset.univ : Finset V))
      D.firstBudget D.secondBudget N q hN hq Cgrid Ccenter Dlocal hCcenter hDlocal
    · simpa only [Fintype.card_fin] using hnode
    · intro t
      simpa only [Finset.card_univ] using hcenter
    · intro t o _
      exact hα t o
    · intro t o _
      exact hγ t o
  have hbudget : 0 ≤ 2 * Cgrid * Ccenter * Dlocal / (N : ℝ) ^ (q - 3) := by
    positivity
  have hconditional := conditional_budget_factor_two _ _ _ hbudget hmass htotal
  have hrate := D.generalized_theorem_4_2_rate A₀ K₀ D₀ hs hε width model sparse
  apply hrate.trans
  convert hconditional using 1
  ring

end Theorem42Inputs

end LocalLaw
