import LocalLaw.Abstract
import LocalLaw.FiniteResampling

/-!
# A generalized finite local-law assembly theorem

The graph measure and enlarged resampling measure are finite weighted spaces.
The proof derives the failure probability from the two integrated resampling
errors, deterministic certificate closure, ordered transport, and continuum
coverage. Model-dependent estimates remain explicit hypotheses.
-/

open scoped BigOperators

namespace LocalLaw

section OrderedNet

variable {X : Type*} {T : ℕ}

/-- Arbitrary preceding strict events may establish the next weak event.
This formulation permits several anchors and arbitrary ordered finite nets. -/
theorem ordered_first_failure (F : X → Prop) (A H : Fin T → X → Prop)
    (transport : ∀ t x, F x → (∀ k, k < t → H k x) → A t x)
    (x : X) (hx : F x ∧ ¬ ∀ t, H t x) :
    ∃ t, A t x ∧ ¬ H t x := by
  classical
  by_contra hnone
  have hall : ∀ n (hn : n < T), H ⟨n, hn⟩ x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_contra hH
      apply hnone
      refine ⟨⟨n, hn⟩, transport ⟨n, hn⟩ x hx.1 ?_, hH⟩
      intro k hk
      exact ih k.val hk k.isLt
  exact hx.2 (fun t => hall t.val t.isLt)

variable [Fintype X]

theorem ordered_bootstrap_mass (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (F : X → Prop) (A H : Fin T → X → Prop)
    (transport : ∀ t x, F x → (∀ k, k < t → H k x) → A t x)
    (δ : Fin T → ℝ)
    (defect : ∀ t, eventMass w (fun x => A t x ∧ ¬ H t x) ≤ δ t) :
    eventMass w (fun x => F x ∧ ¬ ∀ t, H t x) ≤ ∑ t, δ t := by
  classical
  calc
    eventMass w (fun x => F x ∧ ¬ ∀ t, H t x)
        ≤ eventMass w (fun x => ∃ t ∈ (Finset.univ : Finset (Fin T)),
          A t x ∧ ¬ H t x) :=
      eventMass_mono w hw (by
        intro x hx
        obtain ⟨t, ht⟩ := ordered_first_failure F A H transport x hx
        exact ⟨t, Finset.mem_univ _, ht⟩)
    _ ≤ ∑ t, eventMass w (fun x => A t x ∧ ¬ H t x) :=
      eventMass_exists_finset_le _ w hw _
    _ ≤ ∑ t, δ t := Finset.sum_le_sum (fun t _ => defect t)

end OrderedNet

section EnlargedResampling

variable {X Ω O Z : Type*} [Fintype X] [Fintype Ω]
variable {T : ℕ}

/-- Transfer a two-stage estimate on the enlarged space to an event of the
original configurations. Marginality is stated for all events explicitly. -/
theorem projected_reversible_two_stage
    (w : X → ℝ) (ν : Ω → ℝ) (hν : ∀ ω, 0 ≤ ν ω) (π : Ω → X)
    (marginal : ∀ P : X → Prop, eventMass ν (fun ω => P (π ω)) = eventMass w P)
    (τ : Equiv.Perm Ω) (preserve : ∀ ω, ν (τ ω) = ν ω)
    (involution : Function.Involutive τ)
    (A B C : X → Prop) (α γ : ℝ)
    (first : eventMass ν (fun ω => A (π ω) ∧ ¬ B (π (τ ω))) ≤ α)
    (second : eventMass ν (fun ω => B (π ω) ∧ ¬ C (π (τ ω))) ≤ γ) :
    eventMass w (fun x => A x ∧ ¬ C x) ≤ α + γ := by
  rw [← marginal (fun x => A x ∧ ¬ C x)]
  exact reversible_two_stage ν hν τ preserve involution
    (fun ω => A (π ω)) (fun ω => B (π ω)) (fun ω => C (π ω)) α γ first second

/-- Local certificates plus a finite union bound give the strict-event defect. -/
theorem certificate_defect_mass (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (centers : Finset O) (A H : X → Prop) (C : O → X → Prop) (δ : O → ℝ)
    (closure : ∀ x, A x → (∀ o ∈ centers, C o x) → H x)
    (site : ∀ o ∈ centers, eventMass w (fun x => A x ∧ ¬ C o x) ≤ δ o) :
    eventMass w (fun x => A x ∧ ¬ H x) ≤ ∑ o ∈ centers, δ o := by
  classical
  have hcover : ∀ x, (A x ∧ ¬ H x) → ∃ o ∈ centers, A x ∧ ¬ C o x := by
    intro x hx
    by_contra hn
    apply hx.2
    apply closure x hx.1
    intro o ho
    by_contra hc
    exact hn ⟨o, ho, hx.1, hc⟩
  calc
    eventMass w (fun x => A x ∧ ¬ H x)
        ≤ eventMass w (fun x => ∃ o ∈ centers, A x ∧ ¬ C o x) :=
      eventMass_mono w hw hcover
    _ ≤ ∑ o ∈ centers, eventMass w (fun x => A x ∧ ¬ C o x) :=
      eventMass_exists_finset_le centers w hw _
    _ ≤ ∑ o ∈ centers, δ o := Finset.sum_le_sum site

/-- Complete generalized assembly probability theorem. In particular, the
right side is derived from local resampling estimates, not assumed as a
hypothesis. `Domain` may be infinite; finiteness of X avoids measurability
issues for the simultaneous event. -/
theorem assembly_failure_mass
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (ν : Ω → ℝ) (hν : ∀ ω, 0 ≤ ν ω) (π : Ω → X)
    (marginal : ∀ P : X → Prop, eventMass ν (fun ω => P (π ω)) = eventMass w P)
    (F : X → Prop) (A H : Fin T → X → Prop)
    (centers : Fin T → Finset O) (B C : Fin T → O → X → Prop)
    (τ : Fin T → O → Equiv.Perm Ω)
    (preserve : ∀ t o ω, ν (τ t o ω) = ν ω)
    (involution : ∀ t o, Function.Involutive (τ t o))
    (α γ : Fin T → O → ℝ)
    (first : ∀ t o, o ∈ centers t →
      eventMass ν (fun ω => A t (π ω) ∧ ¬ B t o (π (τ t o ω))) ≤ α t o)
    (second : ∀ t o, o ∈ centers t →
      eventMass ν (fun ω => B t o (π ω) ∧ ¬ C t o (π (τ t o ω))) ≤ γ t o)
    (closure : ∀ t x, A t x → (∀ o ∈ centers t, C t o x) → H t x)
    (transport : ∀ t x, F x → (∀ k, k < t → H k x) → A t x)
    (Domain : Set Z) (Regular : Z → X → Prop)
    (cover : ∀ x, F x → (∀ t, H t x) → ∀ z ∈ Domain, Regular z x) :
    eventMass w (fun x => F x ∧ ¬ ∀ z ∈ Domain, Regular z x) ≤
      ∑ t, ∑ o ∈ centers t, (α t o + γ t o) := by
  have hdefect : ∀ t, eventMass w (fun x => A t x ∧ ¬ H t x) ≤
      ∑ o ∈ centers t, (α t o + γ t o) := by
    intro t
    apply certificate_defect_mass w hw (centers t) (A t) (H t) (C t)
      (fun o => α t o + γ t o) (closure t)
    intro o ho
    exact projected_reversible_two_stage w ν hν π marginal (τ t o)
      (preserve t o) (involution t o) (A t) (B t o) (C t o)
      (α t o) (γ t o) (first t o ho) (second t o ho)
  calc
    eventMass w (fun x => F x ∧ ¬ ∀ z ∈ Domain, Regular z x)
        ≤ eventMass w (fun x => F x ∧ ¬ ∀ t, H t x) :=
      eventMass_mono w hw (by
        intro x hx
        exact ⟨hx.1, fun hall => hx.2 (cover x hx.1 hall)⟩)
    _ ≤ ∑ t, ∑ o ∈ centers t, (α t o + γ t o) :=
      ordered_bootstrap_mass w hw F A H transport _ hdefect

/-- Conditional version: retain the structural-event denominator explicitly.
If w sums to one, this is the usual conditional failure probability. -/
theorem assembly_conditional_failure
    (w : X → ℝ) (F : X → Prop) (Failure : X → Prop) (budget : ℝ)
    (positive : 0 < eventMass w F)
    (unconditional : eventMass w (fun x => F x ∧ Failure x) ≤ budget) :
    eventMass w (fun x => F x ∧ Failure x) / eventMass w F ≤
      budget / eventMass w F :=
  div_le_div_of_nonneg_right unconditional positive.le

end EnlargedResampling

section EntryTrace

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The pointwise deterministic local law: boundary replacement followed by
averaging. The exceptional-vertex density is kept as an explicit term. -/
theorem boundary_entry_trace
    (G : V → V → ℂ) (P : ℂ → V → V → ℂ) (q m md : ℂ)
    (bad : Finset V) (a b K M : ℝ) (hK : 0 ≤ K)
    (hcard : 0 < Fintype.card V)
    (approximation : ∀ i j, ‖G i j - P q i j‖ ≤ a)
    (boundary : dist q m ≤ b)
    (sensitivity : ∀ i j, ‖P q i j - P m i j‖ ≤ K * dist q m)
    (tree : ∀ i, i ∉ bad → P m i i = md)
    (exceptional : ∀ i, i ∈ bad → ‖P m i i - md‖ ≤ M) :
    (∀ i j, ‖G i j - P m i j‖ ≤ a + K * b) ∧
    ‖(Fintype.card V : ℝ)⁻¹ • ∑ i, (G i i - md)‖ ≤
      a + K * b + ((bad.card : ℝ) / (Fintype.card V : ℝ)) * M := by
  have hentry : ∀ i j, ‖G i j - P m i j‖ ≤ a + K * b := by
    intro i j
    exact model_transfer (G i j) (fun w => P w i j) q m a K b hK
      (approximation i j) boundary (sensitivity i j)
  refine ⟨hentry, ?_⟩
  apply sparse_average_bound (fun i => G i i - md) bad (a + K * b) M hcard
  · intro i hi
    simpa [tree i hi] using hentry i i
  · intro i hi
    exact (norm_sub_le_norm_sub_add_norm_sub (G i i) (P m i i) md).trans
      (add_le_add (hentry i i) (exceptional i hi))

/-- The local-law event at one spectral parameter. -/
def EntryTraceAt {X Z : Type*}
    (G : X → Z → V → V → ℂ) (Reference : X → Z → V → V → ℂ)
    (md : Z → ℂ) (bad : X → Z → Finset V) (entryError M : Z → ℝ)
    (z : Z) (x : X) : Prop :=
    (∀ i j, ‖G x z i j - Reference x z i j‖ ≤ entryError z) ∧
    ‖(Fintype.card V : ℝ)⁻¹ • ∑ i, (G x z i i - md z)‖ ≤
      entryError z + (((bad x z).card : ℝ) / (Fintype.card V : ℝ)) * M z

end EntryTrace



section BudgetTransport

variable {Z J : Type*} [PseudoMetricSpace Z]

/-- Analytic continuity and error-budget comparison are separate assumptions.
This lemma remains valid across discontinuous budgets when the displayed
comparison holds, and makes no unproved budget-comparability inference. -/
theorem defect_budget_transport (defect budget : Z → J → ℝ)
    (z w : Z) (θ : ℝ) (K : J → ℝ)
    (strict : ∀ j, defect w j ≤ θ * budget w j)
    (continuous : ∀ j, |defect z j - defect w j| ≤ K j * dist z w)
    (comparison : ∀ j, θ * budget w j + K j * dist z w ≤ budget z j) :
    ∀ j, defect z j ≤ budget z j := by
  intro j
  have hd : defect z j - defect w j ≤ K j * dist z w :=
    (le_abs_self _).trans (continuous j)
  exact (show defect z j ≤ θ * budget w j + K j * dist z w by
    linarith [strict j]).trans (comparison j)

end BudgetTransport

/-- A center may have its own finite enlarged resampling space. Requiring
separate extensions avoids an unjustified common-space assumption. -/
structure ReversibleExtension (X : Type*) [Fintype X] (w : X → ℝ) where
  space : Type
  [finite : Fintype space]
  weight : space → ℝ
  nonnegative : ∀ ω, 0 ≤ weight ω
  project : space → X
  marginal : ∀ P : X → Prop,
    eventMass weight (fun ω => P (project ω)) = eventMass w P
  switching : Equiv.Perm space
  preserve : ∀ ω, weight (switching ω) = weight ω
  involution : Function.Involutive switching

attribute [instance] ReversibleExtension.finite


/-- Construct the abstract extension from actual graph-dependent finite
resampling fibers. Marginality and weight preservation are proved by the
finite-fiber library; only the combinatorial switching properties are inputs. -/
noncomputable def finiteFiberExtension {X Block : Type} [Fintype X]
    (S : X → Type) [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (block : X → Block)
    (hweight : ∀ x y, block x = block y → w x = w y)
    (hcard : ∀ x y, block x = block y → Fintype.card (S x) = Fintype.card (S y))
    (τ : Equiv.Perm (Σ x, S x))
    (hblock : ∀ ω, block (τ ω).1 = block ω.1)
    (hinvolution : Function.Involutive τ) : ReversibleExtension X w where
  space := Σ x, S x
  finite := inferInstance
  weight := finiteFiberWeight S w
  nonnegative := finiteFiberWeight_nonneg S w hw
  project := Sigma.fst
  marginal := finiteFiberWeight_projection S w
  switching := τ
  preserve := finiteFiberWeight_preserved_of_block S w block hweight hcard τ hblock
  involution := hinvolution

/-- Explicit input contract for the generalized assembly theorem. The fields
are local errors and deterministic inclusions, never the desired final
probability bound. `normalized` makes eventMass an actual probability. -/
structure AssemblyInputs (X O Z : Type*) [Fintype X] (T : ℕ) where
  weight : X → ℝ
  nonnegative : ∀ x, 0 ≤ weight x
  normalized : ∑ x, weight x = 1
  structural : X → Prop
  structuralPositive : 0 < eventMass weight structural
  weak : Fin T → X → Prop
  strict : Fin T → X → Prop
  centers : Fin T → Finset O
  intermediate : Fin T → O → X → Prop
  certificate : Fin T → O → X → Prop
  extension : Fin T → O → ReversibleExtension X weight
  firstBudget : Fin T → O → ℝ
  secondBudget : Fin T → O → ℝ
  firstEstimate : ∀ t o, o ∈ centers t →
    eventMass (extension t o).weight (fun ω => weak t ((extension t o).project ω) ∧
      ¬ intermediate t o ((extension t o).project ((extension t o).switching ω)))
        ≤ firstBudget t o
  secondEstimate : ∀ t o, o ∈ centers t →
    eventMass (extension t o).weight
      (fun ω => intermediate t o ((extension t o).project ω) ∧
        ¬ certificate t o ((extension t o).project ((extension t o).switching ω)))
          ≤ secondBudget t o
  closure : ∀ t x, weak t x → (∀ o ∈ centers t, certificate t o x) → strict t x
  transport : ∀ t x, structural x → (∀ k, k < t → strict k x) → weak t x
  domain : Set Z
  regular : Z → X → Prop
  cover : ∀ x, structural x → (∀ t, strict t x) → ∀ z ∈ domain, regular z x

namespace AssemblyInputs

variable {X O Z : Type*} [Fintype X] {T : ℕ}

noncomputable def totalBudget (S : AssemblyInputs X O Z T) : ℝ :=
  ∑ t, ∑ o ∈ S.centers t, (S.firstBudget t o + S.secondBudget t o)

theorem uniform_failure_bound (S : AssemblyInputs X O Z T) :
    eventMass S.weight (fun x => S.structural x ∧ ¬ ∀ z ∈ S.domain, S.regular z x)
      ≤ S.totalBudget :=
by
  have hdefect : ∀ t, eventMass S.weight (fun x => S.weak t x ∧ ¬ S.strict t x) ≤
      ∑ o ∈ S.centers t, (S.firstBudget t o + S.secondBudget t o) := by
    intro t
    apply certificate_defect_mass S.weight S.nonnegative (S.centers t)
      (S.weak t) (S.strict t) (S.certificate t)
      (fun o => S.firstBudget t o + S.secondBudget t o) (S.closure t)
    intro o ho
    let E := S.extension t o
    exact projected_reversible_two_stage S.weight E.weight E.nonnegative E.project
      E.marginal E.switching E.preserve E.involution (S.weak t) (S.intermediate t o)
      (S.certificate t o) (S.firstBudget t o) (S.secondBudget t o)
      (S.firstEstimate t o ho) (S.secondEstimate t o ho)
  calc
    eventMass S.weight (fun x => S.structural x ∧ ¬ ∀ z ∈ S.domain, S.regular z x)
        ≤ eventMass S.weight (fun x => S.structural x ∧ ¬ ∀ t, S.strict t x) :=
      eventMass_mono S.weight S.nonnegative (by
        intro x hx
        exact ⟨hx.1, fun hall => hx.2 (S.cover x hx.1 hall)⟩)
    _ ≤ S.totalBudget :=
      ordered_bootstrap_mass S.weight S.nonnegative S.structural S.weak S.strict
        S.transport _ hdefect

/-- Generalized assembly, including uniform entry bounds, trace bounds, and
conditioning on the positive structural event. The graph-specific analytic
content is precisely the listed pointwise hypotheses on `S.regular`. -/
theorem uniform_entry_trace_local_law
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : AssemblyInputs X O Z T)
    (G : X → Z → V → V → ℂ) (P : X → Z → ℂ → V → V → ℂ)
    (q : X → Z → ℂ) (m md : Z → ℂ) (bad : X → Z → Finset V)
    (a b K M : Z → ℝ) (hK : ∀ z ∈ S.domain, 0 ≤ K z)
    (hcard : 0 < Fintype.card V)
    (approximation : ∀ z ∈ S.domain, ∀ x, S.regular z x →
      ∀ i j, ‖G x z i j - P x z (q x z) i j‖ ≤ a z)
    (boundary : ∀ z ∈ S.domain, ∀ x, S.regular z x → dist (q x z) (m z) ≤ b z)
    (sensitivity : ∀ z ∈ S.domain, ∀ x, S.regular z x →
      ∀ i j, ‖P x z (q x z) i j - P x z (m z) i j‖ ≤ K z * dist (q x z) (m z))
    (tree : ∀ z ∈ S.domain, ∀ x, S.regular z x →
      ∀ i, i ∉ bad x z → P x z (m z) i i = md z)
    (exceptional : ∀ z ∈ S.domain, ∀ x, S.regular z x →
      ∀ i, i ∈ bad x z → ‖P x z (m z) i i - md z‖ ≤ M z) :
    eventMass S.weight (fun x => S.structural x ∧ ¬ ∀ z ∈ S.domain,
      EntryTraceAt G (fun x z => P x z (m z)) md bad
        (fun z => a z + K z * b z) M z x) / eventMass S.weight S.structural
      ≤ S.totalBudget / eventMass S.weight S.structural := by
  have hpointwise : ∀ z ∈ S.domain, ∀ x, S.regular z x →
      EntryTraceAt G (fun x z => P x z (m z)) md bad
        (fun z => a z + K z * b z) M z x := by
    intro z hz x hx
    exact boundary_entry_trace (G x z) (P x z) (q x z) (m z) (md z)
      (bad x z) (a z) (b z) (K z) (M z) (hK z hz) hcard
      (approximation z hz x hx) (boundary z hz x hx) (sensitivity z hz x hx)
      (tree z hz x hx) (exceptional z hz x hx)
  apply div_le_div_of_nonneg_right _ S.structuralPositive.le
  calc
    eventMass S.weight (fun x => S.structural x ∧ ¬ ∀ z ∈ S.domain,
        EntryTraceAt G (fun x z => P x z (m z)) md bad
          (fun z => a z + K z * b z) M z x)
        ≤ eventMass S.weight (fun x => S.structural x ∧
          ¬ ∀ z ∈ S.domain, S.regular z x) :=
      eventMass_mono S.weight S.nonnegative (by
        intro x hx
        refine ⟨hx.1, ?_⟩
        intro hall
        apply hx.2
        intro z hz
        exact hpointwise z hz x (hall z hz))
    _ ≤ S.totalBudget := S.uniform_failure_bound

end AssemblyInputs

end LocalLaw
