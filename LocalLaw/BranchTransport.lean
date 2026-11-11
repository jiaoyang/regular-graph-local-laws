import LocalLaw.RectangularNet
import LocalLaw.BudgetComparison
import LocalLaw.ErrorParameters
import LocalLaw.SpectralTransport

/-!
# Branch-respecting spectral transport for the actual error inflation

Finite cells supply same-branch representatives. Within one branch, base-error
variation implies inflated-error variation; explicit relative bounds then
leave sufficient budget for analytic defect transport. No global continuity
of the thresholded epsilon is assumed.
-/

namespace LocalLaw

/-- Relative continuity of the inflated error follows from the same-branch
base-error modulus and epsilon>=epsilon0. -/
theorem inflatedError_relative_variation (L e₀ e₁ s₀ s₁ : ℝ)
    (hL : 1 ≤ L) (he₀ : 0 ≤ e₀)
    (hbranch : errorBranch L e₁ s₁ = errorBranch L e₀ s₀)
    (hbase : L ^ 4 * |e₁ - e₀| ≤ e₀ / 8) :
    |inflateError L e₁ s₁ - inflateError L e₀ s₀| ≤ inflateError L e₀ s₀ / 8 := by
  have hdiff := inflateError_abs_sub_le_same_branch hL hbranch
  have hlow := (inflateError_bounds (s := s₀) hL he₀).1
  exact hdiff.trans (hbase.trans (by linarith))

/-- A local step from a same-error-branch representative, built from
component continuity and explicit quarter-budget bounds. -/
noncomputable def branchTransportStep {X V : Type*}
    (F : LocalLawFamily X V) (structural : X → Prop)
    (L : ℝ) (base : ℂ → ℝ) (w z : ℂ)
    (KQ Km KG KP : ℝ) (hL : 1 ≤ L)
    (hs : 0 < F.s z) (hε : 0 < F.ε z) (hbaseNonneg : 0 ≤ base z)
    (errorFormula : ∀ u, F.ε u = inflateError L (base u) (F.s u))
    (sameBranch : errorBranch L (base w) (F.s w) = errorBranch L (base z) (F.s z))
    (baseModulus : L ^ 4 * |base w - base z| ≤ base z / 8)
    (scaleModulus : |F.s w - F.s z| ≤ F.s z / 8)
    (hKQ : 0 ≤ KQ) (hKm : 0 ≤ Km) (hKG : 0 ≤ KG) (hKP : 0 ≤ KP)
    (hQ : ∀ x, structural x → ‖F.Q x z - F.Q x w‖ ≤ KQ * dist z w)
    (hm : ‖F.m z - F.m w‖ ≤ Km * dist z w)
    (hG : ∀ x, structural x → ∀ i j,
      ‖F.G x z i j - F.G x w i j‖ ≤ KG * dist z w)
    (hP : ∀ x, structural x → ∀ i j,
      ‖F.P x z (F.Q x z) i j - F.P x w (F.Q x w) i j‖ ≤ KP * dist z w)
    (cavityMargin : (KQ + Km) * dist z w ≤ scalarScale (F.s z) (F.ε z) / 4)
    (entryMargin : (KG + KP) * dist z w ≤ F.ε z / 4) :
    LocalLawTransportStep F structural w z := by
  have hvar : |F.ε w - F.ε z| ≤ F.ε z / 8 := by
    simp only [errorFormula]
    exact inflatedError_relative_variation L (base z) (base w) (F.s z) (F.s w)
      hL hbaseNonneg sameBranch baseModulus
  have hbudget := local_budget_comparison (F.s z) (F.s w) (F.ε z) (F.ε w)
    (KQ + Km) (KG + KP) (dist z w) hs hε scaleModulus hvar cavityMargin entryMargin
  exact LocalLawTransportStep.ofComponents F structural w z KQ Km KG KP
    hKQ hKm hKG hKP hQ hm hG hP hbudget.1 hbudget.2

/-- A branch-preserving net supplies the full simultaneous event once each
permitted center-to-target comparison is justified analytically. -/
theorem branchNet_uniform_cover {X V J : Type*} (F : LocalLawFamily X V)
    (structural : X → Prop) (domain : Set ℂ) (classify : ℂ → J) (h : ℝ) (K : ℕ)
    (net : BranchNet domain classify h K)
    (steps : ∀ z ∈ domain, ∀ w ∈ net.centers, classify w = classify z → dist z w ≤ h →
      Nonempty (LocalLawTransportStep F structural w z)) :
    ∀ x, structural x → (∀ w ∈ net.centers, F.strict w x) →
      ∀ z ∈ domain, F.weak z x := by
  intro x hx hall z hz
  obtain ⟨w, hw, hbranch, hdist⟩ := net.cover z hz
  obtain ⟨step⟩ := steps z hz w hw hbranch hdist
  exact step.strict_to_weak x hx (hall w hw)

/-- The number of branch-aware representatives is explicitly bounded by
2(M+1)(K+1) for the paper's two error branches. -/
theorem exists_errorBranch_rectangular_net
    (domain : Set ℂ) (L : ℝ) (base scale : ℂ → ℝ)
    (a b h : ℝ) (M K : ℕ) (hh : 0 < h)
    (hD : domain ⊆ spectralRectangle a b h M K) :
    Nonempty (BranchNet domain (fun z => errorBranch L (base z) (scale z)) (2 * h)
      ((M + 1) * (K + 1) * 2)) := by
  simpa only [Fintype.card_bool] using
    exists_rectangular_branchNet domain (fun z => errorBranch L (base z) (scale z))
      a b h M K hh hD

end LocalLaw
