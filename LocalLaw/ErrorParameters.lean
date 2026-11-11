import LocalLaw.SpectralGap
import LocalLaw.ScalarStability

/-!
# The paper's error parameters and their exact dichotomy

The integer exponents a and radii r are finite choices of the parameters in
Definition 4.1. The formulas keep log N, the variance input Im(m_d), and N*eta
visible. Positivity/smallness hypotheses are explicit; no exceptional-vertex
term is silently absorbed.
-/

namespace LocalLaw

/-- The threshold inflation in (4.3), with L = log N and s = kappa+eta. -/
noncomputable def inflateError (L e₀ s : ℝ) : ℝ :=
  if e₀ ≤ s / L then e₀ else L ^ 4 * e₀

theorem inflateError_of_small {L e₀ s : ℝ} (h : e₀ ≤ s / L) :
    inflateError L e₀ s = e₀ := if_pos h

theorem inflateError_of_large {L e₀ s : ℝ} (h : s / L < e₀) :
    inflateError L e₀ s = L ^ 4 * e₀ := if_neg (not_le.mpr h)

theorem inflateError_nonnegative {L e₀ s : ℝ} (he₀ : 0 ≤ e₀) :
    0 ≤ inflateError L e₀ s := by
  unfold inflateError
  split <;> positivity

theorem inflateError_positive {L e₀ s : ℝ} (hL : 0 < L) (he₀ : 0 < e₀) :
    0 < inflateError L e₀ s := by
  unfold inflateError
  split <;> positivity

theorem inflateError_bounds {L e₀ s : ℝ} (hL : 1 ≤ L) (he₀ : 0 ≤ e₀) :
    e₀ ≤ inflateError L e₀ s ∧ inflateError L e₀ s ≤ L ^ 4 * e₀ := by
  have hp : 1 ≤ L ^ 4 := one_le_pow₀ hL
  have hm : e₀ ≤ L ^ 4 * e₀ := by nlinarith [mul_le_mul_of_nonneg_right hp he₀]
  unfold inflateError
  split <;> constructor <;> linarith

/-- The exact separated/edge dichotomy required by scalar stability. -/
theorem inflateError_dichotomy {L e₀ s : ℝ} (hL : 0 < L) :
    inflateError L e₀ s ≤ s / L ∨ L ^ 3 * s ≤ inflateError L e₀ s := by
  unfold inflateError
  split
  next h => exact Or.inl h
  next h =>
    right
    have hs : s < e₀ * L := (div_lt_iff₀ hL).mp (lt_of_not_ge h)
    have hp := mul_le_mul_of_nonneg_left hs.le (pow_nonneg hL.le 3)
    nlinarith [hp]

/-- Downward spectral motion is favorable when the base error increases and
the regularized edge distance decreases. This monotonicity includes the
small-to-large branch jump, without assuming the inflated error continuous. -/
theorem inflateError_mono {L e₁ e₂ s₁ s₂ : ℝ} (hL : 1 ≤ L)
    (he₁ : 0 ≤ e₁) (he : e₁ ≤ e₂) (hs : s₂ ≤ s₁) :
    inflateError L e₁ s₁ ≤ inflateError L e₂ s₂ := by
  have hLp : 0 < L := by linarith
  have hthreshold : s₂ / L ≤ s₁ / L := div_le_div_of_nonneg_right hs hLp.le
  by_cases h₁ : e₁ ≤ s₁ / L
  · rw [inflateError_of_small h₁]
    exact he.trans (inflateError_bounds hL (he₁.trans he)).1
  · have h₂ : ¬ e₂ ≤ s₂ / L := by
      intro hh
      exact h₁ (he.trans (hh.trans hthreshold))
    simp only [inflateError, h₁, h₂, if_false]
    exact mul_le_mul_of_nonneg_left he (pow_nonneg hLp.le 4)


/-- The classifier used to choose separate representatives of the two error
branches inside each spectral cell. -/
noncomputable def errorBranch (L e₀ s : ℝ) : Bool :=
  if e₀ ≤ s / L then true else false

/-- Inflation is continuous with an explicit modulus inside a fixed branch.
The hypothesis is essential: no global continuity across the jump is claimed. -/
theorem inflateError_abs_sub_le_same_branch {L e₁ e₂ s₁ s₂ : ℝ}
    (hL : 1 ≤ L) (hbranch : errorBranch L e₁ s₁ = errorBranch L e₂ s₂) :
    |inflateError L e₁ s₁ - inflateError L e₂ s₂| ≤ L ^ 4 * |e₁ - e₂| := by
  have hp : 1 ≤ L ^ 4 := one_le_pow₀ hL
  by_cases h₁ : e₁ ≤ s₁ / L
  · have h₂ : e₂ ≤ s₂ / L := by
      by_contra hn
      simp [errorBranch, h₁, hn] at hbranch
    rw [inflateError_of_small h₁, inflateError_of_small h₂]
    nlinarith [mul_le_mul_of_nonneg_right hp (abs_nonneg (e₁ - e₂))]
  · have h₂ : ¬ e₂ ≤ s₂ / L := by
      intro hh
      simp [errorBranch, h₁, hh] at hbranch
    simp only [inflateError, h₁, h₂, if_false]
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ L ^ 4)]

/-- Explicit threshold smallness: an upper bound on L^4 times the base error
is sufficient for an upper bound on the inflated error. -/
theorem inflateError_le_of_base {L e₀ s cap : ℝ} (hL : 1 ≤ L)
    (he₀ : 0 ≤ e₀) (hcap : L ^ 4 * e₀ ≤ cap) :
    inflateError L e₀ s ≤ cap := (inflateError_bounds hL he₀).2.trans hcap

/-- The three terms inside the parentheses in (4.2). -/
noncomputable def baseErrorTerms (d N r : ℕ) (η immd : ℝ) : ℝ :=
  (((d - 1 : ℕ) : ℝ) ^ r)⁻¹ + Real.sqrt (immd / ((N : ℝ) * η)) +
    (((N : ℝ) * η) ^ (2 / 3 : ℝ))⁻¹

/-- Equation (4.2), with the logarithmic factor L supplied separately. -/
noncomputable def baseError (L : ℝ) (a d N r : ℕ) (η immd : ℝ) : ℝ :=
  L ^ (8 * a) * baseErrorTerms d N r η immd

/-- Equation (4.2) with its actual logarithm. -/
noncomputable def paperBaseError (a d N r : ℕ) (η immd : ℝ) : ℝ :=
  baseError (Real.log (N : ℝ)) a d N r η immd

/-- Equations (4.2)--(4.3) at the actual edge-distance scale. The reference
transform's imaginary part is passed explicitly rather than identified with
an unproved integral formula. -/
noncomputable def paperError (a d N r : ℕ) (z : ℂ) (immd : ℝ) : ℝ :=
  inflateError (Real.log (N : ℝ)) (paperBaseError a d N r z.im immd) (spectralScale z)

theorem baseErrorTerms_nonnegative (d N r : ℕ) (η immd : ℝ)
    (hη : 0 ≤ η) : 0 ≤ baseErrorTerms d N r η immd := by
  unfold baseErrorTerms
  positivity

theorem baseError_nonnegative (L : ℝ) (a d N r : ℕ) (η immd : ℝ)
    (hL : 0 ≤ L) (hη : 0 ≤ η) : 0 ≤ baseError L a d N r η immd :=
  mul_nonneg (pow_nonneg hL _) (baseErrorTerms_nonnegative d N r η immd hη)

theorem baseError_positive (L : ℝ) (a d N r : ℕ) (η immd : ℝ)
    (hL : 0 < L) (hd : 2 ≤ d) (hN : 0 < N) (hη : 0 < η) :
    0 < baseError L a d N r η immd := by
  have hd' : 0 < d - 1 := by omega
  have hdn : (0 : ℝ) < (d - 1 : ℕ) := Nat.cast_pos.mpr hd'
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  unfold baseError baseErrorTerms
  positivity

/-- Each weighted component is bounded by the full nonnegative base error. -/
theorem baseError_component_bounds (L : ℝ) (a d N r : ℕ) (η immd : ℝ)
    (hL : 0 ≤ L) (hη : 0 ≤ η) :
    L ^ (8 * a) * (((d - 1 : ℕ) : ℝ) ^ r)⁻¹ ≤ baseError L a d N r η immd ∧
    L ^ (8 * a) * Real.sqrt (immd / ((N : ℝ) * η)) ≤ baseError L a d N r η immd ∧
    L ^ (8 * a) * (((N : ℝ) * η) ^ (2 / 3 : ℝ))⁻¹ ≤ baseError L a d N r η immd := by
  have h₁ : 0 ≤ (((d - 1 : ℕ) : ℝ) ^ r)⁻¹ := by positivity
  have h₂ : 0 ≤ Real.sqrt (immd / ((N : ℝ) * η)) := Real.sqrt_nonneg _
  have h₃ : 0 ≤ (((N : ℝ) * η) ^ (2 / 3 : ℝ))⁻¹ := by positivity
  have hw : 0 ≤ L ^ (8 * a) := pow_nonneg hL _
  unfold baseError baseErrorTerms
  constructor
  · exact mul_le_mul_of_nonneg_left (by linarith) hw
  constructor <;> exact mul_le_mul_of_nonneg_left (by linarith) hw

/-- Finite smallness from explicit per-component budgets; no asymptotic
threshold, radius restriction, or exceptional-vertex absorption is hidden. -/
theorem baseError_le_of_component_bounds (L : ℝ) (a d N r : ℕ)
    (η immd cap : ℝ)
    (h₁ : L ^ (8 * a) * (((d - 1 : ℕ) : ℝ) ^ r)⁻¹ ≤ cap / 3)
    (h₂ : L ^ (8 * a) * Real.sqrt (immd / ((N : ℝ) * η)) ≤ cap / 3)
    (h₃ : L ^ (8 * a) * (((N : ℝ) * η) ^ (2 / 3 : ℝ))⁻¹ ≤ cap / 3) :
    baseError L a d N r η immd ≤ cap := by
  unfold baseError baseErrorTerms
  nlinarith


/-- An explicit finite-L sufficient condition for the first inequality in
(4.5). This statement does not assert that the paper's N-dependent choices
already satisfy the supplied base-error bound. -/
theorem inflateError_small_of_base {L e₀ s : ℝ} (a : ℕ) (hL : 1 ≤ L)
    (he₀ : 0 ≤ e₀) (hbase : e₀ ≤ (L ^ (4 * a + 4))⁻¹) :
    inflateError L e₀ s ≤ (L ^ (4 * a))⁻¹ := by
  have hLp : 0 < L := by linarith
  have hLzero : L ≠ 0 := ne_of_gt hLp
  calc
    inflateError L e₀ s ≤ L ^ 4 * e₀ := (inflateError_bounds hL he₀).2
    _ ≤ L ^ 4 * (L ^ (4 * a + 4))⁻¹ :=
      mul_le_mul_of_nonneg_left hbase (pow_nonneg hLp.le 4)
    _ = (L ^ (4 * a))⁻¹ := by
      rw [pow_add]
      field_simp [hLzero]
      ring

/-- The raw sum of the three error components can be bounded before applying
the logarithmic weight and threshold inflation. The exponent arithmetic is
proved explicitly. -/
theorem inflatedBaseError_small (L : ℝ) (a d N r : ℕ) (η immd s : ℝ)
    (hL : 1 ≤ L) (hη : 0 ≤ η)
    (hterms : baseErrorTerms d N r η immd ≤ (L ^ (12 * a + 4))⁻¹) :
    inflateError L (baseError L a d N r η immd) s ≤ (L ^ (4 * a))⁻¹ := by
  have hLp : 0 < L := by linarith
  have hLzero : L ≠ 0 := ne_of_gt hLp
  apply inflateError_small_of_base a hL (baseError_nonnegative L a d N r η immd hLp.le hη)
  calc
    baseError L a d N r η immd ≤ L ^ (8 * a) * (L ^ (12 * a + 4))⁻¹ :=
      mul_le_mul_of_nonneg_left hterms (pow_nonneg hLp.le _)
    _ = (L ^ (4 * a + 4))⁻¹ := by
      rw [show 12 * a + 4 = 8 * a + (4 * a + 4) by omega, pow_add]
      field_simp [hLzero]

/-- Equation (4.4), epsilon-prime. -/
noncomputable def inflatedPrime (L ε : ℝ) : ℝ := L ^ 3 * ε

/-- Equation (4.4), the Green-function correlation threshold phi. -/
noncomputable def correlationThreshold (L : ℝ) (a N : ℕ)
    (η immd s ε : ℝ) : ℝ :=
  L ^ (2 * a) * Real.sqrt ((immd + inflatedPrime L ε + scalarScale s ε) /
    ((N : ℝ) * η))

theorem paperError_dichotomy (a d N r : ℕ) (z : ℂ) (immd : ℝ)
    (hlog : 0 < Real.log (N : ℝ)) :
    paperError a d N r z immd ≤ spectralScale z / Real.log (N : ℝ) ∨
      Real.log (N : ℝ) ^ 3 * spectralScale z ≤ paperError a d N r z immd :=
  inflateError_dichotomy hlog

end LocalLaw
