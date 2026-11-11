import SpectralConsequences.FiniteResolventSpectrum

/-! # Corrected positive traces exclude eigenvalues on a finite covered region

The removed modes are actual indices, so repeated eigenvalues are counted
with their multiplicities. Grid coverage is an explicit hypothesis.
-/

open scoped BigOperators
noncomputable section
namespace SpectralConsequences
variable {N : ℕ}

def correctedFiniteStieltjes (values : Fin N → ℝ) (removed : Finset (Fin N)) (z : ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ i ∈ removedᶜ, ((values i : ℂ) - z)⁻¹

theorem correctedFiniteStieltjes_eq_sub (values : Fin N → ℝ)
    (removed : Finset (Fin N)) (z : ℂ) :
    correctedFiniteStieltjes values removed z = finiteStieltjes values z -
      (N : ℂ)⁻¹ * ∑ i ∈ removed, ((values i : ℂ) - z)⁻¹ := by
  unfold correctedFiniteStieltjes finiteStieltjes
  have hs := Finset.sum_compl_add_sum removed (fun i => ((values i : ℂ) - z)⁻¹)
  rw [← hs]
  ring

theorem correctedFiniteStieltjes_im (values : Fin N → ℝ)
    (removed : Finset (Fin N)) (E η : ℝ) :
    (correctedFiniteStieltjes values removed ((E : ℂ) + (η : ℂ) * Complex.I)).im =
      (N : ℝ)⁻¹ * ∑ i ∈ removedᶜ, η / ((values i - E)^2 + η^2) := by
  unfold correctedFiniteStieltjes
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add,
    Complex.im_sum, inverse_real_sub_im, add_zero]

theorem poisson_term_lower_of_abs_sub_le (x E η : ℝ) (hη : 0 < η)
    (hnear : |x - E| ≤ η) :
    1 / (2 * η) ≤ η / ((x - E)^2 + η^2) := by
  have hd : 0 < (x - E)^2 + η^2 := by positivity
  have hs : (x - E)^2 ≤ η^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg (x - E)) hη.le).mpr hnear
    simpa only [sq_abs] using hh
  apply (le_div_iff₀ hd).mpr
  apply (mul_le_mul_right (show 0 < 2 * η by positivity)).mp
  calc
    _ = (x - E)^2 + η^2 := by field_simp
    _ ≤ η * (2 * η) := by nlinarith

/-- Any unremoved eigenvalue near a tested energy forces a positive spike. -/
theorem correctedFiniteStieltjes_im_lower_of_near (values : Fin N → ℝ)
    (removed : Finset (Fin N)) (hN : 0 < N) (E η : ℝ) (hη : 0 < η)
    (i : Fin N) (hi : i ∉ removed) (hnear : |values i - E| ≤ η) :
    1 / (2 * (N : ℝ) * η) ≤
      (correctedFiniteStieltjes values removed ((E : ℂ) + (η : ℂ) * Complex.I)).im := by
  rw [correctedFiniteStieltjes_im]
  have hs := Finset.single_le_sum (s := removedᶜ)
    (f := fun j : Fin N => η / ((values j - E)^2 + η^2))
    (fun j _ => div_nonneg hη.le (by positivity)) (Finset.mem_compl.mpr hi)
  have hp := poisson_term_lower_of_abs_sub_le (values i) E η hη hnear
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hh := mul_le_mul_of_nonneg_left (hp.trans hs) (inv_nonneg.mpr hNp.le)
  convert hh using 1
  field_simp
  ring

/-- A finite grid excludes every unremoved atom in the region it covers. -/
theorem finite_grid_exclusion (values : Fin N → ℝ) (removed : Finset (Fin N))
    (hN : 0 < N) (η : ℝ) (hη : 0 < η) (region : Set ℝ) (grid : Finset ℝ)
    (hcover : ∀ x ∈ region, ∃ E ∈ grid, |x - E| ≤ η)
    (htrace : ∀ E ∈ grid,
      (correctedFiniteStieltjes values removed ((E : ℂ) + (η : ℂ) * Complex.I)).im <
        1 / (2 * (N : ℝ) * η)) :
    ∀ i, i ∉ removed → values i ∉ region := by
  intro i hi hregion
  obtain ⟨E, hE, hnear⟩ := hcover (values i) hregion
  exact (not_lt_of_ge (correctedFiniteStieltjes_im_lower_of_near values removed hN E η hη i hi hnear))
    (htrace E hE)

/-- The interval-confinement form of the finite-grid criterion. -/
theorem finite_grid_confinement (values : Fin N → ℝ) (removed : Finset (Fin N))
    (hN : 0 < N) (M A B Δ η : ℝ) (hη : 0 < η) (grid : Finset ℝ)
    (hbox : ∀ i, -M ≤ values i ∧ values i ≤ M)
    (hcover : ∀ x, (-M ≤ x ∧ x < A - Δ) ∨ (B + Δ < x ∧ x ≤ M) →
      ∃ E ∈ grid, |x - E| ≤ η)
    (htrace : ∀ E ∈ grid,
      (correctedFiniteStieltjes values removed ((E : ℂ) + (η : ℂ) * Complex.I)).im <
        1 / (2 * (N : ℝ) * η)) :
    ∀ i, i ∉ removed → A - Δ ≤ values i ∧ values i ≤ B + Δ := by
  have hex := finite_grid_exclusion values removed hN η hη
    {x | (-M ≤ x ∧ x < A - Δ) ∨ (B + Δ < x ∧ x ≤ M)} grid hcover htrace
  intro i hi
  have hh := hex i hi
  have hb := hbox i
  constructor
  · by_contra h
    exact hh (Or.inl ⟨hb.1, lt_of_not_ge h⟩)
  · by_contra h
    exact hh (Or.inr ⟨lt_of_not_ge h, hb.2⟩)

end SpectralConsequences
