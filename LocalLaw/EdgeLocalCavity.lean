import LocalLaw.CavityAveragePerturbation

/-!
# Cavity comparison from diagonal and adjacent-entry caps only

An oriented cavity term uses just its two diagonal entries and the two
adjacent entries. Masking every other matrix entry therefore preserves the
actual edge sums and turns local caps into the uniform caps required by the
already proved rational modulus. No global nonlocal entry cap is used.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance edgeLocalCavityDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*}

def edgeLocalMatrix (G : SimpleGraph V) (R : Matrix V V ℂ) : Matrix V V ℂ :=
  fun i j => if i = j ∨ G.Adj i j then R i j else 0

@[simp] theorem edgeLocalMatrix_diagonal (G : SimpleGraph V) (R : Matrix V V ℂ) (i : V) :
    edgeLocalMatrix G R i i = R i i := by simp only [edgeLocalMatrix, true_or, if_true]

theorem edgeLocalMatrix_of_adj (G : SimpleGraph V) (R : Matrix V V ℂ) {i j : V} (hij : G.Adj i j) :
    edgeLocalMatrix G R i j = R i j := by simp only [edgeLocalMatrix, hij, or_true, if_true]

theorem matrixCavityTerm_edgeLocal (G : SimpleGraph V) (R : Matrix V V ℂ) {i j : V} (hij : G.Adj i j) :
    matrixCavityTerm (edgeLocalMatrix G R) i j = matrixCavityTerm R i j := by
  simp only [matrixCavityTerm, edgeLocalMatrix_diagonal, edgeLocalMatrix_of_adj G R hij,
    edgeLocalMatrix_of_adj G R hij.symm]

theorem edgeLocalMatrix_norm_bound (G : SimpleGraph V) (R : Matrix V V ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hdiag : ∀ i, ‖R i i‖ ≤ C) (hedge : ∀ i j, G.Adj i j → ‖R i j‖ ≤ C) :
    ∀ i j, ‖edgeLocalMatrix G R i j‖ ≤ C := by
  intro i j
  unfold edgeLocalMatrix
  split_ifs with h
  · rcases h with rfl | h
    · exact hdiag i
    · exact hedge i j h
  · simpa only [norm_zero] using hC

variable [Fintype V]

/-- Exact local-cap version of the averaged rational cavity modulus. -/
theorem regular_edge_cavity_difference_local (G : SimpleGraph V) (d : ℕ)
    (hregular : G.IsRegularOfDegree d) (R S : Matrix V V ℂ) (C L : ℝ)
    (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hRd : ∀ i, ‖R i i‖ ≤ C) (hRe : ∀ i j, G.Adj i j → ‖R i j‖ ≤ C)
    (hSd : ∀ i, ‖S i i‖ ≤ C) (hSe : ∀ i j, G.Adj i j → ‖S i j‖ ≤ C)
    (hRp : ∀ j, R j j ≠ 0) (hSp : ∀ j, S j j ≠ 0)
    (hRi : ∀ j, ‖(R j j)⁻¹‖ ≤ L) (hSi : ∀ j, ‖(S j j)⁻¹‖ ≤ L) :
    (∑ i, ∑ j, if G.Adj i j then ‖matrixCavityTerm R i j - matrixCavityTerm S i j‖ else 0) ≤
      ((d : ℝ) * (1 + C ^ 2 * L ^ 2)) * (∑ i, ‖R i i - S i i‖) +
        2 * C * L * (∑ i, ∑ j, if G.Adj i j then ‖R i j - S i j‖ else 0) := by
  have hh := regular_edge_cavity_difference G d hregular (edgeLocalMatrix G R) (edgeLocalMatrix G S)
    C L hC hL (edgeLocalMatrix_norm_bound G R C hC hRd hRe) (edgeLocalMatrix_norm_bound G S C hC hSd hSe)
    (by intro i; simpa only [edgeLocalMatrix_diagonal] using hRp i)
    (by intro i; simpa only [edgeLocalMatrix_diagonal] using hSp i)
    (by intro i; simpa only [edgeLocalMatrix_diagonal] using hRi i)
    (by intro i; simpa only [edgeLocalMatrix_diagonal] using hSi i)
  have hterm : ∀ i j, (if G.Adj i j then
      ‖matrixCavityTerm (edgeLocalMatrix G R) i j - matrixCavityTerm (edgeLocalMatrix G S) i j‖ else 0) =
        (if G.Adj i j then ‖matrixCavityTerm R i j - matrixCavityTerm S i j‖ else 0) := by
    intro i j
    by_cases hij : G.Adj i j <;> simp only [hij, if_true, if_false]
    rw [matrixCavityTerm_edgeLocal G R hij, matrixCavityTerm_edgeLocal G S hij]
  have hentry : ∀ i j, (if G.Adj i j then
      ‖edgeLocalMatrix G R i j - edgeLocalMatrix G S i j‖ else 0) =
        (if G.Adj i j then ‖R i j - S i j‖ else 0) := by
    intro i j
    by_cases hij : G.Adj i j <;> simp only [hij, if_true, if_false]
    rw [edgeLocalMatrix_of_adj G R hij, edgeLocalMatrix_of_adj G S hij]
  simpa only [hterm, hentry, edgeLocalMatrix_diagonal] using hh

end LocalLaw
