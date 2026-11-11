import LocalLaw.EdgeLocalCavity
import LocalLaw.CavityAveragePerturbation

/-!
# Switching cavity averages from local old caps

The weak target event gives a uniform cap on the new Green matrix, while
the enlarged source event supplies only old diagonal/adjacent-entry caps.
These are sufficient for the exact graph-cavity perturbation bound: mask
irrelevant old entries, retain the genuine physical Ward identities, and
count changed oriented edges separately.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance cavitySwitchingLocalDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem regular_edge_cavity_difference_local_ward (G : SimpleGraph V) (d : ℕ)
    (hregular : G.IsRegularOfDegree d) (H K : Matrix V V ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (C L I : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hRd : ∀ i, ‖green H z i i‖ ≤ C)
    (hRe : ∀ i j, G.Adj i j → ‖green H z i j‖ ≤ C)
    (hS : ∀ i j, ‖green K z i j‖ ≤ C)
    (hRi : ∀ j, ‖(green H z j j)⁻¹‖ ≤ L) (hSi : ∀ j, ‖(green K z j j)⁻¹‖ ≤ L)
    (hHI : ∀ j, (green H z j j).im ≤ I) (hKI : ∀ j, (green K z j j).im ≤ I) :
    (∑ i, ∑ j, if G.Adj i j then
        ‖matrixCavityTerm (green H z) i j - matrixCavityTerm (green K z) i j‖ else 0) ≤
      ((d : ℝ) * (1 + C * L) ^ 2 * I / z.im) * (∑ u, ∑ v, ‖(K - H) u v‖) := by
  have hbase := regular_edge_cavity_difference_local G d hregular (green H z) (green K z) C L hC hL
    hRd hRe (fun i => hS i i) (fun i j _ => hS i j) (green_diagonal_ne_zero H hH z hz) (green_diagonal_ne_zero K hK z hz) hRi hSi
  have hdiag := diagonal_green_difference_ward H K hH hK z hz I hHI hKI
  have hedge := regular_edge_green_difference_ward G d hregular H K hH hK z hz I hHI hKI
  apply hbase.trans
  calc
    _ ≤ ((d : ℝ) * (1 + C ^ 2 * L ^ 2)) *
        ((I / z.im) * (∑ u, ∑ v, ‖(K - H) u v‖)) +
        2 * C * L * (((d : ℝ) * I / z.im) * (∑ u, ∑ v, ‖(K - H) u v‖)) :=
      add_le_add (mul_le_mul_of_nonneg_left hdiag (by positivity))
        (mul_le_mul_of_nonneg_left hedge (by positivity))
    _ = _ := by ring

/-- Deterministic graph-cavity change, with the two genuinely different costs:
resolvent propagation from Ward and directly changed oriented edges. -/
theorem cavityAverage_graph_difference_local_ward (G F : SimpleGraph V) (d : ℕ)
    (hregular : G.IsRegularOfDegree d) (z : ℂ) (hz : 0 < z.im)
    (C L I : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hGd : ∀ i, ‖green (normalizedAdjacency G d) z i i‖ ≤ C)
    (hGe : ∀ i j, G.Adj i j → ‖green (normalizedAdjacency G d) z i j‖ ≤ C)
    (hF : ∀ i j, ‖green (normalizedAdjacency F d) z i j‖ ≤ C)
    (hGi : ∀ j, ‖(green (normalizedAdjacency G d) z j j)⁻¹‖ ≤ L)
    (hFi : ∀ j, ‖(green (normalizedAdjacency F d) z j j)⁻¹‖ ≤ L)
    (hGI : ∀ j, (green (normalizedAdjacency G d) z j j).im ≤ I)
    (hFI : ∀ j, (green (normalizedAdjacency F d) z j j).im ≤ I) :
    ‖cavityAverage G d z - cavityAverage F d z‖ ≤
      ((Fintype.card V : ℝ) * (d : ℝ))⁻¹ *
        ((((d : ℝ) * (1 + C * L) ^ 2 * I / z.im) *
            (∑ u, ∑ v, ‖(normalizedAdjacency F d - normalizedAdjacency G d) u v‖)) +
          adjacencyDisagreement G F * (C + C ^ 2 * L)) := by
  let R := green (normalizedAdjacency G d) z
  let S := green (normalizedAdjacency F d) z
  let Rlocal := edgeLocalMatrix G R
  have hsum := edge_cavity_sums_difference G F Rlocal S (C + C ^ 2 * L)
    (matrixCavityTerm_norm_bound Rlocal C L hC hL
      (edgeLocalMatrix_norm_bound G R C hC hGd hGe)
      (by intro i; simpa only [Rlocal, edgeLocalMatrix_diagonal] using hGi i))
    (matrixCavityTerm_norm_bound S C L hC hL hF hFi)
  have hleft : ∀ i j, (if G.Adj i j then matrixCavityTerm Rlocal i j else 0) =
      (if G.Adj i j then matrixCavityTerm R i j else 0) := by
    intro i j
    by_cases hij : G.Adj i j <;> simp only [hij, if_true, if_false]
    exact matrixCavityTerm_edgeLocal G R hij
  have hdiff : ∀ i j, (if G.Adj i j then
      ‖matrixCavityTerm Rlocal i j - matrixCavityTerm S i j‖ else 0) =
      (if G.Adj i j then ‖matrixCavityTerm R i j - matrixCavityTerm S i j‖ else 0) := by
    intro i j
    by_cases hij : G.Adj i j <;> simp only [hij, if_true, if_false]
    rw [show matrixCavityTerm Rlocal i j = matrixCavityTerm R i j from matrixCavityTerm_edgeLocal G R hij]
  simp_rw [hleft, hdiff] at hsum
  have hward := regular_edge_cavity_difference_local_ward G d hregular
    (normalizedAdjacency G d) (normalizedAdjacency F d)
    (normalizedAdjacency_isHermitian G d) (normalizedAdjacency_isHermitian F d)
    z hz C L I hC hL hGd hGe hF hGi hFi hGI hFI
  have hbound := hsum.trans (add_le_add_right hward _)
  rw [cavityAverage_eq_matrixCavityTerm G d z hz, cavityAverage_eq_matrixCavityTerm F d z hz,
    ← mul_sub, norm_mul]
  simp only [norm_inv, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

end LocalLaw
