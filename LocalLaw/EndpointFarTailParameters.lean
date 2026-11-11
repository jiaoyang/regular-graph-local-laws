import LocalLaw.EndpointSurgeryParameters
import LocalLaw.RadiusHierarchy

/-! # Actual endpoint cardinality times far-kernel decay is negligible -/

noncomputable section
namespace LocalLaw
local instance endpointFarTailParametersDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem endpoint_far_tail_log_absorption (a : ℕ) (L ε n U p tail : ℝ)
    (ha : 12 ≤ a) (hL : 1 ≤ L) (hU : 0 ≤ U) (hp : 0 ≤ p) (ht : 0 ≤ tail)
    (hcount : n ≤ U * L ^ (2 * a)) (hdecay : tail ≤ p)
    (hfloor : L ^ (8 * a) * p ≤ ε) (hlarge : U ≤ L) : n * tail ≤ ε / L ^ 16 := by
  have hLp : 0 < L := by linarith
  apply (le_div_iff₀ (pow_pos hLp 16)).mpr
  calc
    _ ≤ (U * L ^ (2 * a)) * p * L ^ 16 :=
      mul_le_mul_of_nonneg_right (mul_le_mul hcount hdecay ht (by positivity)) (by positivity)
    _ = U * L ^ (2 * a + 16) * p := by rw [pow_add]; ring
    _ ≤ L * L ^ (2 * a + 16) * p :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlarge (by positivity)) hp
    _ = L ^ (2 * a + 17) * p := by rw [show 2 * a + 17 = (2 * a + 16) + 1 by omega, pow_succ]; ring
    _ ≤ L ^ (8 * a) * p := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL (by omega)) hp
    _ ≤ _ := hfloor

namespace RegularGraph

theorem eventually_endpoint_far_tail_small (a d : ℕ) (K : ℝ) (ha : 12 ≤ a) (hd : 3 ≤ d) (hK : 0 ≤ K) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (ell : ℕ),
      ell ≤ doubleLogRadius a d N → ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) (selector rError h : ℕ),
      2 * rError ≤ h → ∀ z : ℂ, 0 ≤ z.im →
      let s := g.admissibleState (graphBallVertices g.graph o ell) boundary samples
      K * (Nat.card (s.endpointModelRoots selector) : ℝ) * physicalTransfer d z ^ h ≤
        graphPaperError a d N rError z / Real.log (N : ℝ) ^ 16 := by
  let U := K * (3 * (d : ℝ) * ((d : ℝ) + 1))
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  filter_upwards [eventually_log_ge_nat 1, eventually_log_ge_nat U] with N hlog hlarge
  intro g o ell hell ι _ boundary samples selector rError h hh z hz
  dsimp only
  let s := g.admissibleState (graphBallVertices g.graph o ell) boundary samples
  let L := Real.log (N : ℝ)
  let p := ((((d - 1 : ℕ) : ℝ) ^ rError)⁻¹)
  have ht : 0 ≤ physicalTransfer d z := norm_nonneg _
  have htone : physicalTransfer d z ≤ 1 := by nlinarith [physicalTransfer_sq_le_half d hd z]
  have hdecay : physicalTransfer d z ^ h ≤ p :=
    (pow_le_pow_of_le_one ht htone hh).trans (physical_transfer_two_sided_tail d hd z rError)
  have hcount : K * (Nat.card (s.endpointModelRoots selector) : ℝ) ≤ U * L ^ (2 * a) := by
    have hroot : (Nat.card (s.endpointModelRoots selector) : ℝ) ≤
        3 * (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ) := by
      exact_mod_cast s.endpointModelRoots_card selector
    have hh := mul_le_mul_of_nonneg_left (hroot.trans (mul_le_mul_of_nonneg_left
      (g.boundary_card_log_bound o a ell hd hlog hell) (by norm_num : (0 : ℝ) ≤ 3))) hK
    exact hh.trans_eq (by dsimp only [U]; ring)
  have hfloor : L ^ (8 * a) * p ≤ graphPaperError a d N rError z := by
    have hh := graphPaperError_lower a d N rError z hlog hz
    simpa only [localizationErrorFloor, L, p] using hh
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  exact endpoint_far_tail_log_absorption a L _ _ U p _ ha hlog hU hp (pow_nonneg ht _) hcount hdecay hfloor hlarge

end RegularGraph
end LocalLaw
