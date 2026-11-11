import LocalLaw.SourceGoodDiagonalObservation
import LocalLaw.SourceSurgeryCorrections

/-!
# Realized error in the actual good switched diagonal

The correlation and quadratic terms in physical principal-minor surgery
fit the nominal sixteen-log tolerance. The model radius does not enter
this numerical argument, so the nominal error remains unchanged.
-/

noncomputable section
namespace LocalLaw
local instance sourceGoodDiagonalParametersDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def goodDiagonalSurgeryCoefficient (d : ℕ) (C P : ℝ) : ℝ :=
  (1 + C * P) * (2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1)) * (C + C ^ 2 * P)

theorem goodDiagonalSurgeryCoefficient_nonnegative (d : ℕ) (C P : ℝ)
    (hC : 0 ≤ C) (hP : 0 ≤ P) : 0 ≤ goodDiagonalSurgeryCoefficient d C P := by
  unfold goodDiagonalSurgeryCoefficient
  positivity

theorem good_diagonal_correction_le_surgery_budget (n : ℕ) (d : ℕ)
    (C P φ δ E : ℝ) (hC : 0 ≤ C) (hP : 0 ≤ P) (hφ : 0 ≤ φ)
    (hδ : 0 ≤ δ) (_hE : 0 ≤ E) (hδE : δ ≤ E) :
    (n : ℝ) * ((1 + C * P) * φ) * (2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1)) *
        (C + C ^ 2 * P) + δ ^ 2 * P ≤
      (goodDiagonalSurgeryCoefficient d C P + P) * (E ^ 2 + (n : ℝ) * φ) := by
  let A := goodDiagonalSurgeryCoefficient d C P
  have hA : 0 ≤ A := goodDiagonalSurgeryCoefficient_nonnegative d C P hC hP
  have hsquare : δ ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ hδ hδE 2
  have hmain : A * ((n : ℝ) * φ) + P * δ ^ 2 ≤ A * ((n : ℝ) * φ) + P * E ^ 2 :=
    add_le_add_left (mul_le_mul_of_nonneg_left hsquare hP) _
  have hcross : 0 ≤ A * E ^ 2 + P * ((n : ℝ) * φ) := by positivity
  dsimp only [A, goodDiagonalSurgeryCoefficient] at *
  nlinarith

namespace RegularGraph

/-- The literal good-diagonal correction is small eventually, including an
arbitrary smaller endpoint approximation error. -/
theorem eventually_source_good_diagonal_correction_small (a b d : ℕ) (β C P D : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hβ : 0 < β)
    (hC : 0 ≤ C) (hP : 0 ≤ P) (hD : 0 ≤ D) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (ell : ℕ),
      ell ≤ doubleLogRadius a d N → ∀ z : ℂ, 0 < z.im →
      Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ D * g.sourcePrime a (logarithmicRadius β d N) z →
      (3 * (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ)) *
          ((1 + C * P) * correlationThreshold (Real.log (N : ℝ)) a N z.im
            (graphKestenMcKayReference d z).im (spectralScale z)
            (graphPaperError a d N (logarithmicRadius β d N) z)) *
          (2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1)) * (C + C ^ 2 * P) + δ ^ 2 * P ≤
        graphPaperError a d N (logarithmicRadius β d N) z / Real.log (N : ℝ) ^ 16 := by
  let K := goodDiagonalSurgeryCoefficient d C P + P
  have hK : 0 ≤ K := add_nonneg (goodDiagonalSurgeryCoefficient_nonnegative d C P hC hP) hP
  filter_upwards [eventually_source_surgery_diagonal_correction_small a b d β D K ha hb hd hβ hD hK,
    eventually_log_ge_nat 1, Filter.eventually_ge_atTop 1] with N hsmall hlog hN
  intro g o ell hell z hz hscale δ hδ hδE
  let φ := correlationThreshold (Real.log (N : ℝ)) a N z.im (graphKestenMcKayReference d z).im
    (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z)
  have hφ : 0 ≤ φ := by unfold φ correlationThreshold; positivity
  have hE : 0 ≤ D * g.sourcePrime a (logarithmicRadius β d N) z := by
    have hε := graphPaperError_nonnegative a d N (logarithmicRadius β d N) z hN hz.le
    unfold sourcePrime inflatedPrime
    positivity
  have hh := good_diagonal_correction_le_surgery_budget
    (3 * Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))) d
      C P φ δ (D * g.sourcePrime a (logarithmicRadius β d N) z) hC hP hφ hδ hE hδE
  have hbound := hsmall g o ell (3 * Nat.card (BoundaryOrientedEdge g.graph
    (graphBallVertices g.graph o ell))) hell le_rfl z hz hscale
  have hcast : (3 * (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ)) *
      ((1 + C * P) * φ) * (2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1)) * (C + C ^ 2 * P) + δ ^ 2 * P ≤
      K * ((D * g.sourcePrime a (logarithmicRadius β d N) z) ^ 2 +
        ((3 * Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℕ) : ℝ) * φ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh
  exact hcast.trans hbound

end RegularGraph
end LocalLaw
