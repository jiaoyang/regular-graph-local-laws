import LocalLaw.DeletedDiagonalReference
import LocalLaw.IndependentRadiusEvents

/-! # The actual deleted-diagonal variance cap at independent model radii

The two finite-model estimates formerly left as inputs are proved from the
structural eighth-radius budget. The deleted approximation and cavity prior
are consumed at their separate model/error radii. Only the explicit finite
boundary-feedback smallness remains for the large-N parameter lemma.
-/

noncomputable section
namespace LocalLaw

local instance sourceDeletedVarianceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceDeletedVarianceConstant (C1 : ℝ) (d : ℕ) : ℝ :=
  sourceVarianceConstant C1 (finiteExtraReferenceConstant d) (deletedSensitivityConstant d)

theorem sourceDeletedVarianceConstant_nonnegative (C1 : ℝ) (d : ℕ)
    (hC1 : 0 ≤ C1) (hd : 3 ≤ d) : 0 ≤ sourceDeletedVarianceConstant C1 d :=
  sourceVarianceConstant_nonnegative _ _ _ hC1
    ((by norm_num : (0 : ℝ) ≤ 1).trans (finiteExtraReferenceConstant_ge_one d hd))
    (deletedSensitivityConstant_nonnegative d)

private theorem im_le_add_norm_difference (x y : ℂ) : x.im ≤ y.im + ‖x - y‖ := by
  have h := (le_abs_self (x - y).im).trans (Complex.abs_im_le_norm (x - y))
  rw [Complex.sub_im] at h
  linarith

namespace RegularGraph.SourceOmegaPlusWithRadii
variable {N d a rModel rError R ell Cq badCount : ℕ} {C1 : ℝ} {o : Fin N} {z : ℂ}
variable {g : RegularGraph N d}

theorem actual_diagonal_variance_cap
    (h : g.SourceOmegaPlusWithRadii a rModel rError R ell (finiteOmega d) Cq badCount C1 o z)
    (hN : 1 ≤ N) (hd : 3 ≤ d) (hz : 0 < z.im) (hC1 : 0 ≤ C1)
    (hmargin : rModel + 2 * ell + 1 ≤ R / 8)
    (small : ‖g.Q z - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * (4 * (rModel : ℝ) + 2) ≤ 1 / 2) :
    let T := graphBallVertices g.graph o ell
    ∀ u : {w : Fin N // w ∉ T},
      (green (normalizedAdjacency (outsideGraph g.graph T) d) z u u).im ≤
        sourceDeletedVarianceConstant C1 d *
          ((graphKestenMcKayReference d z).im + g.sourcePrime a rError z + g.sourceScale a rError z) := by
  dsimp only
  intro u
  let T := graphBallVertices g.graph o ell
  let C := finiteExtraReferenceConstant d
  let K := deletedSensitivityConstant d
  have hC : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have hK : 0 ≤ K := deletedSensitivityConstant_nonnegative d
  have hε : 0 ≤ graphPaperError a d N rError z := graphPaperError_nonnegative a d N rError z hN hz.le
  have hprime : 0 ≤ g.sourcePrime a rError z := by
    unfold RegularGraph.sourcePrime inflatedPrime
    exact mul_nonneg (pow_nonneg (Real.log_nonneg (by exact_mod_cast hN)) _) hε
  have hscale : 0 ≤ g.sourceScale a rError z := scalarScale_nonneg hε
  have hv : 0 ≤ (graphKestenMcKayReference d z).im :=
    (kestenMcKayTransform_im_pos d (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le).le
  have href : (g.deletedP T rModel z (semicircleRoot z) u u).im ≤
      C * (graphKestenMcKayReference d z).im :=
    (le_abs_self _).trans (g.deletedP_diagonal_reference_im_bound hd o ell rModel (R / 8)
      hmargin h.structural.1 z hz u)
  have hsens : ‖g.deletedP T rModel z (g.Q z) u u -
      g.deletedP T rModel z (semicircleRoot z) u u‖ ≤ K * ‖g.Q z - semicircleRoot z‖ :=
    g.deletedP_diagonal_boundary_uniform_stability hd o ell rModel (R / 8) hmargin h.structural.1
      z (g.Q z) hz (g.Q_im_nonnegative z hz) small u
  have hfirst := im_le_add_norm_difference ((g.deficient.delete T).G z u u)
    (g.deletedP T rModel z (g.Q z) u u)
  have hsecond := im_le_add_norm_difference (g.deletedP T rModel z (g.Q z) u u)
    (g.deletedP T rModel z (semicircleRoot z) u u)
  have hperturb := hsens.trans (mul_le_mul_of_nonneg_left h.cavity hK)
  have hsum : ((g.deficient.delete T).G z u u).im ≤
      C * (graphKestenMcKayReference d z).im + C1 * g.sourcePrime a rError z +
        (K * C1) * g.sourceScale a rError z := by
    have happ := h.deleted u u
    nlinarith
  rw [RegularGraph.deleted_deficient_G] at hsum
  apply hsum.trans
  have hc1 : C1 ≤ sourceDeletedVarianceConstant C1 d := by
    unfold sourceDeletedVarianceConstant sourceVarianceConstant
    nlinarith [mul_nonneg hK hC1]
  have hcm : C ≤ sourceDeletedVarianceConstant C1 d := by
    unfold sourceDeletedVarianceConstant sourceVarianceConstant
    nlinarith [mul_nonneg hK hC1]
  have hck : K * C1 ≤ sourceDeletedVarianceConstant C1 d := by
    unfold sourceDeletedVarianceConstant sourceVarianceConstant
    dsimp only [K]
    linarith
  have ha := mul_le_mul_of_nonneg_right hcm hv
  have hb := mul_le_mul_of_nonneg_right hc1 hprime
  have hc := mul_le_mul_of_nonneg_right hck hscale
  nlinarith

end RegularGraph.SourceOmegaPlusWithRadii
end LocalLaw
