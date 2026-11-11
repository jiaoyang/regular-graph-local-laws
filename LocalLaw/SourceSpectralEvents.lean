import LocalLaw.DeficientGraphModel
import LocalLaw.CorrelationSampling
import LocalLaw.LocalErrorBudgets
import LocalLaw.UniformGraphNet

/-!
# The actual source spectral events

Definitions 4.3--4.7 are expressed with the physical graph, its actual deleted
Green matrix, and the inherited-deficit deleted local model. This module
states intermediate implications with explicit deleted-model reference and
boundary-sensitivity hypotheses. `DeletedDiagonalReference` proves the source
model bounds, and `SourceOmegaPlusTransferEffective` proves the weak-event to
enlarged-event implication using the actual deleted-graph comparison.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw

local instance sourceEventsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace RegularGraph

variable {N d : ℕ}

/-- Definition 4.3, with rounded radii and finite exceptional-count budget. -/
def SourceStructuralPlus (g : RegularGraph N d) (R ω Cq badCount : ℕ) : Prop :=
  (∀ o, graphBallExcess g.graph o (R / 8) ≤ ω) ∧
  (∀ o, graphBallExcess g.graph o (R / 2) ≤ Cq) ∧
  (nonTreeCenters g.graph R).card ≤ 2 * badCount

/-- The actual source epsilon-prime in (4.4). -/
def sourcePrime (_g : RegularGraph N d) (a r : ℕ) (z : ℂ) : ℝ :=
  inflatedPrime (Real.log (N : ℝ)) (graphPaperError a d N r z)

/-- The actual square-root scale at the source error. -/
def sourceScale (_g : RegularGraph N d) (a r : ℕ) (z : ℂ) : ℝ :=
  scalarScale (spectralScale z) (graphPaperError a d N r z)

/-- Definition 4.4, including membership in the structural event. -/
def SourceOmega (g : RegularGraph N d) (a r R ω badCount : ℕ) (z : ℂ) : Prop :=
  structural R ω badCount g ∧ (graphLocalLawFamily N d a r).weak z g

/-- The half-sized global event of Definition 4.10. -/
def SourceOmegaMinus (g : RegularGraph N d) (a r R ω badCount : ℕ) (z : ℂ) : Prop :=
  structural R ω badCount g ∧ (graphLocalLawFamily N d a r).strict z g

/-- Definition 4.5 with the genuine deficient local model in G(T). -/
structure SourceOmegaPlus (g : RegularGraph N d) (a r R ell ω Cq badCount : ℕ)
    (C1 : ℝ) (o : Fin N) (z : ℂ) : Prop where
  structural : g.SourceStructuralPlus R ω Cq badCount
  cavity : ‖g.Q z - semicircleRoot z‖ ≤ C1 * g.sourceScale a r z
  full : ∀ i j, ‖g.G z i j - g.P r z (g.Q z) i j‖ ≤ C1 / Real.log (N : ℝ)
  deleted : let T := graphBallVertices g.graph o ell
    ∀ i j : (Tᶜ : Set (Fin N)),
      ‖(g.deficient.delete T).G z i j - g.deletedP T r z (g.Q z) i j‖ ≤
        C1 * g.sourcePrime a r z

/-- The nonlinear feedback appearing in source (4.14)--(4.15). -/
def sourceFeedback (g : RegularGraph N d) (z : ℂ) : ℝ :=
  Real.sqrt (spectralScale z) * ‖g.Q z - semicircleRoot z‖ +
    ‖g.Q z - semicircleRoot z‖ ^ 2

/-- The inside-row error in (4.14). Membership in B_ell ensures edist is
finite, so its toNat is the actual graph distance. -/
def sourceInsideRowBudget (g : RegularGraph N d) (a r ell : ℕ) (C2 : ℝ)
    (o i : Fin N) (z : ℂ) : ℝ :=
  C2 * ((Real.log (N : ℝ) / resamplingDecayDenominator d ell +
    Real.log (N : ℝ) ^ 2 /
      ((d - 1 : ℕ) : ℝ) ^ ((ell : ℝ) - ((g.graph.edist o i).toNat : ℝ) / 2)) *
        g.sourcePrime a r z + Real.log (N : ℝ) * g.sourceFeedback z)

/-- The outside-row error in (4.15). -/
def sourceOutsideRowBudget (g : RegularGraph N d) (a r ell : ℕ) (C2 : ℝ) (z : ℂ) : ℝ :=
  C2 * (Real.log (N : ℝ) ^ 2 * g.sourcePrime a r z / resamplingDecayDenominator d ell +
    Real.log (N : ℝ) * g.sourceFeedback z)

/-- The average of absolute cavity errors in (4.16). Y_ell is the ell+1
fold cavity map for a radius-ell tree (including its root). -/
def sourceCavityAbsoluteResidual (g : RegularGraph N d) (ell : ℕ) (o : Fin N) (z : ℂ) : ℝ :=
  (d : ℝ)⁻¹ * ∑ j : g.graph.neighborSet o,
    ‖green (deletedMatrix g.H j.val) z ⟨o, j.property.ne⟩ ⟨o, j.property.ne⟩ -
      cavityIterate z (g.Q z) (ell + 1)‖

/-- The local improved event of Definition 4.7. It is not declared to imply
the global improved event without the averaging and scalar closure proofs. -/
structure SourceOmegaMinusLocal (g : RegularGraph N d) (a r R ell : ℕ)
    (C2 : ℝ) (o : Fin N) (z : ℂ) : Prop where
  cavity : ‖g.Q z - semicircleRoot z‖ ≤ C2 * g.sourceScale a r z
  rowInside : ∀ i ∈ graphBallVertices g.graph o ell,
    ‖g.G z o i - g.P r z (g.Q z) o i‖ ≤ g.sourceInsideRowBudget a r ell C2 o i z
  rowOutside : ∀ i ∉ graphBallVertices g.graph o ell,
    ‖g.G z o i - g.P r z (g.Q z) o i‖ ≤ g.sourceOutsideRowBudget a r ell C2 z
  localCavity : (graphBall g.graph o R).IsTree →
    g.sourceCavityAbsoluteResidual ell o z ≤
      C2 * (Real.log (N : ℝ) * g.sourcePrime a r z / resamplingDecayDenominator d ell)

end RegularGraph

/-- A concrete constant for the source diagonal variance cap. -/
def sourceVarianceConstant (C1 Cmodel Kmodel : ℝ) : ℝ := C1 + Cmodel + Kmodel * C1

theorem sourceVarianceConstant_nonnegative (C1 Cmodel Kmodel : ℝ)
    (hC1 : 0 ≤ C1) (hCmodel : 0 ≤ Cmodel) (hKmodel : 0 ≤ Kmodel) :
    0 ≤ sourceVarianceConstant C1 Cmodel Kmodel := by unfold sourceVarianceConstant; positivity

private theorem complex_im_le_im_add_norm (x y : ℂ) : x.im ≤ y.im + ‖x - y‖ := by
  have h := (le_abs_self (x - y).im).trans (Complex.abs_im_le_norm (x - y))
  rw [Complex.sub_im] at h
  linarith

namespace RegularGraph.SourceOmegaPlus

variable {N d a r R ell ω Cq badCount : ℕ} {C1 : ℝ} {o : Fin N} {z : ℂ}
variable {g : RegularGraph N d}

/-- Source (5.40) from the actual deleted approximation and the two remaining
finite-model inputs. Neither the diagonal cap nor a correlation probability
is a hypothesis. -/
theorem diagonal_variance_cap (h : g.SourceOmegaPlus a r R ell ω Cq badCount C1 o z)
    (hN : 1 ≤ N) (hz : 0 < z.im) (Cmodel Kmodel : ℝ)
    (hC1 : 0 ≤ C1) (hCmodel : 0 ≤ Cmodel) (hKmodel : 0 ≤ Kmodel)
    (reference : let T := graphBallVertices g.graph o ell
      ∀ u : (Tᶜ : Set (Fin N)),
        (g.deletedP T r z (semicircleRoot z) u u).im ≤ Cmodel * (graphKestenMcKayReference d z).im)
    (sensitivity : let T := graphBallVertices g.graph o ell
      ∀ u : (Tᶜ : Set (Fin N)),
        ‖g.deletedP T r z (g.Q z) u u - g.deletedP T r z (semicircleRoot z) u u‖ ≤
          Kmodel * ‖g.Q z - semicircleRoot z‖) :
    let T := graphBallVertices g.graph o ell
    ∀ u : {w : Fin N // w ∉ T},
      (green (normalizedAdjacency (outsideGraph g.graph T) d) z u u).im ≤
        sourceVarianceConstant C1 Cmodel Kmodel *
          ((graphKestenMcKayReference d z).im + g.sourcePrime a r z + g.sourceScale a r z) := by
  dsimp only at reference sensitivity ⊢
  intro u
  let T := graphBallVertices g.graph o ell
  have hε : 0 ≤ graphPaperError a d N r z := graphPaperError_nonnegative a d N r z hN hz.le
  have hprime : 0 ≤ g.sourcePrime a r z := by
    unfold RegularGraph.sourcePrime inflatedPrime
    exact mul_nonneg (pow_nonneg (Real.log_nonneg (by exact_mod_cast hN)) _) hε
  have hscale : 0 ≤ g.sourceScale a r z := scalarScale_nonneg hε
  have hv : 0 ≤ (graphKestenMcKayReference d z).im :=
    (kestenMcKayTransform_im_pos d (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le).le
  have hfirst := complex_im_le_im_add_norm
    ((g.deficient.delete T).G z u u) (g.deletedP T r z (g.Q z) u u)
  have hsecond := complex_im_le_im_add_norm (g.deletedP T r z (g.Q z) u u)
    (g.deletedP T r z (semicircleRoot z) u u)
  have hsens := (sensitivity u).trans (mul_le_mul_of_nonneg_left h.cavity hKmodel)
  have hsum : ((g.deficient.delete T).G z u u).im ≤
      Cmodel * (graphKestenMcKayReference d z).im + C1 * g.sourcePrime a r z +
        (Kmodel * C1) * g.sourceScale a r z := by
    have happ := h.deleted u u
    have href := reference u
    nlinarith
  rw [RegularGraph.deleted_deficient_G] at hsum
  apply hsum.trans
  have hc1 : C1 ≤ sourceVarianceConstant C1 Cmodel Kmodel := by
    unfold sourceVarianceConstant
    nlinarith [mul_nonneg hKmodel hC1]
  have hcm : Cmodel ≤ sourceVarianceConstant C1 Cmodel Kmodel := by
    unfold sourceVarianceConstant
    nlinarith [mul_nonneg hKmodel hC1]
  have hck : Kmodel * C1 ≤ sourceVarianceConstant C1 Cmodel Kmodel := by
    unfold sourceVarianceConstant
    linarith
  have ha := mul_le_mul_of_nonneg_right hcm hv
  have hb := mul_le_mul_of_nonneg_right hc1 hprime
  have hc := mul_le_mul_of_nonneg_right hck hscale
  nlinarith

end RegularGraph.SourceOmegaPlus

/-- The simultaneous correlation-sample estimate under the actual source
OmegaPlus event. Its deleted approximation and Q prior are consumed here;
only the two specified model estimates remain hypotheses. -/
theorem eventually_sourceOmegaPlus_few_correlated_samples (a d q : ℕ)
    (c C1 Cmodel Kmodel : ℝ) (ha : 0 < a) (hd : 3 ≤ d)
    (hc : 0 ≤ c) (hc₁ : c < 1) (hC1 : 0 ≤ C1)
    (hCmodel : 0 ≤ Cmodel) (hKmodel : 0 ≤ Kmodel) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ), 0 < z.im →
      ∀ (r R ω Cq badCount : ℕ),
      g.SourceOmegaPlus a r R (actualCavityDepth a d N z - 1) ω Cq badCount C1 o z →
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      (∀ u : (Tᶜ : Set (Fin N)),
        (g.deletedP T r z (semicircleRoot z) u u).im ≤
          Cmodel * (graphKestenMcKayReference d z).im) →
      (∀ u : (Tᶜ : Set (Fin N)),
        ‖g.deletedP T r z (g.Q z) u u - g.deletedP T r z (semicircleRoot z) u u‖ ≤
          Kmodel * ‖g.Q z - semicircleRoot z‖) →
      eventMass (localSamplingWeight g.graph T)
        (fun S => ∃ x : {w : Fin N // w ∉ T}, Nat.ceil (Real.log (N : ℝ)) ≤
          (g.correlatedSampleIndices T z
            (correlationThreshold (Real.log (N : ℝ)) a N z.im
              (graphKestenMcKayReference d z).im (spectralScale z) (graphPaperError a d N r z))
            (logarithmicRadius (c / 4) d N / 4) x S).card) ≤ 1 / (N : ℝ) ^ q := by
  filter_upwards [eventually_uniform_few_correlated_samples a d q c
    (sourceVarianceConstant C1 Cmodel Kmodel) ha hd hc hc₁
      (sourceVarianceConstant_nonnegative C1 Cmodel Kmodel hC1 hCmodel hKmodel),
    eventually_log_ge_nat 1, Filter.eventually_ge_atTop 2] with N htail hlog hN
  intro g o z hz r R ω Cq badCount hplus
  dsimp only
  intro href hsens
  have hcap := hplus.diagonal_variance_cap (by omega) hz Cmodel Kmodel
    hC1 hCmodel hKmodel href hsens
  have hv : 0 ≤ (graphKestenMcKayReference d z).im :=
    (kestenMcKayTransform_im_pos d (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le).le
  have hLp : 0 < Real.log (N : ℝ) := by linarith
  have hk : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hfloor : 0 < localizationErrorFloor a d N r := by
    unfold localizationErrorFloor
    positivity
  have hε : 0 < graphPaperError a d N r z :=
    hfloor.trans_le (graphPaperError_lower a d N r z hlog hz.le)
  exact htail g o z hz (graphKestenMcKayReference d z).im (spectralScale z)
    (graphPaperError a d N r z) hv hε hcap

end LocalLaw
