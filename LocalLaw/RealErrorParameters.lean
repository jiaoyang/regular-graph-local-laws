import LocalLaw.GraphTheorem42
import LocalLaw.VerticalBudgets

/-! # Real source exponents follow by rounding down the logarithmic weight

The paper allows real a>=12 and b>=25a. The integer development may use
A=floor(a), B=25A: its spectral domain is larger, its error is smaller and
the nominal geometric radius is unchanged. Monotonicity of threshold
inflation and of the stability scale transfers the final actual local law.
-/

namespace LocalLaw

noncomputable def realGraphPaperError (a : ℝ) (d N r : ℕ) (z : ℂ) : ℝ :=
  inflateError (Real.log (N : ℝ))
    (Real.log (N : ℝ) ^ (8 * a) * baseErrorTerms d N r z.im (graphKestenMcKayReference d z).im)
    (spectralScale z)

theorem graphPaperError_le_real (A : ℕ) (a : ℝ) (d N r : ℕ) (z : ℂ)
    (hL : 1 ≤ Real.log (N : ℝ)) (hz : 0 ≤ z.im) (ha : (A : ℝ) ≤ a) :
    graphPaperError A d N r z ≤ realGraphPaperError a d N r z := by
  let L := Real.log (N : ℝ)
  let T := baseErrorTerms d N r z.im (graphKestenMcKayReference d z).im
  have hT : 0 ≤ T := baseErrorTerms_nonnegative d N r z.im _ hz
  have hexp : (((8 * A : ℕ) : ℝ)) ≤ 8 * a := by push_cast; linarith
  have hpR := Real.rpow_le_rpow_of_exponent_le hL hexp
  have hp : L ^ (8 * A) ≤ L ^ (8 * a) := by simpa only [Real.rpow_natCast] using hpR
  have hbase : 0 ≤ L ^ (8 * A) * T := mul_nonneg (pow_nonneg (by linarith) _) hT
  have hbasele : L ^ (8 * A) * T ≤ L ^ (8 * a) * T := mul_le_mul_of_nonneg_right hp hT
  exact inflateError_mono hL hbase hbasele (le_refl (spectralScale z))

theorem real_parameter_rounding (a b L : ℝ) (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hL : 1 ≤ L) :
    12 ≤ ⌊a⌋₊ ∧ (((25 * ⌊a⌋₊ : ℕ) : ℝ)) ≤ b ∧ L ^ (25 * ⌊a⌋₊ : ℕ) ≤ L ^ b := by
  have ha0 : 0 ≤ a := by linarith
  have hA : 12 ≤ ⌊a⌋₊ := (Nat.le_floor_iff ha0).mpr ha
  have hfloor : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha0
  have hB : (((25 * ⌊a⌋₊ : ℕ) : ℝ)) ≤ b := by push_cast; linarith
  refine ⟨hA, hB, ?_⟩
  simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hL hB

theorem real_domain_implies_rounded_domain (a b : ℝ) (N : ℕ) (z : ℂ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hL : 1 ≤ Real.log (N : ℝ))
    (hfloor : Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im) :
    Real.log (N : ℝ) ^ (25 * ⌊a⌋₊ : ℕ) / (N : ℝ) ≤ z.im :=
  (div_le_div_of_nonneg_right (real_parameter_rounding a b _ ha hb hL).2.2 (Nat.cast_nonneg N)).trans hfloor

def RealActualGraphLocalLawAt {N d : ℕ} (a : ℝ) (r : ℕ) (Centry Ctrace : ℝ)
    (z : ℂ) (g : RegularGraph N d) : Prop :=
  (∀ i j, ‖g.G z i j - g.P r z (semicircleRoot z) i j‖ ≤
    Centry * scalarScale (spectralScale z) (realGraphPaperError a d N r z)) ∧
  ‖empiricalTransform g.H z - graphKestenMcKayReference d z‖ ≤
    Ctrace * scalarScale (spectralScale z) (realGraphPaperError a d N r z)

theorem ActualGraphLocalLawAt.to_real_exponent {N d A r : ℕ} {a Centry Ctrace : ℝ}
    {z : ℂ} {g : RegularGraph N d} (h : ActualGraphLocalLawAt A r Centry Ctrace z g)
    (hN : 1 ≤ N) (hL : 1 ≤ Real.log (N : ℝ)) (hz : 0 < z.im)
    (ha : (A : ℝ) ≤ a) (hCentry : 0 ≤ Centry) (hCtrace : 0 ≤ Ctrace) :
    RealActualGraphLocalLawAt a r Centry Ctrace z g := by
  have hε := graphPaperError_nonnegative A d N r z hN hz.le
  have hle := graphPaperError_le_real A a d N r z hL hz.le ha
  have hscale := scalarScale_mono_error (spectralScale z) _ _ (spectralScale_pos hz) hε hle
  exact ⟨fun i j => (h.1 i j).trans (mul_le_mul_of_nonneg_left hscale hCentry),
    h.2.trans (mul_le_mul_of_nonneg_left hscale hCtrace)⟩

end LocalLaw
