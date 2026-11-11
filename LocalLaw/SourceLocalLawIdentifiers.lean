import LocalLaw.RealErrorParameters
import LocalLaw.SourceReferenceIdentification

/-! # Literal source density integrals and infinite tree-extension identifiers -/

noncomputable section
namespace LocalLaw
local instance sourceLocalLawIdentifiersDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def realSourcePaperError (a : ℝ) (d N r : ℕ) (z : ℂ) : ℝ :=
  inflateError (Real.log (N : ℝ))
    (Real.log (N : ℝ) ^ (8 * a) * baseErrorTerms d N r z.im (kestenMcKayStieltjes d z).im)
    (spectralScale z)

theorem realSourcePaperError_eq_graph (a : ℝ) (d N r : ℕ) (hd : 3 ≤ d) (z : ℂ) (hz : 0 < z.im) :
    realSourcePaperError a d N r z = realGraphPaperError a d N r z := by
  unfold realSourcePaperError realGraphPaperError
  rw [kestenMcKayStieltjes_eq_transform d hd z hz]
  rfl

def RealSourceLocalLawAt {N d : ℕ} (hd : 1 ≤ d) (a : ℝ) (r : ℕ) (C : ℝ)
    (z : ℂ) (g : RegularGraph N d) : Prop :=
  (∀ i j, ‖g.G z i j - (g.pairModel i j r).treeExtensionGreen hd z
    (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r)‖ ≤
      C * scalarScale (spectralScale z) (realSourcePaperError a d N r z)) ∧
  ‖empiricalTransform g.H z - kestenMcKayStieltjes d z‖ ≤
    C * scalarScale (spectralScale z) (realSourcePaperError a d N r z)

theorem RealActualGraphLocalLawAt.to_source {N d r : ℕ} {a C : ℝ} {z : ℂ} {g : RegularGraph N d}
    (h : RealActualGraphLocalLawAt a r C C z g) (hd : 3 ≤ d) (hz : 0 < z.im) :
    RealSourceLocalLawAt (by omega) a r C z g := by
  have htarget (i j : Fin N) : (g.pairModel i j r).treeExtensionGreen (by omega) z
      (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r) = g.P r z (semicircleRoot z) i j := by
    rw [(g.pairModel i j r).treeExtensionGreen_eq_extensionGreen hd z hz]
    exact g.pairModel_P i j r (semicircleRoot z) z
  constructor
  · intro i j
    rw [htarget, realSourcePaperError_eq_graph a d N r hd z hz]
    exact h.1 i j
  · rw [kestenMcKayStieltjes_eq_transform d hd z hz, realSourcePaperError_eq_graph a d N r hd z hz]
    exact h.2

theorem ActualGraphLocalLawAt.mono_constants {N d a r : ℕ} {Centry Ctrace C : ℝ}
    {z : ℂ} {g : RegularGraph N d} (h : ActualGraphLocalLawAt a r Centry Ctrace z g)
    (hN : 1 ≤ N) (hz : 0 ≤ z.im) (he : Centry ≤ C) (ht : Ctrace ≤ C) :
    ActualGraphLocalLawAt a r C C z g := by
  have hscale := scalarScale_nonneg (s := spectralScale z) (graphPaperError_nonnegative a d N r z hN hz)
  exact ⟨fun i j => (h.1 i j).trans (mul_le_mul_of_nonneg_right he hscale),
    h.2.trans (mul_le_mul_of_nonneg_right ht hscale)⟩

end LocalLaw
