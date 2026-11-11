import SpectralConsequences.ReferenceCDF

/-! # Reference distributions with square-root edge mass -/

namespace SpectralConsequences

structure SquareRootCDF extends CompactCDF where
  mass : ℝ
  mass_pos : 0 < mass
  lower_mass : ∀ x y : ℝ, lower ≤ x → x ≤ y → y ≤ upper →
    mass * (y-x) * Real.sqrt (y-x) ≤ cdf y - cdf x

end SpectralConsequences
