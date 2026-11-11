import LocalLaw.SourceObservationParameters

/-! # Actual radius and logarithmic budgets for two-target augmentations -/

noncomputable section
namespace LocalLaw

def augmentedObservationDiameter (d r : ℕ) : ℕ :=
  3*((finiteOmega d+1)*(2*r+1))+4*r+4

theorem augmented_radius_margin (r ell D R : ℕ) (hell : ell≤D) (hmargin : r+2*D+1≤R/8) :
    7*r+6*ell+8≤R := by
  have hh := Nat.mul_le_mul_left 8 hmargin
  have hdiv := Nat.div_mul_le_self R 8
  omega

theorem eventually_effective_augmented_radius_margin (a d : ℕ) (c β : ℝ)
    (hd : 3≤d) (hc : 0<c) (hβ : 0<β) (hβc : β≤c/32) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ ell : ℕ, ell≤doubleLogRadius a d N →
      7*effectiveModelRadius a d N β+6*ell+8≤logarithmicRadius (c/4) d N := by
  filter_upwards [eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc]
    with N hmargin
  intro ell hell
  exact augmented_radius_margin _ ell _ _ hell hmargin

theorem augmented_diameter_log_cap (ω r : ℕ) (L θ : ℝ) (hL : 1≤L) (_hθ : 0≤θ)
    (hr : (r:ℝ)≤θ*L) :
    ((3*((ω+1)*(2*r+1))+4*r+4:ℕ):ℝ)+1≤(6*(ω:ℝ)+10)*(1+θ)*L := by
  have hω : 0≤(ω:ℝ) := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_left hr (show 0≤6*(ω:ℝ)+10 by positivity)
  have hconst := mul_le_mul_of_nonneg_left hL (show 0≤6*(ω:ℝ)+10 by positivity)
  push_cast
  nlinarith only [hh,hconst,hω]

theorem effective_augmented_diameter_log (a d N : ℕ) (β : ℝ) (hd : 3≤d) (hβ : 0≤β)
    (hL : 1≤Real.log (N:ℝ)) :
    (augmentedObservationDiameter d (effectiveModelRadius a d N β):ℝ)+1≤
      sourceObservationLogCap d β*Real.log (N:ℝ) := by
  let k : ℝ := ((d-1:ℕ):ℝ)
  have hk : 1<k := by dsimp only [k]; exact_mod_cast (show 1<d-1 by omega)
  have hlogk : 0<Real.log k := Real.log_pos hk
  have hL0 : 0≤Real.log (N:ℝ) := by linarith
  have hnom : (logarithmicRadius β d N:ℝ)≤(β/Real.log k)*Real.log (N:ℝ) := by
    have hh := Nat.floor_le (div_nonneg (mul_nonneg hβ hL0) hlogk.le)
    change (logarithmicRadius β d N:ℝ)≤β*Real.log (N:ℝ)/Real.log k at hh
    exact hh.trans_eq (by ring)
  have hr : (effectiveModelRadius a d N β:ℝ)≤(β/Real.log k)*Real.log (N:ℝ) :=
    (Nat.cast_le.mpr (Nat.sub_le _ _)).trans hnom
  exact augmented_diameter_log_cap (finiteOmega d) _ _ _ hL (div_nonneg hβ hlogk.le) hr

end LocalLaw
