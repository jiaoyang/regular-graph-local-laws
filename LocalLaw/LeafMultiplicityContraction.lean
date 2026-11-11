import LocalLaw.LeafScalarContractionParameters

/-! # Scalar leaf contraction with bounded slot multiplicity

One removed sample vertex can produce several restoring leaf slots.  A fixed
multiplicity is absorbed into the already realized scalar inverse contraction.
-/

open Filter
noncomputable section
namespace LocalLaw
local instance leafMultiplicityContractionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_selected_leaf_multiplicity_contraction (a b d M : ℕ) (β P K : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hβ : 0<β) (hP : 0≤P) :
    ∀ᶠ N : ℕ in atTop, ∀(g : RegularGraph N d)(o : Fin N)(ell : ℕ),
      ell≤doubleLogRadius a d N→∀{ι : Type}[Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))(selector : ℕ)(z : ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→∀(n : ℕ),
      n≤M*Nat.card ((g.admissibleState (graphBallVertices g.graph o ell) labels samples).AdmissibleSampleIndex selector)→
      ∀(p : ℂ)(δ : ℝ),‖p⁻¹‖≤P→0≤δ→
      δ≤K*Real.log (N:ℝ)*graphPaperError a d N (logarithmicRadius β d N) z→
      (n:ℝ)*‖p⁻¹‖*δ≤1/2 := by
  filter_upwards [eventually_selected_leaf_scalar_contraction a b d β P ((M:ℝ)*K) ha hb hd hβ hP]
    with N hN
  intro g o ell hell ι _ labels samples selector z hz hfloor n hn p δ hp hδ hcap
  let m := Nat.card ((g.admissibleState (graphBallVertices g.graph o ell) labels samples).AdmissibleSampleIndex selector)
  have hscaled : (M:ℝ)*δ≤((M:ℝ)*K)*Real.log (N:ℝ)*graphPaperError a d N (logarithmicRadius β d N) z := by
    calc
      _≤(M:ℝ)*(K*Real.log (N:ℝ)*graphPaperError a d N (logarithmicRadius β d N) z) :=
        mul_le_mul_of_nonneg_left hcap (Nat.cast_nonneg _)
      _=_ := by ring
  have hh := hN g o ell hell labels samples selector z hz hfloor m (le_refl _) p ((M:ℝ)*δ)
    hp (mul_nonneg (Nat.cast_nonneg _) hδ) hscaled
  have hnm : (n:ℝ)≤(M:ℝ)*(m:ℝ) := by exact_mod_cast hn
  calc
    _≤((M:ℝ)*(m:ℝ))*‖p⁻¹‖*δ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnm (norm_nonneg _)) hδ
    _=(m:ℝ)*‖p⁻¹‖*((M:ℝ)*δ) := by ring
    _≤1/2 := hh

end RegularGraph
end LocalLaw
