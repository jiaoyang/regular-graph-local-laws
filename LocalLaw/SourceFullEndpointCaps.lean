import LocalLaw.SourceFullEndpointApproximation
import LocalLaw.SourceGreenCaps

/-! # New full physical endpoint and reciprocal-diagonal caps from the old weak event

Only the original source event is used. The benchmark is the actual new
filled model, whose base class is already derived by the pendant geometry.
These are endpoint caps, not a claim about every new ambient vertex.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceFullEndpointCapsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_fullEndpoint_green_caps (a b d : ℕ) (c β B : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ∀ badCount : ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (finiteOmega d) badCount z →
      ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      let selector := logarithmicRadius (c / 4) d N / 4
      let s := g.admissibleState T boundary samples
      let gnew := g.labelledResampledGraph T boundary samples selector
      (∀ i j : s.fullEndpointRoots selector, ‖gnew.G z i.val j.val‖ ≤ sourceGreenEntryCap d) ∧
        (∀ i : s.fullEndpointRoots selector, ‖(gnew.G z i.val i.val)⁻¹‖ ≤ sourceGreenPivotCap d B) := by
  let C := finiteReferenceConstant d
  let Cconv := coreConvolutionConstant (finiteOmega d)
  let A := filledEndpointLogCap d β
  let τ := 1 / (4 * C * (B + 2))
  let Hbase := C * Cconv * A
  let Hchange := 8 * C ^ 2 * Cconv
  have hC : 1 ≤ C := finiteReferenceConstant_ge_one d hd
  have hC0 : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans hC
  have hCconv : 0 ≤ Cconv := coreConvolutionConstant_nonnegative _
  have hAobs := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hA : 0 ≤ A := by dsimp only [A, filledEndpointLogCap]; linarith
  have hAle : sourceObservationLogCap d β ≤ A := by dsimp only [A, filledEndpointLogCap]; linarith
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hτone : τ ≤ 1 := by
    dsimp only [τ]
    apply (div_le_iff₀ (by positivity : 0 < 4 * C * (B + 2))).mpr
    nlinarith
  have hHbase : 0 ≤ Hbase := by dsimp only [Hbase]; positivity
  have hHchange : 0 ≤ Hchange := by dsimp only [Hchange]; positivity
  filter_upwards [eventually_source_fullEndpoint_approximation a b d c β B τ ha hb hd hc hβ hβc hτ hτone,
    eventually_sourceObservationBounds_of_cap a b d c β B 1 A ha hb hd hc hβ hβc le_rfl hAle,
    eventually_filledEndpoint_diameter_log a b d c β B 1 ha hb hd hc hβ hβc le_rfl,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,
    eventually_log_ge_nat (2 * Hbase), eventually_log_ge_nat (Hchange / τ)]
    with N happ hnum hlog hmarg hlarge hchange
  intro g o z hz hzB hfloor badCount hsource ι _ boundary samples
  dsimp only
  let ell := actualCavityDepth a d N z - 1
  let R := logarithmicRadius (c / 4) d N
  let selector := R / 4
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary samples
  let gnew := g.labelledResampledGraph T boundary samples selector
  let M := gnew.filledExteriorModel T (s.endpointModelVertices selector r)
  let e := s.fullEndpointModelEmbedding selector r
  let L := Real.log (N : ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let x := ‖g.Q z - semicircleRoot z‖
  have num := hnum z hz hfloor
  have hL : 1 ≤ L := num.log_one
  have hLp : 0 < L := by linarith
  have hprior : x ≤ scalarScale (spectralScale z) ε := hsource.2.1
  have hcap : ε * L ^ 4 ≤ 1 := by simpa only [one_pow, one_mul] using num.error_scaled
  have hscaled : x * L ^ 2 ≤ 1 := weak_prior_scaled_norm z (g.Q z) hz ε L num.error_nonnegative hcap hprior
  have hx : 0 ≤ x := norm_nonneg _
  have hsep : 2 * r + 2 ≤ selector := by
    have hh := hmarg.2.2.2 z
    dsimp only [r, selector, R]
    omega
  have hmargin : ell + r + 1 ≤ R := by
    have hh := hmarg.2.2.2 z
    dsimp only [ell, r, R]
    omega
  have hclass : M.ComponentReferenceBudget := g.filledEndpoint_component_reference_budget o ell selector r R
    boundary samples hsep hmargin (hsource.1.1 o)
  have hdiam : ∀ u v, M.graph.dist u v ≤ filledEndpointDiameter d ell r :=
    g.filledEndpoint_distance_bound o ell selector r R (finiteOmega d) boundary samples hsep hmargin (hsource.1.1 o)
  have hRlog := hlog z hz hfloor
  have hsmall : x * C * Cconv * ((filledEndpointDiameter d ell r : ℝ) + 1) ≤ 1 / 2 := by
    calc
      _ ≤ x * C * Cconv * (A * L) := mul_le_mul_of_nonneg_left hRlog (by positivity)
      _ = x * Hbase * L := by dsimp only [Hbase]; ring
      _ ≤ 1 / 2 := scale_weight_small x L Hbase hx hLp hHbase hscaled hlarge
  have hδ : Hchange * x ≤ τ := by
    have hHL : Hchange ≤ τ * L := by simpa only [mul_comm] using (div_le_iff₀ hτ).mp hchange
    have hLsq : L ≤ L ^ 2 := by nlinarith only [hL]
    calc
      _ ≤ (τ * L ^ 2) * x := mul_le_mul_of_nonneg_right
        (hHL.trans (mul_le_mul_of_nonneg_left hLsq hτ.le)) hx
      _ = τ * (x * L ^ 2) := by ring
      _ ≤ τ * 1 := mul_le_mul_of_nonneg_left hscaled hτ.le
      _ = τ := mul_one _
  have hmodel (i j : s.fullEndpointRoots selector) :
      ‖M.extensionGreen (g.Q z) z (e i) (e j) - M.extensionGreen (semicircleRoot z) z (e i) (e j)‖ ≤ τ :=
    (M.componentwise_boundary_uniform_stability hd hclass z (g.Q z) hz (g.Q_im_nonnegative z hz)
      (filledEndpointDiameter d ell r) hdiam hsmall (e i) (e j)).trans hδ
  have hphysical := happ g o z hz hzB hfloor badCount hsource boundary samples
  have htotal (i j : s.fullEndpointRoots selector) :
      ‖gnew.G z i.val j.val - M.extensionGreen (semicircleRoot z) z (e i) (e j)‖ ≤ 2 * τ :=
    ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add (hphysical i j) (hmodel i j))).trans_eq (by ring)
  constructor
  · intro i j
    have href := M.componentwise_reference_entry_bound hd hclass z hz (e i) (e j)
    have htri := norm_add_le (gnew.G z i.val j.val - M.extensionGreen (semicircleRoot z) z (e i) (e j))
      (M.extensionGreen (semicircleRoot z) z (e i) (e j))
    rw [sub_add_cancel] at htri
    change ‖gnew.G z i.val j.val‖ ≤ C + 2
    linarith [htotal i j]
  · intro i
    have href := (M.componentwise_reference_diagonal_bounds hd hclass z hz B hzB (e i)).1
    have hdist := htotal i i
    have hreverse := norm_sub_norm_le (M.extensionGreen (semicircleRoot z) z (e i) (e i))
      (gnew.G z i.val i.val)
    rw [norm_sub_rev] at hreverse
    have hfour : 1 / (C * (B + 2)) = 4 * τ := by dsimp only [τ]; field_simp; ring
    have hlower : 2 * τ ≤ ‖gnew.G z i.val i.val‖ := by rw [hfour] at href; linarith
    rw [norm_inv]
    calc
      _ ≤ (2 * τ)⁻¹ := inv_anti₀ (by positivity) hlower
      _ = sourceGreenPivotCap d B := by dsimp only [τ, sourceGreenPivotCap, C]; field_simp; ring

end RegularGraph
end LocalLaw
