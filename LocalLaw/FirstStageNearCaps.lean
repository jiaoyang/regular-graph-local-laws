import LocalLaw.NearPairGreenCaps
import LocalLaw.SourceGuardedCapParameters
import LocalLaw.SourceFullEndpointCaps
import LocalLaw.SwitchingQEdgeParameters
import LocalLaw.IndependentRadiusSourceCaps
import LocalLaw.SourceModelTransfer

/-! # First-stage local physical caps and Q change from a near-entry comparison

The only analytic comparison left as an input is the new diagonal/adjacent
pair approximation at the OLD Q. New structural ball budgets and the old
weak source event derive every physical cap. Removed old edges are handled
by the already proved full modified-endpoint estimate.
-/

noncomputable section
namespace LocalLaw
local instance firstStageNearCapsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}

def nearFrozenBoundaryComparison (g h : RegularGraph N d) (r : ℕ) (D : ℝ) (z : ℂ) : Prop :=
  ∀ i j, (i = j ∨ h.graph.Adj i j) →
    ‖h.G z i j - h.P r z (g.Q z) i j‖ ≤ D / Real.log (N : ℝ)

theorem eventually_firstStage_near_green_caps (a b d : ℕ) (c β B D : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hB : 0 ≤ B) (hD : 1 ≤ D) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g h : RegularGraph N d) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ∀ badCount : ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (finiteOmega d) badCount z →
      (∀ v, graphBallExcess h.graph v (logarithmicRadius (c / 4) d N / 8) ≤ finiteOmega d) →
      g.nearFrozenBoundaryComparison h (effectiveModelRadius a d N β) D z →
      (∀ i j, (i = j ∨ h.graph.Adj i j) → ‖h.G z i j‖ ≤ sourceGreenEntryCap d) ∧
        (∀ i, ‖(h.G z i i)⁻¹‖ ≤ sourceGreenPivotCap d B) := by
  filter_upwards [eventually_sourceLocalCapBounds a b d β D B ha hb hd hβ (by linarith) hB,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,
    Filter.eventually_ge_atTop 1] with N hnum hmarg hN
  intro g h z hz hzB hfloor badCount hsource hballs hnear
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  have hε : 0 ≤ ε := graphPaperError_nonnegative a d N _ z (by omega) hz.le
  have hprior : ‖g.Q z - semicircleRoot z‖ ≤ D * scalarScale (spectralScale z) ε :=
    hsource.2.1.trans (le_mul_of_one_le_left (scalarScale_nonneg hε) hD)
  have hmargin : effectiveModelRadius a d N β + 1 ≤ logarithmicRadius (c / 4) d N / 8 := by
    have hh := hmarg.2.2.2 z
    omega
  have num := (hnum z (g.Q z) hz hfloor _ hmarg.2.2.1 hprior).1
  exact h.near_green_caps_of_pair_approximation hd _ _ hmargin hballs z (g.Q z) hz
    (g.Q_im_nonnegative z hz) B _ hzB num hnear

theorem eventually_firstStage_Q_change_of_near_comparison (a b d : ℕ) (c β B D : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hB : 0 ≤ B) (hD : 1 ≤ D) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ∀ badCount : ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (finiteOmega d) badCount z →
      ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      let selector := logarithmicRadius (c / 4) d N / 4
      let h := g.labelledResampledGraph T boundary samples selector
      (∀ v, graphBallExcess h.graph v (logarithmicRadius (c / 4) d N / 8) ≤ finiteOmega d) →
      g.nearFrozenBoundaryComparison h (effectiveModelRadius a d N β) D z →
      ‖g.Q z - h.Q z‖ ≤ graphPaperError a d N (logarithmicRadius β d N) z / Real.log (N : ℝ) ^ 16 := by
  let C := sourceGreenEntryCap d
  let P := sourceGreenPivotCap d B
  have hC : 0 ≤ C := by
    have hh := finiteReferenceConstant_ge_one d hd
    dsimp only [C, sourceGreenEntryCap]
    linarith
  have hP : 0 ≤ P := by
    have hh := finiteReferenceConstant_ge_one d hd
    dsimp only [P, sourceGreenPivotCap]
    positivity
  filter_upwards [eventually_firstStage_near_green_caps a b d c β B D ha hb hd hc hβ hβc hB hD,
    eventually_source_fullEndpoint_green_caps a b d c β B ha hb hd hc hβ hβc hB,
    eventually_sourceOmegaWithRadii_green_caps a b d c β B ha hb hd hc hβ hβc hB,
    LabelledResamplingState.eventually_selected_fullResample_cavity_change_edges_small a b d C P B ha hb hd hC hP hB]
    with N hnearCaps hendpoint hOld hchange
  intro g o z hz hzB hfloor badCount hsource ι _ boundary samples
  dsimp only
  let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
  let selector := logarithmicRadius (c / 4) d N / 4
  let s := g.admissibleState T boundary samples
  let h := g.labelledResampledGraph T boundary samples selector
  intro hballs hnear
  have newCaps := hnearCaps g h z hz hzB hfloor badCount hsource hballs hnear
  have oldCaps := hOld g z badCount hz hzB hfloor hsource
  have endpointCaps := hendpoint g o z hz hzB hfloor badCount hsource boundary samples
  have hunion (i j : Fin N) (hij : (s.graph ⊔ (s.fullResample selector).graph).Adj i j) :
      ‖h.G z i j‖ ≤ C := by
    by_cases hnew : h.graph.Adj i j
    · exact newCaps.1 i j (Or.inr hnew)
    · have hold : s.graph.Adj i j := hij.elim id (fun h => False.elim (hnew h))
      have hi : i ∈ s.fullEndpointRoots selector := by
        by_contra hnot
        have haway : i ∉ s.fullResampleEndpoints selector := fun h =>
          hnot (s.fullResampleEndpoints_subset_fullEndpointRoots selector h)
        exact hnew ((s.fullResample_adj_of_away_endpoint selector i j haway).mpr hold)
      have hj : j ∈ s.fullEndpointRoots selector := by
        by_contra hnot
        have haway : j ∉ s.fullResampleEndpoints selector := fun h =>
          hnot (s.fullResampleEndpoints_subset_fullEndpointRoots selector h)
        exact hnew (((s.fullResample_adj_of_away_endpoint selector j i haway).mpr hold.symm).symm)
      exact endpointCaps.1 ⟨i, hi⟩ ⟨j, hj⟩
  have hh := hchange g o z hz hzB hfloor ι s selector (logarithmicRadius β d N) rfl
    (fun i => oldCaps.1 i i) (fun i j _ => oldCaps.1 i j)
    (fun i => newCaps.1 i i (Or.inl rfl)) hunion oldCaps.2 newCaps.2
  exact hh

theorem eventually_firstStage_Q_prior_of_near_comparison (a b d : ℕ) (c β B D : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hB : 0 ≤ B) (hD : 1 ≤ D) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ∀ badCount : ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (finiteOmega d) badCount z →
      ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      let selector := logarithmicRadius (c / 4) d N / 4
      let h := g.labelledResampledGraph T boundary samples selector
      (∀ v, graphBallExcess h.graph v (logarithmicRadius (c / 4) d N / 8) ≤ finiteOmega d) →
      g.nearFrozenBoundaryComparison h (effectiveModelRadius a d N β) D z →
      ‖h.Q z - semicircleRoot z‖ ≤ 2 * g.sourceScale a (logarithmicRadius β d N) z := by
  filter_upwards [eventually_firstStage_Q_change_of_near_comparison a b d c β B D ha hb hd hc hβ hβc hB hD,
    eventually_paperError_small a b d β ha hb hd hβ, eventually_log_ge_nat 1,
    eventually_log_ge_nat (sourceWidthConstant B), Filter.eventually_ge_atTop 1]
    with N hchange hsmall hlog hwidthLarge hN
  intro g o z hz hzB hfloor badCount hsource ι _ boundary samples
  dsimp only
  let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
  let selector := logarithmicRadius (c / 4) d N / 4
  let h := g.labelledResampledGraph T boundary samples selector
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let L := Real.log (N : ℝ)
  let Ψ := scalarScale (spectralScale z) ε
  intro hballs hnear
  have hδ := hchange g o z hz hzB hfloor badCount hsource boundary samples hballs hnear
  have hε : 0 ≤ ε := graphPaperError_nonnegative a d N _ z (by omega) hz.le
  have hΨ : 0 ≤ Ψ := scalarScale_nonneg hε
  have hLp : 0 < L := by dsimp only [L]; linarith
  have hεone : ε ≤ 1 := (hsmall z hz hfloor).trans (inv_le_one_of_one_le₀ (one_le_pow₀ hlog))
  have hwidth := source_bounded_width B z ε hzB hεone
  have hsqrt : 0 < Real.sqrt (spectralScale z + ε) := Real.sqrt_pos.mpr
    (by linarith [spectralScale_pos hz])
  have hεscale : ε ≤ sourceWidthConstant B * Ψ := by
    calc
      _ = Real.sqrt (spectralScale z + ε) * Ψ := by
        dsimp only [Ψ, scalarScale]
        field_simp [ne_of_gt hsqrt]
      _ ≤ _ := mul_le_mul_of_nonneg_right hwidth hΨ
  have hLpower : L ≤ L ^ 16 := by
    calc
      _ = L ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hlog (by omega)
  have herror : ε / L ^ 16 ≤ Ψ := by
    apply (div_le_iff₀ (pow_pos hLp _)).mpr
    exact hεscale.trans (by nlinarith only [mul_le_mul_of_nonneg_right (hwidthLarge.trans hLpower) hΨ])
  have htri := norm_sub_le_norm_sub_add_norm_sub (h.Q z) (g.Q z) (semicircleRoot z)
  have hdist : ‖h.Q z - g.Q z‖ ≤ ε / L ^ 16 := by simpa only [norm_sub_rev] using hδ
  exact (htri.trans (add_le_add hdist hsource.2.1)).trans
    ((add_le_add_right herror Ψ).trans_eq (by dsimp only [Ψ, ε, sourceScale]; ring))

end RegularGraph
end LocalLaw
