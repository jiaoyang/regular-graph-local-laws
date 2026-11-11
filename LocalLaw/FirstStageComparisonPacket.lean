import LocalLaw.FirstStageNearCaps

/-! # Literal first-stage comparison inputs and enlarged-event membership

The frozen-boundary physical comparisons and the two boundary-parameter
changes are separate fields. None of the fields is a probability statement
or the desired enlarged event. The latter follows with realized source
logarithmic budgets and the proved Q-prior transfer.
-/

noncomputable section
namespace LocalLaw
local instance firstStageComparisonPacketDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}

structure FirstStageComparisonPacket (g h : RegularGraph N d) (T : Set (Fin N))
    (a r rn : ℕ) (z : ℂ) (Dfull Ddeleted : ℝ) : Prop where
  fullFrozen : ∀ i j, ‖h.G z i j - h.P r z (g.Q z) i j‖ ≤ Dfull / Real.log (N : ℝ)
  deletedFrozen : ∀ i j : (Tᶜ : Set (Fin N)),
    ‖(h.deficient.delete T).G z i j - h.deletedP T r z (g.Q z) i j‖ ≤ Ddeleted * g.sourcePrime a rn z
  fullBoundary : ∀ i j, ‖h.P r z (g.Q z) i j - h.P r z (h.Q z) i j‖ ≤ 1 / Real.log (N : ℝ)
  deletedBoundary : ∀ i j : (Tᶜ : Set (Fin N)),
    ‖h.deletedP T r z (g.Q z) i j - h.deletedP T r z (h.Q z) i j‖ ≤ g.sourcePrime a rn z

theorem eventually_firstStage_plus_of_comparison_packet (a b d : ℕ) (c β B Dfull Ddeleted C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hB : 0 ≤ B)
    (hDfull : 1 ≤ Dfull) (_hDdeleted : 0 ≤ Ddeleted)
    (hCfull : Dfull + 1 ≤ C1) (hCdeleted : Ddeleted + 1 ≤ C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ∀ Cq badCount : ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (finiteOmega d) badCount z →
      ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))),
      let ell := actualCavityDepth a d N z - 1
      let T := graphBallVertices g.graph o ell
      let R := logarithmicRadius (c / 4) d N
      let r := effectiveModelRadius a d N β
      let rn := logarithmicRadius β d N
      let h := g.labelledResampledGraph T boundary samples (R / 4)
      h.SourceStructuralPlus R (finiteOmega d) Cq badCount →
      FirstStageComparisonPacket g h T a r rn z Dfull Ddeleted →
      h.SourceOmegaPlusWithRadii a r rn R ell (finiteOmega d) Cq badCount C1 o z := by
  filter_upwards [eventually_firstStage_Q_prior_of_near_comparison a b d c β B Dfull ha hb hd hc hβ hβc hB hDfull,
    eventually_log_ge_nat 1, Filter.eventually_ge_atTop 1] with N hprior hlog hN
  intro g o z hz hzB hfloor Cq badCount hsource ι _ boundary samples
  dsimp only
  let ell := actualCavityDepth a d N z - 1
  let T := graphBallVertices g.graph o ell
  let R := logarithmicRadius (c / 4) d N
  let r := effectiveModelRadius a d N β
  let rn := logarithmicRadius β d N
  let s := g.admissibleState T boundary samples
  let h := g.labelledResampledGraph T boundary samples (R / 4)
  let L := Real.log (N : ℝ)
  let ε := graphPaperError a d N rn z
  let εprime := g.sourcePrime a rn z
  intro hstruct P
  have hLp : 0 < L := by dsimp only [L]; linarith
  have hε : 0 ≤ ε := graphPaperError_nonnegative a d N rn z hN hz.le
  have hprime0 : 0 ≤ εprime := by dsimp only [εprime, sourcePrime, inflatedPrime]; positivity
  have hnear : g.nearFrozenBoundaryComparison h r Dfull z := by
    intro i j _
    exact P.fullFrozen i j
  have hQprior := hprior g o z hz hzB hfloor badCount hsource boundary samples hstruct.1 hnear
  have hTnew : graphBallVertices h.graph o ell = T := by
    simpa only [graphSetBall_singleton] using s.fullResample_ball (R / 4) {o} ell
      (by rw [graphSetBall_singleton]; rfl)
  refine ⟨hstruct, ?_, ?_, ?_⟩
  · exact hQprior.trans (mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ C1) (scalarScale_nonneg hε))
  · intro i j
    have hh := (norm_sub_le_norm_sub_add_norm_sub (h.G z i j) (h.P r z (g.Q z) i j) (h.P r z (h.Q z) i j)).trans
      (add_le_add (P.fullFrozen i j) (P.fullBoundary i j))
    have hb : Dfull / L + 1 / L ≤ C1 / L := by
      calc
        _ = (Dfull + 1) / L := by ring
        _ ≤ C1 / L := div_le_div_of_nonneg_right hCfull hLp.le
    exact hh.trans hb
  · dsimp only
    rw [hTnew]
    intro i j
    have hh := (norm_sub_le_norm_sub_add_norm_sub ((h.deficient.delete T).G z i j)
      (h.deletedP T r z (g.Q z) i j) (h.deletedP T r z (h.Q z) i j)).trans
      (add_le_add (P.deletedFrozen i j) (P.deletedBoundary i j))
    exact hh.trans (by
      change Ddeleted * εprime + εprime ≤ C1 * εprime
      have hb := mul_le_mul_of_nonneg_right hCdeleted hprime0
      nlinarith only [hb])

end RegularGraph
end LocalLaw
