import LocalLaw.UniversalBadCenterParameters
import LocalLaw.FourPathPatternProbability
import LocalLaw.StructuralEventTransfer

/-!
# Radius-offset auxiliary events and the original conditioning

The proof can require the stronger radius-(R+J) tree test. Its loss has every
polynomial bound under the actual graph law; the original structural-event
conditioning and its proved mass are retained in the final transfer.
-/

namespace LocalLaw
noncomputable section
local instance offsetStructuralDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Tree neighborhoods are preserved under decreasing the radius. -/
theorem graphBall_tree_mono (G : SimpleGraph V) (o : V) {r R : ℕ} (hr : r ≤ R)
    (hR : (graphBall G o R).IsTree) : (graphBall G o r).IsTree := by
  let f : graphBall G o r →g graphBall G o R :=
    { toFun := fun v => ⟨v.val, graphBallVertices_mono G o hr v.property⟩
      map_rel' := fun h => h }
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (congrArg (fun x : graphBallVertices G o R => x.val) h)
  refine ⟨graphBall_connected G o r, ?_⟩
  intro a p hp
  exact hR.IsAcyclic (p.map f) (hp.map hf)

omit [DecidableEq V] in
theorem nonTreeCenters_mono (G : SimpleGraph V) {r R : ℕ} (hr : r ≤ R) :
    nonTreeCenters G r ⊆ nonTreeCenters G R := by
  intro v hv
  rw [nonTreeCenters_membership] at hv ⊢
  exact fun h => hv (graphBall_tree_mono G v hr h)

namespace RegularGraph
variable {N d : ℕ}

/-- The excess is tested at the source radius, while tree centers are tested
at the larger offset radius required by pair neighborhoods. -/
def offsetStructural (R ω J badCount : ℕ) (g : RegularGraph N d) : Prop :=
  (∀ o, graphBallExcess g.graph o R ≤ ω) ∧ (nonTreeCenters g.graph (R + J)).card ≤ badCount

theorem offsetStructural_implies_structural {R ω J badCount : ℕ} {g : RegularGraph N d}
    (h : offsetStructural R ω J badCount g) : structural R ω badCount g :=
  ⟨h.1, (Finset.card_le_card (nonTreeCenters_mono g.graph (Nat.le_add_right R J))).trans h.2⟩

end RegularGraph

/-- Requiring the enlarged tree-test radius loses only an arbitrary
polynomial amount, with no larger-radius excess assumption. -/
theorem eventually_offset_structural_difference (d ω J p : ℕ) (c γ : ℝ)
    (hd : 3 ≤ d) (hc : 0 ≤ c) (hγ : 3 * c / 4 < γ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ badCount : ℕ,
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        RegularGraph.structural (logarithmicRadius (c / 4) d N) ω badCount g ∧
          ¬RegularGraph.offsetStructural (logarithmicRadius (c / 4) d N) ω J ⌊(N : ℝ) ^ γ⌋₊ g) ≤
        1 / (N : ℝ) ^ p := by
  filter_upwards [eventually_universal_badCenter_probability d J p c γ hd hc hγ] with N htail
  intro badCount
  apply (eventMass_mono RegularGraph.weight RegularGraph.weight_nonnegative ?_).trans htail
  intro g hg
  by_contra hnot
  have hle : ((nonTreeCenters g.graph (logarithmicRadius (c / 4) d N + J)).card : ℝ) ≤ (N : ℝ) ^ γ :=
    le_of_not_gt hnot
  have hf := (Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) γ)).mpr hle
  exact hg.2 ⟨hg.1.1, hf⟩

/-- The strengthened offset event itself has positive mass; the denominator
of the original conditioning is supplied by the proved source structural bound. -/
theorem eventually_offset_structural_mass_quarter (d ω J : ℕ) (c γ : ℝ)
    (hd : 3 ≤ d) (hω : 1 ≤ ω) (hc : 0 < c) (hc₁ : c < 1) (hγ : 3 * c / 4 < γ) :
    ∀ᶠ N : ℕ in Filter.atTop, Nonempty (RegularGraph N d) →
      1 / 4 ≤ eventMass (RegularGraph.weight (N := N) (d := d))
        (RegularGraph.offsetStructural (logarithmicRadius (c / 4) d N) ω J ⌊(N : ℝ) ^ γ⌋₊) := by
  filter_upwards [eventually_original_structural_mass_half d ω c hd hω hc hc₁,
    eventually_offset_structural_difference d ω J 1 c γ hd hc.le hγ,
    Filter.eventually_ge_atTop 4] with N hmass hloss hN
  intro hnonempty
  apply strengthened_event_mass_lower RegularGraph.weight RegularGraph.weight_nonnegative
    (RegularGraph.structural (logarithmicRadius (c / 4) d N) ω ⌊(N : ℝ) ^ c⌋₊)
    _ (hmass hnonempty)
  have hh := hloss ⌊(N : ℝ) ^ c⌋₊
  apply hh.trans
  norm_num only [pow_one]
  exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) (Nat.cast_le.mpr hN)

/-- The final conditional transfer uses the ORIGINAL source event, even when
the bootstrap requires tree tests at an enlarged fixed-offset radius. -/
theorem eventually_offset_original_failure_transfer (d ω J p : ℕ) (c γ : ℝ)
    (hd : 3 ≤ d) (hω : 1 ≤ ω) (hc : 0 < c) (hc₁ : c < 1) (hγ : 3 * c / 4 < γ) :
    ∀ᶠ N : ℕ in Filter.atTop, Nonempty (RegularGraph N d) →
      ∀ (failure : RegularGraph N d → Prop) (β : ℝ), 0 ≤ β →
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        RegularGraph.offsetStructural (logarithmicRadius (c / 4) d N) ω J ⌊(N : ℝ) ^ γ⌋₊ g ∧ failure g) ≤ β →
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        RegularGraph.structural (logarithmicRadius (c / 4) d N) ω ⌊(N : ℝ) ^ c⌋₊ g ∧ failure g) /
        eventMass (RegularGraph.weight (N := N) (d := d))
          (RegularGraph.structural (logarithmicRadius (c / 4) d N) ω ⌊(N : ℝ) ^ c⌋₊) ≤
        2 / (N : ℝ) ^ p + 2 * β := by
  filter_upwards [eventually_original_structural_mass_half d ω c hd hω hc hc₁,
    eventually_offset_structural_difference d ω J p c γ hd hc.le hγ] with N hmass hloss
  intro hnonempty failure β hβ hinside
  have hh := strengthened_event_conditional_failure RegularGraph.weight RegularGraph.weight_nonnegative
    (RegularGraph.structural (logarithmicRadius (c / 4) d N) ω ⌊(N : ℝ) ^ c⌋₊)
    (RegularGraph.offsetStructural (logarithmicRadius (c / 4) d N) ω J ⌊(N : ℝ) ^ γ⌋₊)
    failure (1 / (N : ℝ) ^ p) β (by positivity) hβ (hmass hnonempty) (hloss _) hinside
  convert hh using 1
  ring

end
end LocalLaw
