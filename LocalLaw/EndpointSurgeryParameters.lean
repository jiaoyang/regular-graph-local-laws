import LocalLaw.AdmissibleEndpointPatches
import LocalLaw.AdmissibleGreenBlock
import LocalLaw.SourceSurgeryParameters

/-!
# Actual endpoint dimension and realized surgery smallness

An explicit finite endpoint encoding counts boundary roots and the two
endpoints of each accepted sample. The real source logarithmic count and
nominal error then realize the finite-rank contraction uniformly in z.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance endpointSurgeryParametersDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type*} [Fintype V] {T : Set V} {ι : Type*} [Fintype ι]

theorem endpointModelRoots_card (s : LabelledResamplingState V T ι) (selector : ℕ) :
    Nat.card (s.endpointModelRoots selector) ≤ 3 * Nat.card (BoundaryOrientedEdge s.graph T) := by
  let J := BoundaryOrientedEdge s.graph T ⊕ (s.AdmissibleSampleIndex selector × Bool)
  let f : J → s.endpointModelRoots selector := fun j => match j with
    | Sum.inl a => ⟨boundaryOuterEndpoint s.graph T a, Or.inl ⟨a, rfl⟩⟩
    | Sum.inr (i, false) => ⟨s.admissibleSampleVertex selector i,
        Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_insert _ _⟩)⟩
    | Sum.inr (i, true) => ⟨s.admissibleSecondVertex selector i,
        Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_insert_of_mem _ (Set.mem_singleton _)⟩)⟩
  have hf : Function.Surjective f := by
    rintro ⟨v, hv⟩
    rcases hv with hv | hv
    · obtain ⟨a, rfl⟩ := hv
      exact ⟨Sum.inl a, rfl⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
      simp only [admissiblePairRoots, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      rcases hi with rfl | rfl
      · exact ⟨Sum.inr (i, false), rfl⟩
      · exact ⟨Sum.inr (i, true), rfl⟩
  have hsub : Nat.card (s.AdmissibleSampleIndex selector) ≤ Nat.card ι :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hι : Nat.card ι = Nat.card (BoundaryOrientedEdge s.graph T) := Nat.card_congr s.boundary
  have hh := Nat.card_le_card_of_surjective f hf
  have hbool : Nat.card Bool = 2 := by simp only [Nat.card_eq_fintype_card, Fintype.card_bool]
  simp only [J, Nat.card_sum, Nat.card_prod, hbool] at hh
  omega

end LabelledResamplingState

namespace RegularGraph

/-- The actual finite endpoint contraction holds for every labelled sample
and every selector, at every allowed source radius, eventually. -/
theorem eventually_endpoint_surgery_smallness (a b d : ℕ) (β C w D : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hβ : 0 < β)
    (hC : 0 ≤ C) (hw : 0 ≤ w) (hD : 0 ≤ D) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (ell : ℕ),
      ell ≤ doubleLogRadius a d N → ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) (selector : ℕ) (z : ℂ),
      0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      let s := g.admissibleState (graphBallVertices g.graph o ell) boundary samples
      (Nat.card (s.endpointModelRoots selector) : ℝ) * (1 + C * w) * w *
        (D * g.sourcePrime a (logarithmicRadius β d N) z) ≤ 1 / 2 := by
  let U : ℝ := 3 * (d : ℝ) * ((d : ℝ) + 1)
  filter_upwards [eventually_paperError_small a b d β ha hb hd hβ, eventually_log_ge_nat 1,
    eventually_log_ge_nat (2 * (U * (1 + C * w) * w * D)), Filter.eventually_ge_atTop 1]
    with N hsmall hL hlarge hN
  intro g o ell hell ι _ boundary samples selector z hz hscale
  let s := g.admissibleState (graphBallVertices g.graph o ell) boundary samples
  let L := Real.log (N : ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  have hε : 0 ≤ ε := graphPaperError_nonnegative a d N _ z hN hz.le
  have hcap : ε * L ^ (4 * a) ≤ 1 := by
    exact (le_div_iff₀ (pow_pos (by linarith : 0 < L) _)).mp
      (by simpa only [one_div] using hsmall z hz hscale)
  have hcount : (Nat.card (s.endpointModelRoots selector) : ℝ) ≤ U * L ^ (2 * a) := by
    have hnat := s.endpointModelRoots_card selector
    have hreal : (Nat.card (s.endpointModelRoots selector) : ℝ) ≤
        3 * (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ) := by exact_mod_cast hnat
    apply hreal.trans
    have hh := mul_le_mul_of_nonneg_left (g.boundary_card_log_bound o a ell hd hL hell) (by norm_num : (0 : ℝ) ≤ 3)
    exact hh.trans_eq (by dsimp only [U]; ring)
  have hh := source_endpoint_surgery_smallness a L ε (Nat.card (s.endpointModelRoots selector) : ℝ)
    U C w D (by omega) hL hε (by dsimp only [U]; positivity) hC hw hD hcap hcount hlarge
  convert hh using 1
  unfold sourcePrime inflatedPrime
  ring

end RegularGraph
end LocalLaw
