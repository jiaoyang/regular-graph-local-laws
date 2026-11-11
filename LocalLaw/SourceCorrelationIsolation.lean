import LocalLaw.CorrelationIsolation
import LocalLaw.SourceCorrelationProbability

/-!
# Actual Green-correlation pair isolation with quadratic-log exceptions

The one-draw inverse-log probability comes from the actual deleted variance
cap and Ward counting. Factorial matching and fixed-root-hit tails control
the number of labels correlated to another sample or any original boundary
endpoint. This supplies a stronger isolated-good-pair property with O(log² N)
exceptions, rather than assuming independence of overlapping pair events.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceCorrelationIsolationDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace RegularGraph
variable {N d : ℕ}

def outsideFirstPoint (g : RegularGraph N d) (T : Set (Fin N))
    (e : OutsideOrientedEdge g.graph T) : (Tᶜ : Set (Fin N)) := ⟨e.val.1, e.property.2.1⟩

def outsideSecondPoint (g : RegularGraph N d) (T : Set (Fin N))
    (e : OutsideOrientedEdge g.graph T) : (Tᶜ : Set (Fin N)) := ⟨e.val.2, e.property.2.2⟩

def deletedVertexCorrelation (g : RegularGraph N d) (T : Set (Fin N)) (z : ℂ) (φ : ℝ) (radius : ℕ)
    (x y : (Tᶜ : Set (Fin N))) : Prop :=
  y ∈ wardCorrelatedVertices (outsideGraph g.graph T) (normalizedAdjacency (outsideGraph g.graph T) d)
    z φ radius x

theorem deletedVertexCorrelation_symmetric (g : RegularGraph N d) (T : Set (Fin N))
    (z : ℂ) (φ : ℝ) (radius : ℕ) : Symmetric (g.deletedVertexCorrelation T z φ radius) := by
  have hsym : (green (normalizedAdjacency (outsideGraph g.graph T) d) z).IsSymm := by
    have hh := (g.deficient.delete T).extensionGreen_isSymm (0 : ℂ) z
    simpa only [DeficientGraph.extensionGreen, DeficientGraph.H, boundaryGreen, boundaryMatrix,
      zero_smul, sub_zero, green] using hh
  intro x y h
  rw [deletedVertexCorrelation, mem_wardCorrelatedVertices] at h ⊢
  rcases h with h | ⟨u, hu, v, hv, huv⟩
  · exact Or.inl (by simpa only [SimpleGraph.edist_comm] using h)
  · exact Or.inr ⟨v, hv, u, hu, by simpa only [hsym.apply u v] using huv⟩

theorem outsideCorrelatedVertices_val_iff (g : RegularGraph N d) (T : Set (Fin N))
    (z : ℂ) (φ : ℝ) (radius : ℕ) (x y : (Tᶜ : Set (Fin N))) :
    y.val ∈ g.outsideCorrelatedVertices T z φ radius x ↔ g.deletedVertexCorrelation T z φ radius x y := by
  constructor
  · intro h
    obtain ⟨v, hv, hval⟩ := Finset.mem_image.mp h
    have heq : v = y := Subtype.ext hval
    simpa only [heq] using hv
  · intro h
    exact Finset.mem_image.mpr ⟨y, h, rfl⟩

theorem endpointRelated_deleted_eq_correlated_event (g : RegularGraph N d) (T : Set (Fin N))
    (z : ℂ) (φ : ℝ) (radius : ℕ) (x : (Tᶜ : Set (Fin N))) :
    endpointRelated (g.deletedVertexCorrelation T z φ radius) (g.outsideFirstPoint T) (g.outsideSecondPoint T) x =
      (fun e => outsideEdgeFirst g.graph T e ∈ g.outsideCorrelatedVertices T z φ radius x ∨
        outsideEdgeSecond g.graph T e ∈ g.outsideCorrelatedVertices T z φ radius x) := by
  funext e
  apply propext
  exact (g.outsideCorrelatedVertices_val_iff T z φ radius x (g.outsideFirstPoint T e)).symm.or
    (g.outsideCorrelatedVertices_val_iff T z φ radius x (g.outsideSecondPoint T e)).symm

theorem correlatedSampleIndices_eq_related (g : RegularGraph N d) (T : Set (Fin N))
    (z : ℂ) (φ : ℝ) (radius : ℕ) (x : (Tᶜ : Set (Fin N))) (S : LocalSamplingFiber g.graph T) :
    g.correlatedSampleIndices T z φ radius x S =
      relatedSampleIndices (g.deletedVertexCorrelation T z φ radius)
        (g.outsideFirstPoint T) (g.outsideSecondPoint T) x S := by
  ext a
  simp only [correlatedSampleIndices, badSampleIndices, correlatedOutsideEdges,
    relatedSampleIndices, Finset.mem_filter, Finset.mem_univ, true_and,
    g.endpointRelated_deleted_eq_correlated_event]

def sourceGreenIsolationBad (g : RegularGraph N d) (T : Set (Fin N)) (z : ℂ) (φ : ℝ) (radius k : ℕ)
    (S : LocalSamplingFiber g.graph T) : Prop :=
  k ≤ (badSampleIndices (oldPointHitSet (g.deletedVertexCorrelation T z φ radius)
    (g.outsideFirstPoint T) (g.outsideSecondPoint T) (boundaryOutsideVertex g.graph T)) S).card ∨
  2 * k * (2 * k + 1) ≤ (sampleCollisionGraph
    (pairEndpointRelated (g.deletedVertexCorrelation T z φ radius)
      (g.outsideFirstPoint T) (g.outsideSecondPoint T))
    (pairEndpointRelated_symmetric _ (g.deletedVertexCorrelation_symmetric T z φ radius) _ _) S).support.toFinset.card

end RegularGraph

def sourceCorrelationProbabilityConstant (C1 : ℝ) (d : ℕ) : ℝ :=
  4 * (1 + ((d + 1 : ℕ) : ℝ) ^ 2 * sourceDeletedVarianceConstant C1 d)

theorem sourceCorrelationProbabilityConstant_nonnegative (C1 : ℝ) (d : ℕ) (hC1 : 0 ≤ C1) (hd : 3 ≤ d) :
    0 ≤ sourceCorrelationProbabilityConstant C1 d := by
  have hh := sourceDeletedVarianceConstant_nonnegative C1 d hC1 hd
  unfold sourceCorrelationProbabilityConstant
  positivity

/-- Actual one-edge rare-event bound under the enlarged source event. -/
theorem eventually_sourceOmegaPlusWithRadii_endpoint_probability
    (a b d : ℕ) (c β C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d)
    (hc : 0 < c) (hc₁ : c < 1) (hβ : 0 < β) (hβc : β ≤ c / 32) (hC1 : 0 ≤ C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1)
        (finiteOmega d) Cq badCount C1 o z →
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      let φ := correlationThreshold (Real.log (N : ℝ)) a N z.im (graphKestenMcKayReference d z).im
        (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z)
      ∀ x : (Tᶜ : Set (Fin N)),
        eventMass (finiteUniformWeight (OutsideOrientedEdge g.graph T))
          (endpointRelated (g.deletedVertexCorrelation T z φ (logarithmicRadius (c / 4) d N / 4))
            (g.outsideFirstPoint T) (g.outsideSecondPoint T) x) ≤
          sourceCorrelationProbabilityConstant C1 d / Real.log (N : ℝ) ^ (4 * a) := by
  have ha0 : 0 < a := by omega
  let C := finiteExtraReferenceConstant d
  let C₀ := coreConvolutionConstant (finiteOmega d + 1)
  have hC : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have hC₀ : 0 ≤ C₀ := coreConvolutionConstant_nonnegative (finiteOmega d + 1)
  have hfeedback := eventually_source_kernel_feedback a b d β C1 (2 * C) C₀
    ha hb hd hβ hC1 (by positivity) hC₀
  have hdepth := (lowerLogLogRadius_tendsto a d ha0 hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [RegularGraph.eventually_outside_correlated_endpoint_probability a d c hd hc.le hc₁,
    hfeedback, eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    hdepth, eventually_selected_resampling_budget a d hd ha0,
    eventually_log_ge_nat 1, Filter.eventually_ge_atTop 1] with
      N htail hfeedback hmargin hdepth hbudget hlog hN
  intro g o z hz hscale Cq badCount hplus
  dsimp only
  intro x
  let r := effectiveModelRadius a d N β
  let rn := logarithmicRadius β d N
  let R := logarithmicRadius (c / 4) d N
  let ell := actualCavityDepth a d N z - 1
  let T := graphBallVertices g.graph o ell
  let ε := graphPaperError a d N rn z
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hfit : r + 2 * ell + 1 ≤ R / 8 := by dsimp only [r, R]; omega
  have hrn : r ≤ rn := Nat.sub_le _ _
  have hsmall : ‖g.Q z - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * (4 * (r : ℝ) + 2) ≤ 1 / 2 := by
    have hh := hfeedback z (g.Q z) hz hscale hplus.cavity
    have hcast : (r : ℝ) ≤ rn := Nat.cast_le.mpr hrn
    calc
      _ ≤ ‖g.Q z - semicircleRoot z‖ * C * C₀ * (2 * (2 * (rn : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ‖g.Q z - semicircleRoot z‖ * (2 * C) * C₀ * (2 * (rn : ℝ) + 1) := by ring
      _ ≤ 1 / 2 := hh
  have hcap := hplus.actual_diagonal_variance_cap hN hd hz hC1 hfit hsmall
  have hv : 0 ≤ (graphKestenMcKayReference d z).im :=
    (kestenMcKayTransform_im_pos d (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le).le
  have hLp : 0 < Real.log (N : ℝ) := by linarith
  have hk : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hfloor : 0 < localizationErrorFloor a d N rn := by unfold localizationErrorFloor; positivity
  have hε : 0 < ε := hfloor.trans_le (graphPaperError_lower a d N rn z hlog hz.le)
  have hp := htail g T (g.ball_small o ell (hbudget z)) z hz (graphKestenMcKayReference d z).im
    (spectralScale z) ε (sourceDeletedVarianceConstant C1 d) hv hε x (fun u _ => hcap u)
  rw [g.endpointRelated_deleted_eq_correlated_event]
  exact hp

/-- The actual quadratic-log isolated-good-pair event has every polynomial
failure bound. Per-point occupation, pair collisions and fixed old roots
are all counted under the genuine uniform sampling function space. -/
theorem eventually_sourceGreenIsolation_bad_probability
    (a b d q : ℕ) (c β C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d)
    (hc : 0 < c) (hc₁ : c < 1) (hβ : 0 < β) (hβc : β ≤ c / 32) (hC1 : 0 ≤ C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1)
        (finiteOmega d) Cq badCount C1 o z →
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      let φ := correlationThreshold (Real.log (N : ℝ)) a N z.im (graphKestenMcKayReference d z).im
        (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z)
      eventMass (localSamplingWeight g.graph T)
        (g.sourceGreenIsolationBad T z φ (logarithmicRadius (c / 4) d N / 4)
          (Nat.ceil (Real.log (N : ℝ)))) ≤ 3 / (N : ℝ) ^ q := by
  let P0 := sourceCorrelationProbabilityConstant C1 d
  let M : ℝ := (d : ℝ) * ((d : ℝ) + 1)
  let C0 := M ^ 2 * P0
  have hP0 : 0 ≤ P0 := sourceCorrelationProbabilityConstant_nonnegative C1 d hC1 hd
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hC0 : 0 ≤ C0 := by dsimp only [C0]; positivity
  have ha0 : 0 < a := by omega
  filter_upwards [eventually_sourceOmegaPlusWithRadii_endpoint_probability a b d c β C1 ha hb hd hc hc₁ hβ hβc hC1,
    eventually_sourceOmegaPlusWithRadii_few_correlated_samples a b d q c β C1 ha hb hd hc hc₁ hβ hβc hC1,
    eventually_actual_boundary_card_log_bound a d hd ha0,
    eventually_bounded_mean_factorial_tail q (2 * C0) (by positivity),
    eventually_selected_resampling_budget a d hd ha0,
    eventually_log_ge_nat 1, Filter.eventually_ge_atTop 1] with
      N hprobability hoccupancy hcount hfactorial hbudget hlog hN
  intro g o z hz hscale Cq badCount hplus
  dsimp only
  let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
  let X := (Tᶜ : Set (Fin N))
  let E := OutsideOrientedEdge g.graph T
  let I := BoundaryOrientedEdge g.graph T
  let φ := correlationThreshold (Real.log (N : ℝ)) a N z.im (graphKestenMcKayReference d z).im
    (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z)
  let radius := logarithmicRadius (c / 4) d N / 4
  let Rv := g.deletedVertexCorrelation T z φ radius
  let first := g.outsideFirstPoint T
  let second := g.outsideSecondPoint T
  let old := boundaryOutsideVertex g.graph T
  let L := Real.log (N : ℝ)
  let k := Nat.ceil L
  let pN := P0 / L ^ (4 * a)
  letI : Nonempty E := g.outside_edge_nonempty T (by omega) (by omega)
    (g.ball_small o _ (hbudget z))
  have hLp : 0 < L := by linarith
  have hpN : 0 ≤ pN := div_nonneg hP0 (pow_nonneg hLp.le _)
  have hrare : ∀ x : X, eventMass (finiteUniformWeight E) (endpointRelated Rv first second x) ≤ pN :=
    hprobability g o z hz hscale Cq badCount hplus
  have hμ : (Fintype.card I : ℝ) ≤ M * L ^ (2 * a) := by
    simpa only [Nat.card_eq_fintype_card] using hcount g o z
  have hmean : ((Fintype.card I : ℝ) ^ 2) * pN ≤ C0 := by
    have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hμ 2) hpN
    apply hh.trans_eq
    dsimp only [pN, C0]
    have heq : (L ^ (2 * a)) ^ 2 = L ^ (4 * a) := by
      rw [← pow_mul]
      congr 1
      omega
    rw [mul_pow, heq]
    field_simp [ne_of_gt hLp]
    ring
  have hmean2 : ((Fintype.card I : ℝ) ^ 2) * (2 * pN) ≤ 2 * C0 := by nlinarith only [hmean]
  have hmean1 : ((Fintype.card I : ℝ) ^ 2) * pN ≤ 2 * C0 := by linarith only [hmean, hC0]
  have hfixed := hfactorial _ (by positivity : 0 ≤ ((Fintype.card I : ℝ) ^ 2) * pN) hmean1
  have hpairs := hfactorial _ (by positivity : 0 ≤ ((Fintype.card I : ℝ) ^ 2) * (2 * pN)) hmean2
  have hocc := hoccupancy g o z hz hscale Cq badCount hplus
  dsimp only at hocc
  have hocc' : eventMass (finiteUniformWeight (I → E)) (fun f =>
      ∃ x : X, k ≤ (relatedSampleIndices Rv first second x f).card) ≤ 1 / (N : ℝ) ^ q := by
    simpa only [g.correlatedSampleIndices_eq_related] using hocc
  have htail := uniform_correlation_isolation_failure Rv (g.deletedVertexCorrelation_symmetric T z φ radius)
    first second old k pN hpN hrare
  change eventMass (finiteUniformWeight (I → E)) _ ≤ _
  apply htail.trans
  change _ ≤ 3 / (N : ℝ) ^ q
  dsimp only [I, E, k, L] at hocc' hfixed hpairs ⊢
  calc
    _ ≤ (1 / (N : ℝ) ^ q) + (1 / (N : ℝ) ^ q) + (1 / (N : ℝ) ^ q) :=
      add_le_add (add_le_add hocc' hfixed) hpairs
    _ = _ := by ring

end LocalLaw
