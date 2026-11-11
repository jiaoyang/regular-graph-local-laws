import LocalLaw.FiniteLocalization
import LocalLaw.ComponentwiseReferenceBounds
import LocalLaw.DeficientGraphIso
import LocalLaw.ComponentPairGeometry

/-!
# Actual pair localization in possibly disconnected finite models

Each genuine component may be in the base reference class or in its proved
positive-deficit extension. Connected pair neighborhoods use localization on
their actual component; disconnected pairs contribute only the proved decay
tail. No global total-excess assumption is made.
-/

noncomputable section
namespace LocalLaw
local instance componentFiniteLocalizationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) canonicalComponentFiniteLocalizationMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

/-- The actual allowed reference class is checked separately on each block. -/
def ComponentFiniteReferenceBudget (g : DeficientGraph V d) : Prop :=
  ∀ c : g.graph.ConnectedComponent, (g.restrict c.supp).FiniteReferenceBudget

omit [DecidableEq V] in
theorem ComponentReferenceBudget.to_componentFinite {g : DeficientGraph V d}
    (h : g.ComponentReferenceBudget) : g.ComponentFiniteReferenceBudget := fun c => Or.inl (h c)

theorem componentwise_finite_kernel_decay (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hbudget : g.ComponentFiniteReferenceBudget) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2) (i j : V) :
    ‖g.extensionGreen q z i j‖ ≤
      2 * finiteExtraReferenceConstant d * physicalTransfer d z ^ g.graph.dist i j := by
  let c := g.graph.connectedComponentMk i
  let gc := g.restrict c.supp
  have hC : 0 ≤ finiteExtraReferenceConstant d := (by norm_num : (0 : ℝ) ≤ 1).trans
    (finiteExtraReferenceConstant_ge_one d hd)
  by_cases hj : j ∈ c.supp
  · have hconn : gc.graph.Connected := c.connected_induce_supp
    have hdiam : ∀ a b, gc.graph.dist a b ≤ R := by
      intro a b
      change (g.graph.induce c.supp).dist a b ≤ R
      rw [isolated_induce_distance g.graph c.supp (g.component_cut c)]
      exact hR a.val b.val
    have hh := gc.finite_class_kernel_bound hd hconn (hbudget c) z q hz hq R hdiam small ⟨i, rfl⟩ ⟨j, hj⟩
    rw [g.restrict_extensionGreen_of_isolated hd c.supp (g.component_cut c) q z hz hq] at hh
    simp only [Matrix.submatrix_apply, referenceDecay] at hh
    change ‖g.extensionGreen q z i j‖ ≤ 2 * finiteExtraReferenceConstant d * physicalTransfer d z ^
      (g.graph.induce c.supp).dist ⟨i, rfl⟩ ⟨j, hj⟩ at hh
    rw [isolated_induce_distance g.graph c.supp (g.component_cut c)] at hh
    exact hh
  · rw [g.extensionGreen_zero_across_cut hd c.supp (g.component_cut c) q z hz hq i rfl j hj,
      norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hC) (pow_nonneg (norm_nonneg _) _)

theorem pair_restriction_cross_zero (g : DeficientGraph V d) (hd : 3 ≤ d)
    (i j : V) (r : ℕ) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (hpair : ¬(pairBallGraph g.graph i j r).Connected) :
    (g.restrict (pairBallVertices g.graph i j r)).extensionGreen q z
      (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r) = 0 := by
  let gp := g.restrict (pairBallVertices g.graph i j r)
  let a := pairBallLeft g.graph i j r
  let b := pairBallRight g.graph i j r
  let c := gp.graph.connectedComponentMk a
  have hnot : b ∉ c.supp := by
    intro hh
    exact pairBall_endpoint_not_reachable g.graph i j r hpair (SimpleGraph.ConnectedComponent.exact hh.symm)
  exact gp.extensionGreen_zero_across_cut hd c.supp (gp.component_cut c) q z hz hq a rfl b hnot

def finitePairLocalizationBound (d : ℕ) (q z : ℂ) (Bcap : ℝ) (R r : ℕ) : ℝ :=
  32 * finiteExtraReferenceConstant d ^ 2 * coreConvolutionConstant (finiteOmega d + 1) *
      ordinaryFeedbackBudget z q Bcap R +
    (8 * finiteExtraReferenceConstant d ^ 2 * localizationExceptionalMass d q +
      4 * finiteExtraReferenceConstant d ^ 2 * ‖q‖ * (((finiteOmega d : ℝ) + 1) / ((d : ℝ) - 1)) +
      2 * finiteExtraReferenceConstant d) * physicalTransfer d z ^ (2 * r)

theorem finitePairLocalizationBound_tail (d : ℕ) (hd : 3 ≤ d) (q z : ℂ) (Bcap : ℝ) (R r : ℕ) :
    2 * finiteExtraReferenceConstant d * physicalTransfer d z ^ (2 * r) ≤
      finitePairLocalizationBound d q z Bcap R r := by
  have hC : 0 ≤ finiteExtraReferenceConstant d := (by norm_num : (0 : ℝ) ≤ 1).trans
    (finiteExtraReferenceConstant_ge_one d hd)
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hk0 : 0 ≤ (d : ℝ) - 1 := by linarith
  have hτ := ordinaryFeedbackBudget_nonnegative z q Bcap R
  have hC0 := coreConvolutionConstant_nonnegative (finiteOmega d + 1)
  have ht : 0 ≤ physicalTransfer d z := (physicalTransfer_pos d hd z).le
  have hmass : 0 ≤ localizationExceptionalMass d q := by unfold localizationExceptionalMass; positivity
  have hfirst : 0 ≤ 32 * finiteExtraReferenceConstant d ^ 2 *
      coreConvolutionConstant (finiteOmega d + 1) * ordinaryFeedbackBudget z q Bcap R := by positivity
  have hextra : 0 ≤ (8 * finiteExtraReferenceConstant d ^ 2 * localizationExceptionalMass d q +
      4 * finiteExtraReferenceConstant d ^ 2 * ‖q‖ * (((finiteOmega d : ℝ) + 1) / ((d : ℝ) - 1))) *
        physicalTransfer d z ^ (2 * r) := by positivity
  unfold finitePairLocalizationBound
  nlinarith

/-- Finite Proposition 2.14 for the actual pair model, allowing both the
ambient finite graph and its pair neighborhood to be disconnected. -/
theorem componentwise_pair_localization (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hbudget : g.ComponentFiniteReferenceBudget)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (Bcap : ℝ) (hBcap : ‖z‖ ≤ Bcap)
    (R r : ℕ) (hR : ∀ a b, g.graph.dist a b ≤ R)
    (smallG : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2)
    (smallS : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((4 * r + 1 : ℕ) + 1 : ℝ) ≤ 1 / 2)
    (smallOutside : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * (((finiteOmega d + 1) * (2 * R + 1) : ℕ) + 1 : ℝ) ≤ 1 / 2)
    (smallCavity : ‖q - semicircleRoot z‖ * 3 * (3 / 2 : ℝ) * ((2 * R : ℕ) + 1 : ℝ) ≤ 1 / 2)
    (smallOrdinary : ordinaryFeedbackBudget z q Bcap R * (2 * finiteExtraReferenceConstant d) *
      coreConvolutionConstant (finiteOmega d + 1) * ((4 * r + 1 : ℕ) + 1 : ℝ) ≤ 1 / 2)
    (i j : V) :
    ‖g.extensionGreen q z i j - (g.restrict (pairBallVertices g.graph i j r)).extensionGreen q z
      (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r)‖ ≤
        finitePairLocalizationBound d q z Bcap R r := by
  have hC : 0 ≤ finiteExtraReferenceConstant d := (by norm_num : (0 : ℝ) ≤ 1).trans
    (finiteExtraReferenceConstant_ge_one d hd)
  have ht : 0 ≤ physicalTransfer d z := (physicalTransfer_pos d hd z).le
  have htone : physicalTransfer d z ≤ 1 := by nlinarith [physicalTransfer_sq_le_half d hd z]
  by_cases hpair : (pairBallGraph g.graph i j r).Connected
  · let c := g.graph.connectedComponentMk i
    have hij : g.graph.Reachable i j :=
      (hpair.preconnected (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r)).map
        (SimpleGraph.Embedding.induce (G := g.graph) (pairBallVertices g.graph i j r)).toHom
    have hj : j ∈ c.supp := (SimpleGraph.ConnectedComponent.sound hij).symm
    let ii : c.supp := ⟨i, rfl⟩
    let jj : c.supp := ⟨j, hj⟩
    let gc := g.restrict c.supp
    let S := pairBallVertices gc.graph ii jj r
    let φ := isolatedPairBallIso g.graph c.supp (g.component_cut c) ii jj r
    have hgc : gc.graph.Connected := c.connected_induce_supp
    have hS : (gc.graph.induce S).Connected := φ.connected_iff.mpr hpair
    have hdiam : ∀ a b, gc.graph.dist a b ≤ R := by
      intro a b
      change (g.graph.induce c.supp).dist a b ≤ R
      rw [isolated_induce_distance g.graph c.supp (g.component_cut c)]
      exact hR a.val b.val
    have hdiamS : ∀ a b, (gc.graph.induce S).dist a b ≤ 4 * r + 1 :=
      pairBall_distance_bound gc.graph ii jj r
    have hlocal := gc.finite_model_localization hd S hgc hS (hbudget c) q z hz hq Bcap hBcap
      R (4 * r + 1) hdiam hdiamS smallG smallS smallOutside smallCavity smallOrdinary
      (pairBallLeft gc.graph ii jj r) (pairBallRight gc.graph ii jj r) r (Set.Subset.refl _)
    have hbigM := g.restrict_extensionGreen_of_isolated hd c.supp (g.component_cut c) q z hz hq
    have hbig : gc.extensionGreen q z ii jj = g.extensionGreen q z i j :=
      congrFun (congrFun hbigM ii) jj
    let gp := g.restrict (pairBallVertices g.graph i j r)
    let gcp := gc.restrict S
    have hdeficit : ∀ v, gcp.deficit v = gp.deficit (φ v) := fun _ => rfl
    have hiso := gp.extensionGreen_iso gcp φ hdeficit q z
    have hsmall : gcp.extensionGreen q z (pairBallLeft gc.graph ii jj r) (pairBallRight gc.graph ii jj r) =
        gp.extensionGreen q z (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r) := by
      have hh := congrFun (congrFun hiso (pairBallLeft gc.graph ii jj r)) (pairBallRight gc.graph ii jj r)
      exact hh.symm
    change ‖gc.extensionGreen q z ii jj - gcp.extensionGreen q z
      (pairBallLeft gc.graph ii jj r) (pairBallRight gc.graph ii jj r)‖ ≤ _ at hlocal
    rw [hbig, hsmall] at hlocal
    apply hlocal.trans
    unfold finitePairLocalizationBound
    have hnonneg : 0 ≤ (2 * finiteExtraReferenceConstant d) * physicalTransfer d z ^ (2 * r) := by positivity
    nlinarith
  · rw [g.pair_restriction_cross_zero hd i j r q z hz hq hpair, sub_zero]
    by_cases hij : g.graph.Reachable i j
    · have hdist := pairBall_disconnected_distance_lower g.graph i j r hij hpair
      have hdecay := g.componentwise_finite_kernel_decay hd hbudget q z hz hq R hR smallG i j
      have hpow : physicalTransfer d z ^ g.graph.dist i j ≤ physicalTransfer d z ^ (2 * r) :=
        pow_le_pow_of_le_one ht htone (by omega)
      exact (hdecay.trans (mul_le_mul_of_nonneg_left hpow (by positivity))).trans
        (finitePairLocalizationBound_tail d hd q z Bcap R r)
    · let c := g.graph.connectedComponentMk i
      have hj : j ∉ c.supp := fun hh => hij (SimpleGraph.ConnectedComponent.exact hh.symm)
      rw [g.extensionGreen_zero_across_cut hd c.supp (g.component_cut c) q z hz hq i rfl j hj, norm_zero]
      exact (mul_nonneg (mul_nonneg (by norm_num) hC) (pow_nonneg ht _)).trans
        (finitePairLocalizationBound_tail d hd q z Bcap R r)

end DeficientGraph
end LocalLaw
