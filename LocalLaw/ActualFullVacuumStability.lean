import LocalLaw.InversePrecisionUpdate
import LocalLaw.FullQuadCouplingMass
import LocalLaw.FullMateMultiplicity
import LocalLaw.FullQuadVacuumSurgery
import LocalLaw.FullEndpointWeakCovariance
import LocalLaw.FullQuadInstanceTransport

/-! # Actual full partially retained model surgery without a new model class

The cut-core row estimate and old covariance defect are the two analytic
inputs. Coupling mass, mate multiplicity, precision identities and every
unit condition are derived for the literal full switching masks.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance actualFullVacuumStabilityDecidable (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 3000000
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem full_partial_model_vacuum_stability (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (labels : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T) (selector : ℕ) (hs : 1 ≤ selector)
    (S : Set (Fin N)) (q p z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (hq0 : q ≠ 0) (hp0 : p ≠ 0) (hrel : p⁻¹ = q⁻¹-q*treeEdgeWeight d^2)
    (P C δ : ℝ) (hP : 0 ≤ P) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hqnorm : ‖q‖ ≤ P) (hpnorm : ‖p‖ ≤ P) (hαq : ‖treeEdgeWeight d*q‖ ≤ 1) :
    let s := g.admissibleState T labels samples
    let e := s.fullPartialEmbedding selector S hs
    let G := (g.deficient.restrict S).extensionGreen q z
    let H := ((g.labelledResampledGraph T labels samples selector).deficient.restrict S).extensionGreen q z
    let A := G.submatrix (s.fullCoreEmbedding S) (s.fullCoreEmbedding S)
    let cut := g.fullCoreEdgeCutModel T labels samples selector S
    let w := 4*(d:ℝ)/Real.sqrt ((d:ℝ)-1)
    let Qraw := (fullQuadVacuumPrecision (s.fullInnerMate selector S) (s.fullOuterMate selector S)
      (s.fullFirstMask selector S) (s.fullSecondMask selector S) A⁻¹ q p (treeEdgeWeight d))⁻¹
    let Q0 : Matrix (s.FullEndpointIndex selector S) (s.FullEndpointIndex selector S) ℂ := Qraw
    (∀ i,∑ j,‖cut.extensionGreen q z (s.fullCoreEmbedding S i) (s.fullCoreEmbedding S j)‖≤C) →
    (∀ i j,‖(G.submatrix e e-s.fullOldCovariance selector S G q p (treeEdgeWeight d)) i j‖≤δ) →
    ((Fintype.card (s.FullEndpointIndex selector S):ℝ)*(1+(P+(d+2)*C)*w)*w*δ≤1/2) →
    ∀ i j,‖(H.submatrix e e-Q0) i j‖≤2*(1+(P+(d+2)*C)*w)^2*δ := by
  dsimp only
  let s := g.admissibleState T labels samples
  let e := s.fullPartialEmbedding selector S hs
  let ec := s.fullCoreEmbedding S
  let G := (g.deficient.restrict S).extensionGreen q z
  let H := ((g.labelledResampledGraph T labels samples selector).deficient.restrict S).extensionGreen q z
  let A := G.submatrix ec ec
  let inner := s.fullInnerMate selector S
  let outer := s.fullOuterMate selector S
  let BM := s.fullFirstMask selector S
  let CM := s.fullSecondMask selector S
  let w := 4*(d:ℝ)/Real.sqrt ((d:ℝ)-1)
  intro hrows herr hsmall
  have hA := (g.deficient.restrict S).extensionGreen_submatrix_isUnit hd ec q z hz hq
  have hA0 : IsUnit A⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hA
  have hAsym : A⁻¹.IsSymm := by
    have hh : A.IsSymm := by
      ext i j
      exact (DeficientGraph.extensionGreen_isSymm _ q z).apply _ _
    change (A⁻¹).transpose = A⁻¹
    rw [Matrix.transpose_nonsing_inv,hh.eq]
  have hcut := g.fullCoreEdgeCut_retained_inverse hd T labels samples selector S q z hz hq
  dsimp only at hcut
  have hcutRows : ∀ i,∑ j,‖(A⁻¹-fullQuadRetainedEdges inner outer (treeEdgeWeight d)-
      Matrix.diagonal (fun k=>q*treeEdgeWeight d^2*fullQuadRetainedDegree inner outer k))⁻¹ i j‖≤C := by
    rw [hcut.2]
    exact hrows
  have hOldInv : (fullQuadOldPrecision BM CM A⁻¹ q p (treeEdgeWeight d))⁻¹ =
      s.fullOldCovariance selector S G q p (treeEdgeWeight d) := by
    rw [(fullQuadOldPrecision_inverse BM CM A⁻¹ q p (treeEdgeWeight d) hA0 hq0 hp0 hrel).2]
    rw [Matrix.nonsing_inv_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA)]
    rfl
  have hmult (k : s.fullCoreMask S) : (Nat.card {j:BM⊕CM // fullQuadLeafMate inner outer BM CM j=some k}:ℝ)≤d+1 := by
    have hh := s.fullLeafMate_multiplicity selector S k
    have hdeg : s.graph.degree k.val = d := g.regular k.val
    rw [hdeg] at hh
    exact_mod_cast hh
  have hUpdates := g.full_partial_model_endpoint_updates hd T labels samples selector hs S q z hz hq
  dsimp only at hUpdates
  have hmass := s.fullQuadSurgeryCoupling_mass selector S hs d (fun v=>(g.regular v).le) q
    (by simpa only [mul_comm] using hαq)
  dsimp only at hmass
  let J := s.fullCoreMask S ⊕ (BM ⊕ CM)
  let φ : s.FullEndpointIndex selector S ≃ J := Equiv.refl _
  have hmassRawRows : ∀ i : J,∑ j,‖fullQuadSurgeryCoupling inner outer BM CM q (treeEdgeWeight d) i j‖≤w := by
    intro i
    refine (le_of_eq ?_).trans (hmass.1 (φ.symm i))
    apply Fintype.sum_equiv φ.symm
    intro j
    apply congrArg norm
    exact congrArg (fun M : Matrix J J ℂ => M i j)
      (fullQuadSurgeryCoupling_decidableCongr _ _ _ _ inner outer BM CM q (treeEdgeWeight d))
  have hmassRawCols : ∀ j : J,∑ i,‖fullQuadSurgeryCoupling inner outer BM CM q (treeEdgeWeight d) i j‖≤w := by
    intro j
    refine (le_of_eq ?_).trans (hmass.2 (φ.symm j))
    apply Fintype.sum_equiv φ.symm
    intro i
    apply congrArg norm
    exact congrArg (fun M : Matrix J J ℂ => M i j)
      (fullQuadSurgeryCoupling_decidableCongr _ _ _ _ inner outer BM CM q (treeEdgeWeight d))
  have hsmallRaw : (Fintype.card J:ℝ)*(1+(P+(1+((d:ℝ)+1))*C)*w)*w*δ≤1/2 := by
    rw [←Fintype.card_congr φ]
    convert hsmall using 1; ring
  let R0 : Matrix (s.fullCoreMask S ⊕ (BM ⊕ CM)) (s.fullCoreMask S ⊕ (BM ⊕ CM)) ℂ := G.submatrix e e
  let T0 : Matrix (s.fullCoreMask S ⊕ (BM ⊕ CM)) (s.fullCoreMask S ⊕ (BM ⊕ CM)) ℂ := H.submatrix e e
  have he : ∀ i j,‖(R0-(fullQuadOldPrecision BM CM A⁻¹ q p (treeEdgeWeight d))⁻¹) i j‖≤δ := by
    rw [hOldInv]
    exact herr
  have hg := fullQuadVacuum_surgery_stability inner outer BM CM A⁻¹ q p (treeEdgeWeight d)
    hA0 hAsym hq0 hp0 hrel P C ((d:ℝ)+1) w δ hP hC (by positivity) (by positivity) hδ
    hqnorm hpnorm hαq hmult hcut.1 hcutRows R0 T0 hUpdates.2.2.1 hmassRawRows hmassRawCols he hsmallRaw
  intro i j
  convert hg i j using 1; ring

end RegularGraph
end LocalLaw
