import LocalLaw.ActualFullVacuumStability
import LocalLaw.ActualPartialEndpointCaps

/-! # Genuine new full partial-endpoint rows from the old cut model -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance actualFullEndpointRowCapsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 2500000
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem full_partial_model_vacuum_row_caps (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (labels : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T) (selector : ℕ) (hs : 1 ≤ selector)
    (S : Set (Fin N)) (q p z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (hq0 : q ≠ 0) (hp0 : p ≠ 0) (hrel : p⁻¹=q⁻¹-q*treeEdgeWeight d^2)
    (P C δ : ℝ) (hP : 0≤P) (hC : 0≤C) (hδ : 0≤δ)
    (hqnorm : ‖q‖≤P) (hpnorm : ‖p‖≤P) (hαq : ‖treeEdgeWeight d*q‖≤1) :
    let s := g.admissibleState T labels samples
    let e := s.fullPartialEmbedding selector S hs
    let G := (g.deficient.restrict S).extensionGreen q z
    let H := ((g.labelledResampledGraph T labels samples selector).deficient.restrict S).extensionGreen q z
    let cut := g.fullCoreEdgeCutModel T labels samples selector S
    let w := 4*(d:ℝ)/Real.sqrt ((d:ℝ)-1)
    (∀ i,∑j,‖cut.extensionGreen q z (s.fullCoreEmbedding S i) (s.fullCoreEmbedding S j)‖≤C) →
    (∀ i j,‖(G.submatrix e e-s.fullOldCovariance selector S G q p (treeEdgeWeight d)) i j‖≤δ) →
    ((Fintype.card (s.FullEndpointIndex selector S):ℝ)*(1+(P+(d+2)*C)*w)*w*δ≤1/2) →
    ((Fintype.card (s.FullEndpointIndex selector S):ℝ)*(2*(1+(P+(d+2)*C)*w)^2*δ)≤1) →
    (∀i,∑j,‖H (e i) (e j)‖≤P+(d+2)*C+1) ∧
      (∀j,∑i,‖H (e i) (e j)‖≤P+(d+2)*C+1) := by
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
  intro hrows herr hsmall hmass
  have hcut := g.fullCoreEdgeCut_retained_inverse hd T labels samples selector S q z hz hq
  dsimp only at hcut
  have hcutRows : ∀i,∑j,‖(A⁻¹-fullQuadRetainedEdges inner outer (treeEdgeWeight d)-
      Matrix.diagonal (fun k=>q*treeEdgeWeight d^2*fullQuadRetainedDegree inner outer k))⁻¹ i j‖≤C := by
    rw [hcut.2]
    exact hrows
  have hmult (k:s.fullCoreMask S) : (Nat.card {j:BM⊕CM//fullQuadLeafMate inner outer BM CM j=some k}:ℝ)≤d+1 := by
    have hh := s.fullLeafMate_multiplicity selector S k
    have hdeg : s.graph.degree k.val=d := g.regular k.val
    rw [hdeg] at hh
    exact_mod_cast hh
  let J := s.fullCoreMask S ⊕ (BM ⊕ CM)
  let φ : s.FullEndpointIndex selector S ≃ J := Equiv.refl _
  let Qraw : Matrix J J ℂ := (fullQuadVacuumPrecision inner outer BM CM A⁻¹ q p (treeEdgeWeight d))⁻¹
  let Q0 : Matrix (s.FullEndpointIndex selector S) (s.FullEndpointIndex selector S) ℂ := Qraw
  have hRawRows := fullQuadVacuum_inverse_rows inner outer BM CM A⁻¹ q p (treeEdgeWeight d) hq0 hp0
    P C ((d:ℝ)+1) hP hC (by positivity) hqnorm hpnorm hαq hmult hcut.1 hcutRows
  have hQrows : ∀i,∑j,‖Q0 i j‖≤P+(d+2)*C := by
    intro i
    have hsum : (∑j,‖Q0 i j‖)=∑j:J,‖Qraw (φ i) j‖ := φ.sum_comp (fun j=>‖Qraw (φ i) j‖)
    rw [hsum]
    convert hRawRows (φ i) using 1; ring
  have he := g.full_partial_model_vacuum_stability hd T labels samples selector hs S q p z hz hq hq0 hp0 hrel
    P C δ hP hC hδ hqnorm hpnorm hαq hrows herr hsmall
  have hrow (i:s.FullEndpointIndex selector S) : (∑j,‖H (e i) (e j)‖)≤P+(d+2)*C+1 := by
    have hh := matrix_row_sum_of_entry_error (H.submatrix e e) Q0 (P+(d+2)*C)
      (2*(1+(P+(d+2)*C)*w)^2*δ) hQrows he i
    exact hh.trans (add_le_add_left hmass _)
  refine ⟨hrow,fun j=>?_⟩
  have hsym : H.IsSymm := DeficientGraph.extensionGreen_isSymm _ q z
  have hsum : (∑i,‖H (e i) (e j)‖)=∑i,‖H (e j) (e i)‖ :=
    Finset.sum_congr rfl (fun i _=>congrArg norm (hsym.apply _ _))
  rw [hsum]
  exact hrow j

end RegularGraph
end LocalLaw
