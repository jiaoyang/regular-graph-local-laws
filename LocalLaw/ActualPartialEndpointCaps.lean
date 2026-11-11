import LocalLaw.ActualPartialVacuumBenchmark

/-! # Uniform actual switched partial-endpoint rows from contraction

The covariance defect is used to obtain a constant row bound. Its
unweighted dimension factor is confined to the smallness condition.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
namespace LocalLaw
local instance actualPartialEndpointCapsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem matrix_row_sum_of_entry_error {I:Type} [Fintype I]
    (T Q:Matrix I I ℂ) (C δ:ℝ) (hQ:∀i,∑j,‖Q i j‖≤C)
    (hE:∀i j,‖T i j-Q i j‖≤δ) (i:I) :
    (∑j,‖T i j‖)≤C+(Fintype.card I:ℝ)*δ := by
  have hp (j:I):‖T i j‖≤‖Q i j‖+δ:=by
    have hh:=norm_add_le (Q i j) (T i j-Q i j)
    rw [add_sub_cancel] at hh
    exact hh.trans (add_le_add_left (hE i j) _)
  exact (Finset.sum_le_sum (fun j _=>hp j)).trans
    (by simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      using add_le_add_right (hQ i) ((Fintype.card I:ℝ)*δ))

namespace RegularGraph
variable {N d:ℕ} {ι:Type} [Fintype ι]

theorem partial_model_vacuum_row_caps (g:RegularGraph N d) (hd:3≤d)
    (T:Set (Fin N)) (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector:ℕ) (S:Set (Tᶜ:Set (Fin N))) (q p z:ℂ) (hz:0<z.im) (hq:0≤q.im)
    (hq0:q≠0) (hp0:p≠0) (hrel:p⁻¹=q⁻¹-q*treeEdgeWeight d^2)
    (P K δ:ℝ) (hP:0≤P) (hK:0≤K) (hδ:0≤δ)
    (hqnorm:‖q‖≤P) (hpnorm:‖p‖≤P) (ha:‖treeEdgeWeight d*q‖≤1) :
    let s:=g.admissibleState T labels samples
    let e:=s.partialEndpointEmbedding selector S
    let G:=((g.deficient.delete T).restrict S).extensionGreen q z
    let H:=(((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S).extensionGreen q z
    let A:=G.submatrix (s.partialBoundaryEmbedding selector S) (s.partialBoundaryEmbedding selector S)
    (∀ i,∑ j,‖(A⁻¹-Matrix.diagonal (fun _:s.partialBoundaryMask selector S=>q*treeEdgeWeight d^2))⁻¹ i j‖≤K)→
    (∀ i j,‖(G.submatrix e e-s.partialOldCovariance selector S G q p (treeEdgeWeight d)) i j‖≤δ)→
    ((Fintype.card (s.PartialEndpointIndex selector S):ℝ)*
      (1+(P+2*K)*(2*‖treeEdgeWeight d‖+‖q‖*‖treeEdgeWeight d‖^2))*
        (2*‖treeEdgeWeight d‖+‖q‖*‖treeEdgeWeight d‖^2)*δ≤1/2)→
    ((Fintype.card (s.PartialEndpointIndex selector S):ℝ)*
      (2*(1+(P+2*K)*(2*‖treeEdgeWeight d‖+‖q‖*‖treeEdgeWeight d‖^2))^2*δ)≤1)→
    (∀ i,∑ j,‖H (e i) (e j)‖≤P+2*K+1)∧
      (∀ j,∑ i,‖H (e i) (e j)‖≤P+2*K+1) := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let e:=s.partialEndpointEmbedding selector S
  let G:=((g.deficient.delete T).restrict S).extensionGreen q z
  let H:=(((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S).extensionGreen q z
  let A:=G.submatrix (s.partialBoundaryEmbedding selector S) (s.partialBoundaryEmbedding selector S)
  intro hrows herr hsmall hmass
  have hu:=g.partial_boundary_precision_units hd T labels samples selector S q z hz hq
  let J:=s.partialBoundaryMask selector S⊕(s.partialFirstMask selector S⊕s.partialSecondMask selector S)
  let φ:s.PartialEndpointIndex selector S≃J:=Equiv.refl _
  let Qraw:Matrix J J ℂ:=
    (partialTripleNewPrecision (s.partialBoundaryMask selector S) (s.partialFirstMask selector S)
      (s.partialSecondMask selector S) A⁻¹ q p (treeEdgeWeight d))⁻¹
  let Q0:Matrix (s.PartialEndpointIndex selector S) (s.PartialEndpointIndex selector S) ℂ:=Qraw
  have hRawRows:= (partialTripleNewPrecision_inverse_rows_cap (s.partialBoundaryMask selector S)
      (s.partialFirstMask selector S) (s.partialSecondMask selector S) A⁻¹ q p (treeEdgeWeight d)
      hq0 hp0 P hP hqnorm hpnorm ha K hK hu.2 hrows).2
  have hQrows : ∀i,∑j,‖Q0 i j‖≤P+2*K := by
    intro i
    have hsum:(∑j,‖Q0 i j‖)=∑j:J,‖Qraw (φ i) j‖:=
      φ.sum_comp (fun j=>‖Qraw (φ i) j‖)
    rw [hsum]
    exact hRawRows (φ i)
  have he:=g.partial_model_vacuum_stability hd T labels samples selector S q p z hz hq hq0 hp0 hrel
    P K δ hP hK hδ hqnorm hpnorm ha hrows herr hsmall
  have hrow (i:s.PartialEndpointIndex selector S) : (∑j,‖H (e i) (e j)‖)≤P+2*K+1:=by
    have hh:=matrix_row_sum_of_entry_error (H.submatrix e e)
      Q0
      (P+2*K) (2*(1+(P+2*K)*(2*‖treeEdgeWeight d‖+‖q‖*‖treeEdgeWeight d‖^2))^2*δ)
      hQrows he i
    exact hh.trans (add_le_add_left hmass _)
  refine ⟨hrow,fun j=>?_⟩
  have hs:H.IsSymm:=DeficientGraph.extensionGreen_isSymm _ q z
  have heq:(∑ i,‖H (e i) (e j)‖)=∑i,‖H (e j) (e i)‖:=
    Finset.sum_congr rfl (fun i _=>congrArg norm (hs.apply _ _))
  rw [heq]
  exact hrow j

end RegularGraph
end LocalLaw
