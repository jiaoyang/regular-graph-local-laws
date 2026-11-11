import LocalLaw.ActualPartialBInverseCaps
import LocalLaw.PartialVacuumBBEntries
import LocalLaw.RestoredEndpointOffDiagonal

/-! # Actual sampled-first off-diagonal correlations from the old class

The benchmark B block inherits the separated restored-A kernel. The true
switching covariance error is added once, without summing over sampled B.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance actualPartialBOffDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

theorem partial_model_first_offdiagonal (g:RegularGraph N d)(hd:3≤d)
    (T:Set (Fin N))(labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))
    (hb:((g.deficient.delete T).restrict S).ComponentFiniteReferenceBudget)
    (q p z:ℂ)(hz:0<z.im)(hq:0≤q.im)(hq0:q≠0)(hp0:p≠0)
    (hrel:p⁻¹=q⁻¹-q*treeEdgeWeight d^2)(R:ℕ)
    (hR:∀x y,((g.deficient.delete T).restrict S).graph.dist x y≤R)
    (small:‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2)
    (P K δ:ℝ)(hP:0≤P)(hK:0≤K)(hδ:0≤δ)
    (hqnorm:‖q‖≤P)(hpnorm:‖p‖≤P)(ha:‖treeEdgeWeight d*q‖≤1) :
    let s:=g.admissibleState T labels samples
    let e:=s.partialEndpointEmbedding selector S
    let G:=((g.deficient.delete T).restrict S).extensionGreen q z
    let H:=(((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S).extensionGreen q z
    let A:=G.submatrix (s.partialBoundaryEmbedding selector S) (s.partialBoundaryEmbedding selector S)
    (∀i,∑j,‖(A⁻¹-Matrix.diagonal (fun _:s.partialBoundaryMask selector S=>q*treeEdgeWeight d^2))⁻¹ i j‖≤K)→
    (∀i j,‖(G.submatrix e e-s.partialOldCovariance selector S G q p (treeEdgeWeight d)) i j‖≤δ)→
    (Fintype.card (s.PartialEndpointIndex selector S):ℝ)*
      (1+(P+2*K)*(2*‖treeEdgeWeight d‖+‖q‖*‖treeEdgeWeight d‖^2))*
        (2*‖treeEdgeWeight d‖+‖q‖*‖treeEdgeWeight d‖^2)*δ≤1/2→
    ∀b b':s.partialFirstMask selector S,b≠b'→
    ‖H (s.partialFirstEmbedding selector S b) (s.partialFirstEmbedding selector S b')‖≤
      ‖treeEdgeWeight d*q‖^2*(2*finiteExtraReferenceConstant d*physicalTransfer d z^selector)+
        2*(1+(P+2*K)*(2*‖treeEdgeWeight d‖+‖q‖*‖treeEdgeWeight d‖^2))^2*δ := by
  dsimp only
  intro hrows herr hsmall b b' hbb
  let s:=g.admissibleState T labels samples
  let M:=(g.deficient.delete T).restrict S
  let G:=M.extensionGreen q z
  let H:=(((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S).extensionGreen q z
  let e:=s.partialBoundaryEmbedding selector S
  let A:=G.submatrix e e
  let AM:=s.partialBoundaryMask selector S
  let BM:=s.partialFirstMask selector S
  let CM:=s.partialSecondMask selector S
  let α:=treeEdgeWeight d
  let τ:=2*finiteExtraReferenceConstant d*physicalTransfer d z^selector
  have hpos:∀v∈Set.range e,0<M.deficit v:=by
    intro v hv
    have hi:v∈s.includedEligibleBoundary selector S:=s.partialBoundaryEmbedding_range selector S ▸ hv
    rw [g.includedEligibleBoundary_deficit_one T labels samples selector S v hi]
    norm_num
  have hsep (i j:AM)(hij:i≠j):(selector:ℕ∞)≤M.graph.edist (e i) (e j):=
    (s.partialBoundaryEmbedding_separated selector S i j hij).le.trans
      (graphHom_edist_le (SimpleGraph.Embedding.induce (G:=outsideGraph g.graph T) S).toHom (e i) (e j))
  have hAoff:=M.restored_endpoint_offdiagonal hd hb e hpos selector hsep q z hz hq R hR small
  have hD:q•Matrix.diagonal (fun _:AM=>((1/((d:ℝ)-1):ℝ):ℂ))=
      Matrix.diagonal (fun _:AM=>q*α^2):=by
    ext i j
    have hcast:((1/((d:ℝ)-1):ℝ):ℂ)=1/((d:ℂ)-1):=by push_cast;rfl
    by_cases hij:i=j
    · subst j
      simp only [Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply_eq,α,treeEdgeWeight_sq d hd,hcast]
    · simp [Matrix.diagonal_apply,hij]
  dsimp only at hAoff
  rw [hD] at hAoff
  have hUnits:=g.partial_boundary_precision_units hd T labels samples selector S q z hz hq
  have hτ:0≤τ:=by
    dsimp only [τ]
    have hc:=finiteExtraReferenceConstant_ge_one d hd
    have ht:=pow_nonneg (physicalTransfer_pos d hd z).le selector
    positivity
  have hbench:‖(partialTripleNewPrecision AM BM CM A⁻¹ q p α)⁻¹
      (.inr (.inl b)) (.inr (.inl b'))‖≤‖α*q‖^2*τ:=by
    change ‖(((partialTripleNewPrecision AM BM CM A⁻¹ q p α)⁻¹).submatrix
      (fun b:BM=>Sum.inr (Sum.inl b)) (fun b:BM=>Sum.inr (Sum.inl b))) b b'‖≤_
    rw [partialTriple_BGreen_eq AM BM CM A⁻¹ q p α hq0 hp0 hUnits.2]
    exact partialVacuum_BGreen_offdiagonal AM BM A⁻¹ q p α hq0 hp0 hUnits.2 τ hτ hAoff b b' hbb
  have he:=g.partial_model_vacuum_stability hd T labels samples selector S q p z hz hq hq0 hp0 hrel
    P K δ hP hK hδ hqnorm hpnorm ha hrows herr hsmall
  have hactual:=he (.inr (.inl b)) (.inr (.inl b'))
  have hn:=norm_sub_le_norm_sub_add_norm_sub
    (H (s.partialFirstEmbedding selector S b) (s.partialFirstEmbedding selector S b'))
    ((partialTripleNewPrecision AM BM CM A⁻¹ q p α)⁻¹ (.inr (.inl b)) (.inr (.inl b'))) 0
  simp only [sub_zero] at hn
  exact hn.trans ((add_le_add hactual hbench).trans_eq (by ring))

end RegularGraph
end LocalLaw
