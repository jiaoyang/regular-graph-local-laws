import LocalLaw.PartialTripleBInverse
import LocalLaw.EmbeddedPartialDeficitRestoration
import LocalLaw.ActualPartialVacuumBenchmark

/-! # Actual switched sampled-first inverse rows

The missing-A restoration is performed on the old graph, whose class is
known. The actual switched B Green block is nonsingular independently of
class, and its inverse rows follow from the proved vacuum covariance error.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2500000
namespace LocalLaw
local instance actualPartialBInverseDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type}{T:Set V}{ι:Type}

def partialFirstEmbedding (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set (Tᶜ:Set V)) :
    s.partialFirstMask selector S↪S:=
  {toFun:=fun b=>(s.partialEndpointEmbedding selector S) (.inr (.inl b))
   inj':=by
     intro b c h
     exact Sum.inl.inj (Sum.inr.inj ((s.partialEndpointEmbedding selector S).injective h))}

end LabelledResamplingState
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

theorem partial_first_missing_restoration_rows (g:RegularGraph N d)(hd:3≤d)
    (T:Set (Fin N))(labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))
    (hb:((g.deficient.delete T).restrict S).ComponentFiniteReferenceBudget)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(R:ℕ)
    (hR:∀x y,((g.deficient.delete T).restrict S).graph.dist x y≤R)
    (small:‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2)
    (hcount:(Fintype.card ((g.admissibleState T labels samples).partialBoundaryMask selector S):ℝ)*
      physicalTransfer d z^selector≤1) :
    let s:=g.admissibleState T labels samples
    let G:=((g.deficient.delete T).restrict S).extensionGreen q z
    let A:=G.submatrix (s.partialBoundaryEmbedding selector S) (s.partialBoundaryEmbedding selector S)
    let K:=A⁻¹-partialMissingCharge (s.partialBoundaryMask selector S) (s.partialFirstMask selector S) q (treeEdgeWeight d)
    IsUnit K ∧ (∀i,∑j,‖K⁻¹ i j‖≤4*finiteExtraReferenceConstant d) ∧
      (∀j,∑i,‖K⁻¹ i j‖≤4*finiteExtraReferenceConstant d) := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let M:=(g.deficient.delete T).restrict S
  let AM:=s.partialBoundaryMask selector S
  let BM:=s.partialFirstMask selector S
  let e:=s.partialBoundaryEmbedding selector S
  let Missing:Set AM:={i | i.val∉BM}
  have hpos:∀v∈Set.range e,0<M.deficit v:=by
    intro v hv
    have hi:v∈s.includedEligibleBoundary selector S:=s.partialBoundaryEmbedding_range selector S ▸ hv
    rw [g.includedEligibleBoundary_deficit_one T labels samples selector S v hi]
    norm_num
  have hsep (i j:AM)(hij:i≠j):(selector:ℕ∞)≤M.graph.edist (e i) (e j):=
    (s.partialBoundaryEmbedding_separated selector S i j hij).le.trans
      (graphHom_edist_le (SimpleGraph.Embedding.induce (G:=outsideGraph g.graph T) S).toHom (e i) (e j))
  have hh:=M.partialDeficitRestoration_embedding_rows hd hb e Missing hpos selector hsep q z hz hq R hR small hcount
  have he:q•Matrix.diagonal (fun i:AM=>if i∈Missing then ((1/((d:ℝ)-1):ℝ):ℂ) else 0)=
      partialMissingCharge AM BM q (treeEdgeWeight d):=by
    ext i j
    by_cases hij:i=j
    · subst j
      simp only [partialMissingCharge,Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply_eq]
      have hcast:((1/((d:ℝ)-1):ℝ):ℂ)=1/((d:ℂ)-1):=by push_cast;rfl
      by_cases hi:i.val∈BM <;> simp [Missing,hi,treeEdgeWeight_sq d hd,hcast]
    · simp [partialMissingCharge,Matrix.diagonal_apply,hij]
  dsimp only at hh
  have hcast:((1/((d:ℝ)-1):ℝ):ℂ)=1/((d:ℂ)-1):=by push_cast;rfl
  simp only [←Matrix.diagonal_smul,Pi.smul_def,Pi.smul_apply,smul_eq_mul,Missing,Set.mem_setOf_eq,
    ite_not,mul_ite,mul_zero,hcast] at hh
  have hmfun:(fun i:AM=>if i∈Missing then q/((d:ℂ)-1) else 0)=
      (fun i:AM=>if i.val∈BM then 0 else q/((d:ℂ)-1)):=by
    funext i
    change (if i.val∉BM then _ else _)=(if i.val∈BM then _ else _)
    by_cases hi:i.val∈BM <;> simp [hi]
  simp only [mul_one_div] at hh
  rw [hmfun] at hh
  simpa only [partialMissingCharge,treeEdgeWeight_sq d hd,mul_one_div] using hh

theorem partial_model_first_inverse_caps (g:RegularGraph N d)(hd:3≤d)
    (T:Set (Fin N))(labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))(q p z:ℂ)(hz:0<z.im)(hq:0≤q.im)
    (hq0:q≠0)(hp0:p≠0)(hrel:p⁻¹=q⁻¹-q*treeEdgeWeight d^2)
    (P PInv K δ:ℝ)(hP:0≤P)(hPInv:0≤PInv)(hK:0≤K)(hδ:0≤δ)
    (hqnorm:‖q‖≤P)(hpnorm:‖p‖≤P)(ha:‖treeEdgeWeight d*q‖≤1)
    (hqinv:‖q⁻¹‖≤PInv)(hpinv:‖p⁻¹‖≤PInv) :
    let s:=g.admissibleState T labels samples
    let e:=s.partialEndpointEmbedding selector S
    let G:=((g.deficient.delete T).restrict S).extensionGreen q z
    let H:=(((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S).extensionGreen q z
    let A:=G.submatrix (s.partialBoundaryEmbedding selector S) (s.partialBoundaryEmbedding selector S)
    let AM:=s.partialBoundaryMask selector S
    let BM:=s.partialFirstMask selector S
    let J:=PInv+‖treeEdgeWeight d‖^2*K
    let σ:=2*(1+(P+2*K)*(2*‖treeEdgeWeight d‖+‖q‖*‖treeEdgeWeight d‖^2))^2*δ
    (∀i,∑j,‖(A⁻¹-Matrix.diagonal (fun _:AM=>q*treeEdgeWeight d^2))⁻¹ i j‖≤K)→
    IsUnit (A⁻¹-partialMissingCharge AM BM q (treeEdgeWeight d))→
    (∀i,∑j,‖(A⁻¹-partialMissingCharge AM BM q (treeEdgeWeight d))⁻¹ i j‖≤K)→
    (∀i j,‖(G.submatrix e e-s.partialOldCovariance selector S G q p (treeEdgeWeight d)) i j‖≤δ)→
    (Fintype.card (s.PartialEndpointIndex selector S):ℝ)*
      (1+(P+2*K)*(2*‖treeEdgeWeight d‖+‖q‖*‖treeEdgeWeight d‖^2))*
        (2*‖treeEdgeWeight d‖+‖q‖*‖treeEdgeWeight d‖^2)*δ≤1/2→
    (Fintype.card BM:ℝ)*J*σ≤1/2→
    let U:=H.submatrix (s.partialFirstEmbedding selector S) (s.partialFirstEmbedding selector S)
    IsUnit U ∧ (∀i,∑j,‖U⁻¹ i j‖≤2*J) ∧ (∀j,∑i,‖U⁻¹ i j‖≤2*J) := by
  dsimp only
  intro hrows hmissing hmissRows herr hsmall hBsmall
  let s:=g.admissibleState T labels samples
  let G:=((g.deficient.delete T).restrict S).extensionGreen q z
  let H:=(((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S).extensionGreen q z
  let A:=G.submatrix (s.partialBoundaryEmbedding selector S) (s.partialBoundaryEmbedding selector S)
  let AM:=s.partialBoundaryMask selector S
  let BM:=s.partialFirstMask selector S
  let CM:=s.partialSecondMask selector S
  let U:=H.submatrix (s.partialFirstEmbedding selector S) (s.partialFirstEmbedding selector S)
  have hU:IsUnit U:=(((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S).extensionGreen_submatrix_isUnit hd (s.partialFirstEmbedding selector S) q z hz hq
  have hu:=g.partial_boundary_precision_units hd T labels samples selector S q z hz hq
  have hAs:A⁻¹.IsSymm:=by
    have hA:A.IsSymm:=(DeficientGraph.extensionGreen_isSymm _ q z).submatrix _
    change A⁻¹.transpose=A⁻¹
    rw [Matrix.transpose_nonsing_inv,hA]
  have he:=g.partial_model_vacuum_stability hd T labels samples selector S q p z hz hq hq0 hp0 hrel
    P K δ hP hK hδ hqnorm hpnorm ha hrows herr hsmall
  have hstab:=partialTriple_BGreen_inverse_stability AM BM CM A⁻¹ q p (treeEdgeWeight d)
    hAs hq0 hp0 PInv K _ hPInv hK (by positivity) hqinv hpinv hu.2 hmissing hmissRows U hU
    (fun b b'=>he (.inr (.inl b)) (.inr (.inl b'))) hBsmall
  exact ⟨hU,hstab⟩

end RegularGraph
end LocalLaw
