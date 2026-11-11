import LocalLaw.DeficitReduction
import LocalLaw.RestoredBoundaryQRows
import LocalLaw.SupportedRetainedInverse

/-! Select any subset of one-unit endpoint deficits below an actual upper model. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance endpointDeficitSelectorDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V I:Type}[Fintype V][Fintype I]{d:ℕ}

def endpointDeficitSelector (upper lower:DeficientGraph V d)(e:I↪V)(B:Set I):DeficientGraph V d:=
  upper.lowerDeficit (fun v=>if v∈Set.range e then if v∈(e:I→V) '' B then 0 else upper.deficit v
    else upper.deficit v-lower.deficit v) (by
      intro v
      dsimp only
      split_ifs <;> first | exact Nat.zero_le _ | exact le_rfl | exact Nat.sub_le _ _)

theorem endpointDeficitSelector_at_endpoint (upper lower:DeficientGraph V d)(e:I↪V)(B:Set I)
    (hone:∀i,upper.deficit (e i)=1)(i:I):
    (upper.endpointDeficitSelector lower e B).deficit (e i)=if i∈B then 1 else 0:=by
  have he:e i∈(e:I→V) '' B↔i∈B:=by
    constructor
    · rintro ⟨j,hj,hji⟩
      exact e.injective hji ▸ hj
    · intro hi
      exact ⟨i,hi,rfl⟩
  change upper.deficit (e i)-(if e i∈Set.range e then if e i∈(e:I→V) '' B then 0 else upper.deficit (e i)
    else upper.deficit (e i)-lower.deficit (e i))=_
  simp only [Set.mem_range_self,if_true,he,hone]
  split_ifs <;> norm_num

theorem endpointDeficitSelector_off_endpoints (upper lower:DeficientGraph V d)(e:I↪V)(B:Set I)
    (hle:∀v,lower.deficit v≤upper.deficit v)(v:V)(hv:v∉Set.range e):
    (upper.endpointDeficitSelector lower e B).deficit v=lower.deficit v:=by
  change upper.deficit v-(if v∈Set.range e then _ else _)=_
  rw [if_neg hv]
  exact Nat.sub_sub_self (hle v)

theorem endpointDeficitSelector_budget (upper lower:DeficientGraph V d)(e:I↪V)(B:Set I)
    (hb:upper.ComponentFiniteReferenceBudget):
    (upper.endpointDeficitSelector lower e B).ComponentFiniteReferenceBudget:=
  upper.lowerDeficit_componentFiniteReferenceBudget _ _ hb

theorem extensionMatrix_difference_of_same_graph [DecidableEq V]
    (g h:DeficientGraph V d)(hgraph:h.graph=g.graph)(q z:ℂ):
    h.extensionMatrix q z-g.extensionMatrix q z=
      q•Matrix.diagonal (fun v=>(((h.deficit v:ℝ)-(g.deficit v:ℝ))/((d:ℝ)-1):ℂ)):=by
  have hH:h.H=g.H:=congrArg (fun G=>normalizedAdjacency G d) hgraph
  have hdegree:∀v,h.graph.degree v=g.graph.degree v:=by intro v;rw [hgraph]
  ext i j
  simp only [extensionMatrix,boundaryMatrix,spectralMatrix,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,hH]
  by_cases hij:i=j
  · subst j
    simp only [boundaryDiagonal,Matrix.diagonal_apply_eq,boundaryCoefficient,hdegree,
      Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_natCast,Complex.ofReal_one]
    ring
  · simp only [boundaryDiagonal,Matrix.diagonal_apply,hij,if_false,mul_zero]
    ring

theorem endpointDeficitSelector_retained_matrix [DecidableEq V]
    (upper lower:DeficientGraph V d)(hgraph:lower.graph=upper.graph)(e:I↪V)(B L:Set I)
    (hone:∀i,upper.deficit (e i)=1)(hlower:∀i,lower.deficit (e i)=if i∈L then 1 else 0)
    (q z:ℂ):
    (((upper.endpointDeficitSelector lower e B).extensionMatrix q z-lower.extensionMatrix q z).submatrix e e)=
      q•Matrix.diagonal (fun i:I=>
        (((if i∈B then (1:ℝ) else 0)-(if i∈L then 1 else 0))/((d:ℝ)-1):ℂ)):=by
  rw [lower.extensionMatrix_difference_of_same_graph (upper.endpointDeficitSelector lower e B) hgraph.symm q z]
  ext i j
  by_cases hij:i=j
  · subst j
    simp only [Matrix.submatrix_apply,Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply_eq,
      upper.endpointDeficitSelector_at_endpoint lower e B hone,hlower]
    split_ifs <;> simp
  · simp only [Matrix.submatrix_apply,Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply,
      e.injective.eq_iff,hij,if_false,mul_zero]


theorem endpointDeficitSelector_supported [DecidableEq V]
    (upper lower:DeficientGraph V d)(hgraph:lower.graph=upper.graph)(e:I↪V)(B:Set I)
    (hle:∀v,lower.deficit v≤upper.deficit v)(q z:ℂ):
    ∀x y,x∉Set.range e∨y∉Set.range e→
      ((upper.endpointDeficitSelector lower e B).extensionMatrix q z-lower.extensionMatrix q z) x y=0:=by
  rw [lower.extensionMatrix_difference_of_same_graph (upper.endpointDeficitSelector lower e B) hgraph.symm q z]
  intro x y hxy
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply]
  by_cases h:x=y
  · subst y
    have hx:x∉Set.range e:=hxy.elim id id
    rw [if_pos rfl,upper.endpointDeficitSelector_off_endpoints lower e B hle x hx]
    simp
  · simp [h]

theorem endpointDeficitSelector_inverse_rows [DecidableEq V]
    (upper lower:DeficientGraph V d)(hd:3≤d)(hgraph:lower.graph=upper.graph)(e:I↪V)(B L:Set I)
    (hle:∀v,lower.deficit v≤upper.deficit v)(hone:∀i,upper.deficit (e i)=1)
    (hlower:∀i,lower.deficit (e i)=if i∈L then 1 else 0)
    (hb:upper.ComponentFiniteReferenceBudget)(h R:ℕ)
    (hsep:∀i j,i≠j→(h:ℕ∞)≤upper.graph.edist (e i) (e j))
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(hR:∀x y,upper.graph.dist x y≤R)
    (small:‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2)
    (hcount:(Fintype.card I:ℝ)*physicalTransfer d z^h≤1):
    let P:=(lower.extensionGreen q z).submatrix e e
    let K:=P⁻¹+q•Matrix.diagonal (fun i:I=>
      (((if i∈B then (1:ℝ) else 0)-(if i∈L then 1 else 0))/((d:ℝ)-1):ℂ))
    IsUnit K∧(∀i,∑j,‖K⁻¹ i j‖≤4*finiteExtraReferenceConstant d)∧
      (∀j,∑i,‖K⁻¹ i j‖≤4*finiteExtraReferenceConstant d):=by
  dsimp only
  let M:=upper.endpointDeficitSelector lower e B
  let P:=(lower.extensionGreen q z).submatrix e e
  let Q:=(M.extensionGreen q z).submatrix e e
  have hu:=lower.supported_retained_inverse M hd e q z hz hq
    (upper.endpointDeficitSelector_supported lower hgraph e B hle q z)
  have hprec:=hu.2.2
  rw [upper.endpointDeficitSelector_retained_matrix lower hgraph e B L hone hlower q z] at hprec
  have hK:P⁻¹+q•Matrix.diagonal (fun i:I=>
      (((if i∈B then (1:ℝ) else 0)-(if i∈L then 1 else 0))/((d:ℝ)-1):ℂ))=Q⁻¹:=hprec.symm
  rw [hK]
  have hQ:Q⁻¹⁻¹=Q:=Matrix.nonsing_inv_nonsing_inv Q ((Matrix.isUnit_iff_isUnit_det Q).mp hu.2.1)
  refine ⟨Matrix.isUnit_nonsing_inv_iff.mpr hu.2.1,?_,?_⟩
  · rw [hQ]
    exact (M.separated_perturbed_endpoint_rows hd (upper.endpointDeficitSelector_budget lower e B hb)
      e h hsep z q hz hq R hR small hcount).1
  · rw [hQ]
    exact (M.separated_perturbed_endpoint_rows hd (upper.endpointDeficitSelector_budget lower e B hb)
      e h hsep z q hz hq R hR small hcount).2

end DeficientGraph
end LocalLaw
