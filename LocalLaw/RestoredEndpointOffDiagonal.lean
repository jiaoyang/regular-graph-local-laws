import LocalLaw.RestoredBoundaryQRows
import LocalLaw.PartialEndpointWeakCovariance

/-! # Actual restored endpoint inverse off-diagonals retain graph decay -/

noncomputable section
namespace LocalLaw
local instance restoredEndpointOffDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] {d:ℕ}

theorem restored_endpoint_offdiagonal (g:DeficientGraph V d)(hd:3≤d)
    (hb:g.ComponentFiniteReferenceBudget)(e:I↪V)(hA:∀v∈Set.range e,0<g.deficit v)
    (h:ℕ)(hsep:∀i j,i≠j→(h:ℕ∞)≤g.graph.edist (e i) (e j))
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(R:ℕ)(hR:∀x y,g.graph.dist x y≤R)
    (small:‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2) :
    let K:=((g.extensionGreen q z).submatrix e e)⁻¹-
      q•Matrix.diagonal (fun _:I=>((1/((d:ℝ)-1):ℝ):ℂ))
    ∀i j,i≠j→‖K⁻¹ i j‖≤2*finiteExtraReferenceConstant d*physicalTransfer d z^h := by
  dsimp only
  let M:=g.restoreOneDeficit (Set.range e) hA
  have hbM:=g.restoreOneDeficit_componentFiniteReferenceBudget (Set.range e) hA hb
  have he:=g.restoreOneDeficit_embedding_Green hd e hA q z hz hq
  rw [←he]
  intro i j hij
  exact M.perturbed_green_edist_bound hd hbM z q hz hq R hR small (e i) (e j) h (hsep i j hij)

end DeficientGraph
end LocalLaw
