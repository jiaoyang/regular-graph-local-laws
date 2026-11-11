import LocalLaw.ModelStarHarmonic
import LocalLaw.DeficientMinorComparison

/-! # Actual normalized sampled-star coupling masses -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance starCouplingRowsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

private theorem star_sum_embedding_le {I W:Type} [Fintype I] [Fintype W]
    [DecidableEq W] (e:I↪W)(f:W→ℝ)(hf:∀w,0≤f w) :
    (∑i:I,f (e i))≤∑w:W,f w := by
  calc
    _=∑w∈Finset.univ.image e,f w:=(Finset.sum_image (fun i _ j _ h=>e.injective h)).symm
    _≤∑w:W,f w:=Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun w _ _=>hf w)

namespace DeficientGraph
variable {V I J:Type} [Fintype V] [Fintype I]
    [DecidableEq V] {d:ℕ}

theorem actual_star_coupling_rows (g:DeficientGraph V d)(hd:3≤d)
    (a:J↪V)(e:I↪((Set.range a)ᶜ:Set V))(q z:ℂ) :
    (∀j:J,(∑i:I,‖g.extensionMatrix q z (a j) (e i).val‖)≤(d:ℝ)) ∧
    (∀j:J,(∑i:I,‖g.extensionMatrix q z (e i).val (a j)‖)≤(d:ℝ)) := by
  have hrow (j:J):(∑i:I,‖g.extensionMatrix q z (a j) (e i).val‖)≤(d:ℝ):=by
    let f:I↪{v:V//v≠a j}:=
      {toFun:=fun i=>⟨(e i).val,fun h=>(e i).property ⟨j,h.symm⟩⟩
       inj':=fun _ _ h=>e.injective (Subtype.ext (congrArg (fun v:{v:V//v≠a j}=>v.val) h))}
    have hh:=star_sum_embedding_le f (fun v=>‖g.extensionMatrix q z (a j) v.val‖)
      (fun _=>norm_nonneg _)
    exact hh.trans (g.extensionMatrix_deleted_coupling_bounds hd q z (a j)).1
  refine ⟨hrow,?_⟩
  intro j
  convert hrow j using 1
  apply Finset.sum_congr rfl
  intro i _
  rw[(g.extensionMatrix_isSymm q z).apply]

omit [Fintype I] in
theorem actual_star_coupling_entry (g:DeficientGraph V d)(hd:3≤d)
    (a:J↪V)(e:I↪((Set.range a)ᶜ:Set V))(q z:ℂ)(i:I)(j:J) :
    ‖g.extensionMatrix q z (a j) (e i).val‖≤(d:ℝ) := by
  let v:{v:V//v≠a j}:=⟨(e i).val,fun h=>(e i).property ⟨j,h.symm⟩⟩
  have hh:‖g.extensionMatrix q z (a j) v.val‖≤∑w:{v:V//v≠a j},‖g.extensionMatrix q z (a j) w.val‖:=
    Finset.single_le_sum (f:=fun w:{v:V//v≠a j}=>‖g.extensionMatrix q z (a j) w.val‖)
      (fun _ _=>norm_nonneg _) (Finset.mem_univ v)
  exact hh.trans (g.extensionMatrix_deleted_coupling_bounds hd q z (a j)).1


omit [Fintype I] in
theorem actual_star_coupling_nonzero_adj (g:DeficientGraph V d)
    (a:J↪V)(e:I↪((Set.range a)ᶜ:Set V))(q z:ℂ)(i:I)(j:J)
    (hn:g.extensionMatrix q z (a j) (e i).val≠0) :
    g.graph.Adj (a j) (e i).val := by
  by_contra hadj
  have hne:a j≠(e i).val:=fun he=>(e i).property ⟨j,he⟩
  apply hn
  simp [extensionMatrix,boundaryMatrix,spectralMatrix,boundaryDiagonal,
    Matrix.diagonal_apply,Matrix.one_apply,H,normalizedAdjacency,
    SimpleGraph.adjMatrix_apply,hne,hadj]

end DeficientGraph
end LocalLaw
