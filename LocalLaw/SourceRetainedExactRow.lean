import LocalLaw.SourceRetainedExpansion

/-! # Exact normalized retained row equation on the original boundary labels -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceRetainedExactRowDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

private theorem source_sandwich_row (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (A B : Matrix T T ℂ) (D : Matrix ι ι ℂ) (x y : T) :
    ((A*g.sourceCutCoupling T labels)*D*((g.sourceCutCoupling T labels).transpose*B)) x y =
      (↑((Real.sqrt ((d:ℝ)-1))⁻¹):ℂ)^2*
        ∑ α,∑ β,A x (cutInsideVertex g.graph T (labels α))*D α β*B (cutInsideVertex g.graph T (labels β)) y := by
  have hleft (α : ι) : (A*g.sourceCutCoupling T labels) x α =
      (↑((Real.sqrt ((d:ℝ)-1))⁻¹):ℂ)*A x (cutInsideVertex g.graph T (labels α)) :=
    mul_cutInnerCoupling g.graph d T A x (labels α)
  have hright (β : ι) : ((g.sourceCutCoupling T labels).transpose*B) β y =
      (↑((Real.sqrt ((d:ℝ)-1))⁻¹):ℂ)*B (cutInsideVertex g.graph T (labels β)) y :=
    transpose_cutInnerCoupling_mul g.graph d T B (labels β) y
  calc
    _ = ∑ α,∑ β,(A*g.sourceCutCoupling T labels) x α*D α β*((g.sourceCutCoupling T labels).transpose*B) β y := by
      simp only [Matrix.mul_apply,Finset.sum_mul]
      exact Finset.sum_comm
    _ = _ := by
      simp only [hleft,hright,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro β _
      ring

theorem sourceRetained_exact_row (g : RegularGraph N d) (hd : 3≤d)
    (T : Set (Fin N)) (labels : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T) (selector r : ℕ)
    (hsep : 2*r+2≤selector) (hr : r+2≤selector) (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) (x y : T) :
    let R := ((g.labelledResampledGraph T labels samples selector).G z).submatrix
      (Subtype.val:T→Fin N) (Subtype.val:T→Fin N)
    let P := g.sourceRetainedReference T r q z
    let D := g.sourceBoundaryDefect T labels samples selector r q z
    let c : ℂ := (↑((Real.sqrt ((d:ℝ)-1))⁻¹):ℂ)^2
    R x y-P x y=c*(∑ α,∑ β,P x (cutInsideVertex g.graph T (labels α))*D α β*P (cutInsideVertex g.graph T (labels β)) y)+
      c*(∑ α,∑ β,(R x (cutInsideVertex g.graph T (labels α))-P x (cutInsideVertex g.graph T (labels α)))*
        D α β*P (cutInsideVertex g.graph T (labels β)) y) := by
  dsimp only
  let gnew := g.labelledResampledGraph T labels samples selector
  let R := (gnew.G z).submatrix (Subtype.val:T→Fin N) (Subtype.val:T→Fin N)
  let P := g.sourceRetainedReference T r q z
  let U := g.sourceCutCoupling T labels
  let D := g.sourceBoundaryDefect T labels samples selector r q z
  have hunitR := (green_retained_principal_inverse T gnew.H (normalizedAdjacency_isHermitian gnew.graph d) z hz).1
  have hunitP := g.filledRetainedGreen_isUnit hd T (centralBoundaryVertices g.graph T r) q z hz hq
  have hinv := g.sourceRetained_inverse_difference hd T labels samples selector r hsep hr q z hz hq
  have hmatrix := retained_difference_expansion R P (U*D*U.transpose) hunitR hunitP hinv
  have hentry := congrArg (fun K : Matrix T T ℂ => K x y) hmatrix
  have hmain : P*(U*D*U.transpose)*P=(P*U)*D*(U.transpose*P) := by simp only [Matrix.mul_assoc]
  have hrem : (R-P)*(U*D*U.transpose)*P=((R-P)*U)*D*(U.transpose*P) := by simp only [Matrix.mul_assoc]
  rw [hmain,hrem] at hentry
  simp only [Matrix.sub_apply,Matrix.add_apply,U] at hentry
  rw [source_sandwich_row,source_sandwich_row] at hentry
  simpa only [Matrix.sub_apply] using hentry

theorem sourceRetained_remainder_formula (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (R P : Matrix T T ℂ) (D : Matrix ι ι ℂ) (x y : T) :
    ((R-P)*g.sourceCutCoupling T labels*D*(g.sourceCutCoupling T labels).transpose*P) x y =
      (↑((Real.sqrt ((d:ℝ)-1))⁻¹):ℂ)^2*
        ∑ α,∑ β,(R x (cutInsideVertex g.graph T (labels α))-P x (cutInsideVertex g.graph T (labels α)))*
          D α β*P (cutInsideVertex g.graph T (labels β)) y := by
  have h := source_sandwich_row g T labels (R-P) P D x y
  simpa only [Matrix.mul_assoc,Matrix.sub_apply] using h

end RegularGraph
end LocalLaw
