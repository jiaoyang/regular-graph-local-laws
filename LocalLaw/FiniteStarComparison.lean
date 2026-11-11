import LocalLaw.FiniteStarReduction
import LocalLaw.CoreSchurLift

/-! # Exact Schur lifting across two different ambient core spaces -/

noncomputable section
namespace LocalLaw
local instance finiteStarComparisonDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem finite_star_inverse_difference {V W I J : Type}
    [Fintype V] [Fintype W] [Fintype I] [Fintype J]
    [DecidableEq V] [DecidableEq W] [DecidableEq I] [DecidableEq J]
    (A : Matrix V V ℂ) (B : Matrix W W ℂ)
    (U : Matrix V J ℂ) (Vt : Matrix J V ℂ) (U' : Matrix W J ℂ) (Vt' : Matrix J W ℂ)
    (D : Matrix J J ℂ) (e : I↪V) (f : I↪W)
    (hA : IsUnit A) (hB : IsUnit B)
    (hM : IsUnit (Matrix.fromBlocks A U Vt D)) (hN : IsUnit (Matrix.fromBlocks B U' Vt' D))
    (hR : IsUnit (A⁻¹.submatrix e e)) (hP : IsUnit (B⁻¹.submatrix f f))
    (hU : ∀v j,v∉Set.range e→U v j=0) (hV : ∀j v,v∉Set.range e→Vt j v=0)
    (hU' : ∀w j,w∉Set.range f→U' w j=0) (hV' : ∀j w,w∉Set.range f→Vt' j w=0)
    (hleft : U.submatrix e id=U'.submatrix f id)
    (hright : Vt.submatrix id e=Vt'.submatrix id f) :
    let R:=A⁻¹.submatrix e e
    let P:=B⁻¹.submatrix f f
    let GM:=(Matrix.fromBlocks A U Vt D)⁻¹.submatrix (Sum.map e id) (Sum.map e id)
    let GN:=(Matrix.fromBlocks B U' Vt' D)⁻¹.submatrix (Sum.map f id) (Sum.map f id)
    GM-GN=(GM.submatrix id Sum.inl*R⁻¹)*(R-P)*(P⁻¹*GN.submatrix Sum.inl id) := by
  dsimp only
  let R:=A⁻¹.submatrix e e
  let P:=B⁻¹.submatrix f f
  let M:=finiteStarMatrix A U Vt D e
  let N:=finiteStarMatrix B U' Vt' D f
  have hm:=finite_star_reduction A U Vt D e hA hM hR hU hV
  have hn:=finite_star_reduction B U' Vt' D f hB hN hP hU' hV'
  have h11 : M.toBlocks₁₁=R⁻¹ := rfl
  have h11' : N.toBlocks₁₁=P⁻¹ := rfl
  have h12 : M.toBlocks₁₂=N.toBlocks₁₂ := hleft
  have h21 : M.toBlocks₂₁=N.toBlocks₂₁ := hright
  have h22 : M.toBlocks₂₂=N.toBlocks₂₂ := rfl
  have hh:=core_schur_inverse_difference M N hm.1 hn.1 R P hR hP h11 h11' h12 h21 h22
  rw [hm.2,hn.2] at hh
  exact hh

end LocalLaw
