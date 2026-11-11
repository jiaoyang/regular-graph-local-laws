import LocalLaw.DeficitReduction
import LocalLaw.BoundarySchurRows

/-! # Exact retained inverse after restoring the retained deficit units

Both retained Green blocks are proved nonsingular. The actual complementary
matrix and both cross couplings are unchanged, so their Schur inverses
change by precisely the retained diagonal boundary charge.
-/

noncomputable section
set_option maxHeartbeats 2000000
namespace LocalLaw
local instance principalDeficitRestorationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem restoreOneDeficit_retained_inverse (g : DeficientGraph V d) (hd : 3≤d)
    (A : Set V) (hA : ∀ v∈A,0<g.deficit v) (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) :
    let old := (g.extensionGreen q z).submatrix (Subtype.val:A→V) (Subtype.val:A→V)
    let new := ((g.restoreOneDeficit A hA).extensionGreen q z).submatrix (Subtype.val:A→V) (Subtype.val:A→V)
    IsUnit old ∧ IsUnit new ∧
      new⁻¹=old⁻¹-q • Matrix.diagonal (fun _ : A => ((1/((d:ℝ)-1):ℝ):ℂ)) := by
  dsimp only
  let gnew := g.restoreOneDeficit A hA
  let M := g.extensionMatrix q z
  let N := gnew.extensionMatrix q z
  let a : A→V := Subtype.val
  let b : (Aᶜ:Set V)→V := Subtype.val
  have hM : IsUnit M := g.extensionMatrix_isUnit hd q z hz hq
  have hN : IsUnit N := gnew.extensionMatrix_isUnit hd q z hz hq
  have hD : IsUnit (M.submatrix b b) := by
    have hh := (g.delete A).extensionMatrix_isUnit hd q z hz hq
    rw [g.extensionMatrix_delete] at hh
    exact hh
  have hNN : N.submatrix b b=M.submatrix b b := by
    change ((g.restoreOneDeficit A hA).extensionMatrix q z).submatrix b b=_
    rw [g.restoreOneDeficit_extensionMatrix A hA q z]
    ext i j
    by_cases hij : i=j
    · subst j
      simp only [Matrix.submatrix_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply_eq,
        b,M,if_neg i.property,mul_zero,sub_zero]
    · have hv : i.val≠j.val := fun h => hij (Subtype.ext h)
      simp [Matrix.submatrix_apply,Matrix.diagonal_apply,hv,b,M]
  have hND : IsUnit (N.submatrix b b) := hNN.symm ▸ hD
  have hcross12 : N.submatrix a b=M.submatrix a b := by
    change (gnew.extensionMatrix q z).submatrix a b=(g.extensionMatrix q z).submatrix a b
    rw [gnew.extensionMatrix_cross12,g.extensionMatrix_cross12]
    rfl
  have hcross21 : N.submatrix b a=M.submatrix b a := by
    change (gnew.extensionMatrix q z).submatrix b a=(g.extensionMatrix q z).submatrix b a
    rw [gnew.extensionMatrix_cross21,g.extensionMatrix_cross21]
    rfl
  have hAA : N.submatrix a a=M.submatrix a a-
      q • Matrix.diagonal (fun _ : A => ((1/((d:ℝ)-1):ℝ):ℂ)) := by
    change ((g.restoreOneDeficit A hA).extensionMatrix q z).submatrix a a=_
    rw [g.restoreOneDeficit_extensionMatrix A hA q z]
    ext i j
    by_cases hij : i=j
    · subst j
      simp only [Matrix.submatrix_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
        Matrix.diagonal_apply_eq,a,M,if_pos i.property]
    · have hv : i.val≠j.val := fun h => hij (Subtype.ext h)
      simp [Matrix.submatrix_apply,Matrix.diagonal_apply,hv,hij,a,M]
  have hOld := retained_principal_inverse A M hM hD
  have hNew := retained_principal_inverse A N hN hND
  rw [hAA,hcross12,hcross21,hNN] at hNew
  have hOldUnit := retained_principal_inverse_isUnit A M hM hD
  have hNewUnit := retained_principal_inverse_isUnit A N hN hND
  refine ⟨hOldUnit,hNewUnit,?_⟩
  change (N⁻¹.submatrix a a)⁻¹=(M⁻¹.submatrix a a)⁻¹-_
  calc
    _ = (M.submatrix a a-q • Matrix.diagonal (fun _ : A => ((1/((d:ℝ)-1):ℝ):ℂ)))-
      M.submatrix a b*(M.submatrix b b)⁻¹*M.submatrix b a := hNew
    _ = (M.submatrix a a-M.submatrix a b*(M.submatrix b b)⁻¹*M.submatrix b a)-
      q • Matrix.diagonal (fun _ : A => ((1/((d:ℝ)-1):ℝ):ℂ)) := by abel
    _ = _ := congrArg (fun X : Matrix A A ℂ => X-q • Matrix.diagonal (fun _ : A => ((1/((d:ℝ)-1):ℝ):ℂ))) hOld.symm


theorem restoreOneDeficit_retained_Green (g : DeficientGraph V d) (hd : 3≤d)
    (A : Set V) (hA : ∀ v∈A,0<g.deficit v) (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) :
    ((g.restoreOneDeficit A hA).extensionGreen q z).submatrix (Subtype.val:A→V) (Subtype.val:A→V)=
      (((g.extensionGreen q z).submatrix (Subtype.val:A→V) (Subtype.val:A→V))⁻¹-
        q • Matrix.diagonal (fun _ : A => ((1/((d:ℝ)-1):ℝ):ℂ)))⁻¹ := by
  have hh := g.restoreOneDeficit_retained_inverse hd A hA q z hz hq
  have he := congrArg (fun M : Matrix A A ℂ => M⁻¹) hh.2.2
  dsimp only at he
  rw [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hh.2.1)] at he
  exact he

end DeficientGraph
end LocalLaw
