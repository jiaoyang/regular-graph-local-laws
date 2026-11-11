import LocalLaw.PrincipalDeficitRestoration
import LocalLaw.SeparatedPhysicalRows

/-! # Deficit restoration on an injectively indexed retained block -/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
namespace LocalLaw
local instance embeddedDeficitRestorationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
section Reindex
variable {A J : Type} [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]

private theorem inverse_diagonal_shift_equiv (P Q : Matrix A A ℂ) (φ : J≃A) (q c : ℂ)
    (hh : Q⁻¹=P⁻¹-q • Matrix.diagonal (fun _ : A => c)) :
    (Q.submatrix φ φ)⁻¹=(P.submatrix φ φ)⁻¹-q • Matrix.diagonal (fun _ : J => c) := by
  have hD : (Matrix.diagonal (fun _ : A => c)).submatrix φ φ=Matrix.diagonal (fun _ : J => c) := by
    ext i j
    by_cases hij : i=j
    · subst j; simp
    · have hv : φ i≠φ j := fun h => hij (φ.injective h)
      simp [Matrix.submatrix_apply,Matrix.diagonal_apply,hij,hv]
  calc
    _ = Q⁻¹.submatrix φ φ := Matrix.inv_submatrix_equiv Q φ φ
    _ = (P⁻¹-q • Matrix.diagonal (fun _ : A => c)).submatrix φ φ := congrArg (fun X : Matrix A A ℂ => X.submatrix φ φ) hh
    _ = (P⁻¹).submatrix φ φ-q • Matrix.diagonal (fun _ : J => c) := by
      ext i j
      have hd := congrArg (fun X : Matrix J J ℂ => X i j) hD
      simp only [Matrix.submatrix_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul] at hd ⊢
      rw [hd]
    _ = _ := congrArg (fun X : Matrix J J ℂ => X-q • Matrix.diagonal (fun _ : J => c)) (Matrix.inv_submatrix_equiv P φ φ).symm

end Reindex
namespace DeficientGraph
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] {d : ℕ}

theorem restoreOneDeficit_embedding_inverse (g : DeficientGraph V d) (hd : 3≤d)
    (e : I↪V) (hA : ∀ v∈Set.range e,0<g.deficit v)
    (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) :
    let old := (g.extensionGreen q z).submatrix e e
    let new := ((g.restoreOneDeficit (Set.range e) hA).extensionGreen q z).submatrix e e
    IsUnit old ∧ IsUnit new ∧
      new⁻¹=old⁻¹-q • Matrix.diagonal (fun _ : I => ((1/((d:ℝ)-1):ℝ):ℂ)) := by
  dsimp only
  let A := Set.range e
  letI : DecidablePred (fun v : V => v∈A) := fun _ => Classical.propDecidable _
  letI : Fintype A := Subtype.fintype (fun v : V => v∈A)
  let φ : I≃A := Equiv.ofInjective (e:I→V) e.injective
  have hh := g.restoreOneDeficit_retained_inverse hd A hA q z hz hq
  have hOldM : ((g.extensionGreen q z).submatrix (Subtype.val:A→V) (Subtype.val:A→V)).submatrix φ φ=
      (g.extensionGreen q z).submatrix e e := by ext i j; rfl
  have hNewM : (((g.restoreOneDeficit A hA).extensionGreen q z).submatrix
      (Subtype.val:A→V) (Subtype.val:A→V)).submatrix φ φ=
      ((g.restoreOneDeficit A hA).extensionGreen q z).submatrix e e := by ext i j; rfl
  have hOld : IsUnit ((g.extensionGreen q z).submatrix e e) := by
    rw [←hOldM]
    exact (Matrix.isUnit_submatrix_equiv φ φ).mpr hh.1
  have hNew : IsUnit (((g.restoreOneDeficit A hA).extensionGreen q z).submatrix e e) := by
    rw [←hNewM]
    exact (Matrix.isUnit_submatrix_equiv φ φ).mpr hh.2.1
  have he := inverse_diagonal_shift_equiv
    ((g.extensionGreen q z).submatrix (Subtype.val:A→V) (Subtype.val:A→V))
    (((g.restoreOneDeficit A hA).extensionGreen q z).submatrix (Subtype.val:A→V) (Subtype.val:A→V))
    φ q ((1/((d:ℝ)-1):ℝ):ℂ) hh.2.2
  rw [hOldM,hNewM] at he
  exact ⟨hOld,hNew,he⟩


theorem restoreOneDeficit_embedding_Green (g : DeficientGraph V d) (hd : 3≤d)
    (e : I↪V) (hA : ∀ v∈Set.range e,0<g.deficit v)
    (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) :
    ((g.restoreOneDeficit (Set.range e) hA).extensionGreen q z).submatrix e e=
      (((g.extensionGreen q z).submatrix e e)⁻¹-
        q • Matrix.diagonal (fun _ : I => ((1/((d:ℝ)-1):ℝ):ℂ)))⁻¹ := by
  have hh := g.restoreOneDeficit_embedding_inverse hd e hA q z hz hq
  have he := congrArg (fun M : Matrix I I ℂ => M⁻¹) hh.2.2
  dsimp only at he
  rw [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hh.2.1)] at he
  exact he


theorem restored_physical_block_rows (g : DeficientGraph V d) (hd : 3≤d)
    (hbudget : g.ComponentFiniteReferenceBudget) (e : I↪V)
    (hA : ∀ v∈Set.range e,0<g.deficit v) (h : ℕ)
    (hsep : ∀ i j,i≠j→(h:ℕ∞)≤g.graph.edist (e i) (e j))
    (z : ℂ) (hz : 0<z.im) (hsmall : (Fintype.card I:ℝ)*physicalTransfer d z^h≤1) :
    let P := ((g.extensionGreen (semicircleRoot z) z).submatrix e e)⁻¹-
      (semicircleRoot z) • Matrix.diagonal (fun _ : I => ((1/((d:ℝ)-1):ℝ):ℂ))
    (∀ i,∑ j,‖P⁻¹ i j‖≤4*finiteExtraReferenceConstant d) ∧
      (∀ j,∑ i,‖P⁻¹ i j‖≤4*finiteExtraReferenceConstant d) := by
  dsimp only
  let gnew := g.restoreOneDeficit (Set.range e) hA
  have hb := g.restoreOneDeficit_componentFiniteReferenceBudget (Set.range e) hA hbudget
  have hrows := gnew.separated_physical_endpoint_rows hd hb e h hsep z hz hsmall
  have he := g.restoreOneDeficit_embedding_Green hd e hA (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le
  constructor
  · intro i
    have hh := hrows.1 i
    change (∑ j,‖((gnew.extensionGreen (semicircleRoot z) z).submatrix e e) i j‖)≤_ at hh
    rw [he] at hh
    exact hh
  · intro j
    have hh := hrows.2 j
    change (∑ i,‖((gnew.extensionGreen (semicircleRoot z) z).submatrix e e) i j‖)≤_ at hh
    rw [he] at hh
    exact hh

end DeficientGraph
end LocalLaw
