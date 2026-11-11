import LocalLaw.EmbeddedDeficitRestoration
import LocalLaw.EmbeddedFiniteRankResolvent

/-! # Exact retained precision under an arbitrary supported model update -/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance supportedRetainedInverseDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] {d : ℕ}

theorem extensionGreen_submatrix_isUnit (g : DeficientGraph V d) (hd : 3≤d)
    (e : I↪V) (q z : ℂ) (hz : 0<z.im) (hq : 0 ≤ q.im) :
    IsUnit ((g.extensionGreen q z).submatrix e e) := by
  let A:=Set.range e
  letI : DecidablePred (fun v : V=>v∈A) := fun _=>Classical.propDecidable _
  letI : Fintype A:=Subtype.fintype (fun v : V=>v∈A)
  let φ : I≃A:=Equiv.ofInjective (e:I→V) e.injective
  let b : (Aᶜ:Set V)→V:=Subtype.val
  have hD : IsUnit ((g.extensionMatrix q z).submatrix b b) := by
    have hh:=(g.delete A).extensionMatrix_isUnit hd q z hz hq
    rw [g.extensionMatrix_delete] at hh
    exact hh
  have hR:=retained_principal_inverse_isUnit A (g.extensionMatrix q z)
    (g.extensionMatrix_isUnit hd q z hz hq) hD
  have he : ((g.extensionGreen q z).submatrix (Subtype.val:A→V) (Subtype.val:A→V)).submatrix φ φ=
      (g.extensionGreen q z).submatrix e e := by ext i j; rfl
  rw [←he]
  exact (Matrix.isUnit_submatrix_equiv φ φ).mpr hR

theorem supported_retained_inverse (g h : DeficientGraph V d) (hd : 3≤d)
    (e : I↪V) (q z : ℂ) (hz : 0<z.im) (hq : 0 ≤ q.im)
    (hsupport : ∀ i j,i∉Set.range e ∨ j∉Set.range e→
      (h.extensionMatrix q z-g.extensionMatrix q z) i j=0) :
    let P:=(g.extensionGreen q z).submatrix e e
    let Q:=(h.extensionGreen q z).submatrix e e
    let W:=(h.extensionMatrix q z-g.extensionMatrix q z).submatrix e e
    IsUnit P ∧ IsUnit Q ∧ Q⁻¹=P⁻¹+W := by
  dsimp only
  let P:=(g.extensionGreen q z).submatrix e e
  let Q:=(h.extensionGreen q z).submatrix e e
  let W:=(h.extensionMatrix q z-g.extensionMatrix q z).submatrix e e
  have hP:=g.extensionGreen_submatrix_isUnit hd e q z hz hq
  have hQ:=h.extensionGreen_submatrix_isUnit hd e q z hz hq
  have hu:=inverse_embedded_finite_rank_updates (g.extensionMatrix q z) (h.extensionMatrix q z)
    (g.extensionMatrix_isUnit hd q z hz hq) (h.extensionMatrix_isUnit hd q z hz hq) e hsupport
  have hupdate : Q+P*W*Q=P := hu.1
  have hPinv:P⁻¹*P=1:=Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP)
  have hQinv:Q*Q⁻¹=1:=Matrix.mul_nonsing_inv Q ((Matrix.isUnit_iff_isUnit_det Q).mp hQ)
  refine ⟨hP,hQ,?_⟩
  change Q⁻¹=P⁻¹+W
  calc
    _=(P⁻¹*P)*Q⁻¹ := by rw [hPinv,Matrix.one_mul]
    _=P⁻¹*(Q+P*W*Q)*Q⁻¹ := by rw [hupdate,Matrix.mul_assoc]
    _=P⁻¹+W := by
      rw [Matrix.mul_add,Matrix.add_mul]
      have hfirst:P⁻¹*Q*Q⁻¹=P⁻¹ := by rw [Matrix.mul_assoc,hQinv,Matrix.mul_one]
      have hsecond:P⁻¹*(P*W*Q)*Q⁻¹=W := by
        calc
          _=(P⁻¹*P)*W*(Q*Q⁻¹) := by simp only [Matrix.mul_assoc]
          _=W := by rw [hPinv,hQinv,Matrix.one_mul,Matrix.mul_one]
      rw [hfirst,hsecond]

theorem supported_retained_Green (g h : DeficientGraph V d) (hd : 3≤d)
    (e : I↪V) (q z : ℂ) (hz : 0<z.im) (hq : 0 ≤ q.im)
    (hsupport : ∀ i j,i∉Set.range e ∨ j∉Set.range e→
      (h.extensionMatrix q z-g.extensionMatrix q z) i j=0) :
    (h.extensionGreen q z).submatrix e e=
      (((g.extensionGreen q z).submatrix e e)⁻¹+
        (h.extensionMatrix q z-g.extensionMatrix q z).submatrix e e)⁻¹ := by
  have hh:=g.supported_retained_inverse h hd e q z hz hq hsupport
  have he:=congrArg (fun M : Matrix I I ℂ=>M⁻¹) hh.2.2
  dsimp only at he
  rw [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hh.2.1)] at he
  exact he

end DeficientGraph
end LocalLaw
