import LocalLaw.AugmentedRowTransfer
import LocalLaw.DeletionStability
import LocalLaw.EmbeddedFiniteRankResolvent

/-! # Small supported normalization with true target weights

Only the old retained Green block must be known nonsingular. The update
equation proves nonsingularity of the new retained block. The entrywise
contraction pays the retained count, while the final target comparison
pays the actual perturbation row mass and target L1 weights.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance supportedSmallUpdateDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem supported_retained_inverse_of_old_unit (A B:Matrix V V ℂ)
    (hA:IsUnit A)(hB:IsUnit B)(e:I↪V)
    (hs:∀x y,x∉Set.range e∨y∉Set.range e→(B-A) x y=0)
    (hP:IsUnit (A⁻¹.submatrix e e)) :
    IsUnit (B⁻¹.submatrix e e) ∧
      (B⁻¹.submatrix e e)⁻¹=(A⁻¹.submatrix e e)⁻¹+(B-A).submatrix e e := by
  let P:=A⁻¹.submatrix e e
  let T:=B⁻¹.submatrix e e
  let W:=(B-A).submatrix e e
  have hu: T+T*W*P=P := (inverse_embedded_finite_rank_updates A B hA hB e hs).2
  have hPi:P*P⁻¹=1:=Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP)
  have hprod:T*(P⁻¹+W)=1:=by
    have hh:=congrArg (fun M:Matrix I I ℂ=>M*P⁻¹) hu
    dsimp only at hh
    rw [Matrix.add_mul,Matrix.mul_assoc,Matrix.mul_assoc,hPi,Matrix.mul_one] at hh
    simpa only [Matrix.mul_add] using hh
  exact ⟨Matrix.isUnit_of_right_inverse hprod,Matrix.inv_eq_right_inv hprod⟩

theorem supported_small_update_rows (A B:Matrix V V ℂ)(hA:IsUnit A)(hB:IsUnit B)(e:I↪V)
    (hs:∀x y,x∉Set.range e∨y∉Set.range e→(B-A) x y=0)
    (hP:IsUnit (A⁻¹.submatrix e e)) (C δ:ℝ)(hC:0≤C)(hδ:0≤δ)
    (hr:∀i,∑j,‖A⁻¹ (e i) (e j)‖≤C)(hc:∀j,∑i,‖A⁻¹ (e i) (e j)‖≤C)
    (he:∀i j,‖(B-A) (e i) (e j)‖≤δ)(hsmall:(Fintype.card I:ℝ)*C*δ≤1/2) :
    (∀i,∑j,‖B⁻¹ (e i) (e j)‖≤2*C) ∧
      (∀j,∑i,‖B⁻¹ (e i) (e j)‖≤2*C) := by
  let P:=A⁻¹.submatrix e e
  let T:=B⁻¹.submatrix e e
  let W:=(B-A).submatrix e e
  obtain ⟨hT,hTi⟩:=supported_retained_inverse_of_old_unit A B hA hB e hs hP
  have hPinv:IsUnit P⁻¹:=Matrix.isUnit_nonsing_inv_iff.mpr hP
  have hTinv:IsUnit T⁻¹:=Matrix.isUnit_nonsing_inv_iff.mpr hT
  have hPii:P⁻¹⁻¹=P:=Matrix.nonsing_inv_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP)
  have hTii:T⁻¹⁻¹=T:=Matrix.nonsing_inv_nonsing_inv T ((Matrix.isUnit_iff_isUnit_det T).mp hT)
  have hTi' : T⁻¹=P⁻¹+W:=hTi
  have herr:∀i j,‖(T⁻¹-P⁻¹) i j‖≤δ:=by
    rw [hTi',add_sub_cancel_left]
    exact he
  have hrows:∀i,∑j,‖P⁻¹⁻¹ i j‖≤C:=by rw [hPii];exact hr
  have hcols:∀j,∑i,‖P⁻¹⁻¹ i j‖≤C:=by rw [hPii];exact hc
  have hh:=inverse_row_column_stability T⁻¹ P⁻¹ hTinv hPinv C δ hC hδ hrows hcols herr hsmall
  rw [hTii] at hh
  exact hh

theorem supported_small_update_target (A B:Matrix V V ℂ)(hA:IsUnit A)(hB:IsUnit B)(e:I↪V)
    (hs:∀x y,x∉Set.range e∨y∉Set.range e→(B-A) x y=0)
    (hP:IsUnit (A⁻¹.submatrix e e)) (C δ w a b:ℝ)
    (hC:0≤C)(hδ:0≤δ)(hw:0≤w)(ha:0≤a)(hb:0≤b)
    (hr:∀i,∑j,‖A⁻¹ (e i) (e j)‖≤C)(hc:∀j,∑i,‖A⁻¹ (e i) (e j)‖≤C)
    (he:∀i j,‖(B-A) (e i) (e j)‖≤δ)(hsmall:(Fintype.card I:ℝ)*C*δ≤1/2)
    (hW:∀i,∑j,‖(B-A) (e i) (e j)‖≤w)(hsym:B⁻¹.IsSymm)
    (x y:V)(hleft:∑i,‖A⁻¹ x (e i)‖≤a)(hright:∑i,‖A⁻¹ y (e i)‖≤b) :
    ‖A⁻¹ x y-B⁻¹ x y‖≤a*w*(b*(1+w*(2*C))) := by
  have hrows:=(supported_small_update_rows A B hA hB e hs hP C δ hC hδ hr hc he hsmall).1
  have hnew:∑i,‖B⁻¹ y (e i)‖≤b*(1+w*(2*C)):=
    inverse_supported_endpoint_row_sum A B hA hB e hs b (2*C) w hb (by positivity) hw y hright hrows hW
  have hnewCap:∀i,‖B⁻¹ (e i) y‖≤b*(1+w*(2*C)):=by
    intro i
    rw [hsym.apply y (e i)]
    exact (Finset.single_le_sum (fun j _=>norm_nonneg (B⁻¹ y (e j))) (Finset.mem_univ i)).trans hnew
  have hdiff:A⁻¹-B⁻¹=A⁻¹*(B-A)*B⁻¹:=by
    rw [Matrix.inv_sub_inv (show IsUnit A↔IsUnit B from ⟨fun _=>hB,fun _=>hA⟩)]
  have hid:=congrArg (fun M:Matrix V V ℂ=>M x y) hdiff
  dsimp only at hid
  rw [Matrix.sub_apply,supported_middle_entry e _ _ _ hs] at hid
  rw [hid]
  have hcap:0≤b*(1+w*(2*C)):=by positivity
  have hinner (i:I):(∑j,‖(B-A) (e i) (e j)‖*‖B⁻¹ (e j) y‖)≤w*(b*(1+w*(2*C))):=by
    calc
      _≤∑j,‖(B-A) (e i) (e j)‖*(b*(1+w*(2*C))):=
        Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left (hnewCap j) (norm_nonneg _))
      _=(∑j,‖(B-A) (e i) (e j)‖)*(b*(1+w*(2*C))):=(Finset.sum_mul ..).symm
      _≤_:=mul_le_mul_of_nonneg_right (hW i) hcap
  calc
    _≤∑i,∑j,‖A⁻¹ x (e i)‖*(‖(B-A) (e i) (e j)‖*‖B⁻¹ (e j) y‖):=by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_mul] using norm_sum_le Finset.univ
        (fun j=>A⁻¹ x (e i)*((B-A) (e i) (e j)*B⁻¹ (e j) y))
    _=∑i,‖A⁻¹ x (e i)‖*(∑j,‖(B-A) (e i) (e j)‖*‖B⁻¹ (e j) y‖):=by simp only [Finset.mul_sum]
    _≤∑i,‖A⁻¹ x (e i)‖*(w*(b*(1+w*(2*C)))):=
      Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (hinner i) (norm_nonneg _))
    _=(∑i,‖A⁻¹ x (e i)‖)*(w*(b*(1+w*(2*C)))):=(Finset.sum_mul ..).symm
    _≤a*(w*(b*(1+w*(2*C)))):=mul_le_mul_of_nonneg_right hleft (mul_nonneg hw hcap)
    _=_:=by ring

end LocalLaw
