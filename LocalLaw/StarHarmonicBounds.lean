import LocalLaw.ModelStarHarmonic
import LocalLaw.PhysicalTailRadiusLoss
import LocalLaw.CappedPairCapture

/-! # Harmonic coefficient bounds without a sampled-vertex count loss -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance starHarmonicBoundsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {I J:Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype J] in
theorem harmonic_delta_row_bound (x:I⊕J) :
    (∑i:I,‖(if x=Sum.inl i then (1:ℂ) else 0)‖)≤1 := by
  cases x <;> simp [eq_comm,apply_ite norm]

theorem harmonic_row_l1 (G:Matrix (I⊕J) J ℂ)(U:Matrix J I ℂ)
    (a:Matrix (I⊕J) I ℂ)(x:I⊕J)(B w:ℝ)(_hB:0≤B)(hw:0≤w)
    (ha:∀i,a x i=(if x=Sum.inl i then 1 else 0)-∑j:J,G x j*U j i)
    (hG:(∑j:J,‖G x j‖)≤B)(hU:∀j:J,∑i:I,‖U j i‖≤w) :
    (∑i:I,‖a x i‖)≤1+B*w := by
  have hp (i:I):‖a x i‖≤‖(if x=Sum.inl i then (1:ℂ) else 0)‖+
      ∑j:J,‖G x j‖*‖U j i‖:=by
    rw[ha i]
    exact (norm_sub_le _ _).trans (add_le_add_left (by simpa only [norm_mul] using norm_sum_le Finset.univ (fun j=>G x j*U j i)) _)
  have hprod:(∑j:J,‖G x j‖*(∑i:I,‖U j i‖))≤B*w:=by
    calc
      _≤∑j:J,‖G x j‖*w:=Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left (hU j) (norm_nonneg _))
      _=(∑j:J,‖G x j‖)*w:=(Finset.sum_mul ..).symm
      _≤B*w:=mul_le_mul_of_nonneg_right hG hw
  calc
    _≤∑i:I,(‖(if x=Sum.inl i then (1:ℂ) else 0)‖+∑j:J,‖G x j‖*‖U j i‖):=
      Finset.sum_le_sum (fun i _=>hp i)
    _=(∑i:I,‖(if x=Sum.inl i then (1:ℂ) else 0)‖)+∑j:J,‖G x j‖*(∑i:I,‖U j i‖):=by
      rw[Finset.sum_add_distrib,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _≤1+B*w:=add_le_add (harmonic_delta_row_bound x) hprod

omit [Fintype I] in
/-- Only active couplings require a far-column bound. -/
theorem harmonic_entry_bound (G:Matrix (I⊕J) J ℂ)(U:Matrix J I ℂ)
    (a:Matrix (I⊕J) I ℂ)(x:I⊕J)(i:I)(D α F:ℝ)(_hD:0≤D)(hα:0≤α)(hF:0≤F)
    (ha:a x i=(if x=Sum.inl i then 1 else 0)-∑j:J,G x j*U j i)
    (hdelta:‖(if x=Sum.inl i then (1:ℂ) else 0)‖≤D)
    (hU:∀j,‖U j i‖≤α)(hG:∀j,U j i≠0→‖G x j‖≤F) :
    ‖a x i‖≤D+(Fintype.card J:ℝ)*F*α := by
  have hp (j:J):‖G x j*U j i‖≤F*α:=by
    by_cases h:U j i=0
    · rw[h,mul_zero,norm_zero];exact mul_nonneg hF hα
    · rw[norm_mul]
      exact mul_le_mul (hG j h) (hU j) (norm_nonneg _) hF
  rw[ha]
  calc
    _≤‖(if x=Sum.inl i then (1:ℂ) else 0)‖+‖∑j:J,G x j*U j i‖:=norm_sub_le _ _
    _≤D+∑j:J,‖G x j*U j i‖:=add_le_add hdelta (norm_sum_le _ _)
    _≤D+∑_j:J,F*α:=add_le_add_left (Finset.sum_le_sum (fun j _=>hp j)) _
    _=D+(Fintype.card J:ℝ)*F*α:=by simp;ring

end LocalLaw
