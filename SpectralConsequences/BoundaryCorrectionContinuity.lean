import SpectralConsequences.CavityBoundaryTotalWeights
import SpectralConsequences.SourceTraceConditionalDrift
import LocalLaw.FiniteBoundaryContinuity

/-! Quantitative q-to-physical sensitivity of the averaged correction. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance boundaryCorrectionContinuityDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {I:Type*}[Fintype I]

def finiteBoundaryCorrection (c α q:ℂ) (w:I→ℂ):ℂ:=
  c*(1+α*q)^2*(∑i:I,∑j:I,if i=j then 0 else w i*w j)

theorem finiteBoundaryCorrection_continuity (c α q m:ℂ) (w v:I→ℂ) (C H:ℝ)
    (hC:0≤C) (hH:0≤H) (hα:‖α‖≤1) (hq:‖α*q‖≤1) (hm:‖α*m‖≤1)
    (hw:∀i,‖w i‖≤C) (hv:∀i,‖v i‖≤C)
    (hchange:∀i,‖w i-v i‖≤H*‖q-m‖):
    ‖finiteBoundaryCorrection c α q w-finiteBoundaryCorrection c α m v‖≤
      ‖c‖*(Fintype.card I:ℝ)^2*(8*C*H+4*C^2)*‖q-m‖:=by
  let A:ℂ:=1+α*q
  let B:ℂ:=1+α*m
  have hA:‖A‖≤2:=(norm_add_le _ _).trans (by simpa only [norm_one] using (show 1+‖α*q‖≤2 by linarith))
  have hB:‖B‖≤2:=(norm_add_le _ _).trans (by simpa only [norm_one] using (show 1+‖α*m‖≤2 by linarith))
  have hAB:‖A-B‖≤‖q-m‖:=by
    have he:A-B=α*(q-m):=by dsimp only [A,B];ring
    rw [he,norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hα
  have hsq:‖A^2-B^2‖≤4*‖q-m‖:=by
    have he:A^2-B^2=(A-B)*(A+B):=by ring
    rw [he,norm_mul]
    have hsum:‖A+B‖≤4:=(norm_add_le _ _).trans (by linarith)
    exact (mul_le_mul hAB hsum (norm_nonneg _) (norm_nonneg _)).trans_eq (by ring)
  have hprod (i j:I):‖w i*w j-v i*v j‖≤2*C*H*‖q-m‖:=by
    have he:w i*w j-v i*v j=(w i-v i)*w j+v i*(w j-v j):=by ring
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul]
    exact (add_le_add
      (mul_le_mul (hchange i) (hw j) (norm_nonneg _) (by positivity))
      (mul_le_mul (hv i) (hchange j) (norm_nonneg _) hC)).trans_eq (by ring)
  have hpoint (i j:I):‖A^2*(w i*w j)-B^2*(v i*v j)‖≤(8*C*H+4*C^2)*‖q-m‖:=by
    have he:A^2*(w i*w j)-B^2*(v i*v j)=
        A^2*(w i*w j-v i*v j)+(A^2-B^2)*(v i*v j):=by ring
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_pow,norm_mul,norm_mul]
    have hw2:‖A‖^2≤4:=by nlinarith [norm_nonneg A]
    have hv2:‖v i‖*‖v j‖≤C^2:=(mul_le_mul (hv i) (hv j) (norm_nonneg _) hC).trans_eq (by ring)
    exact (add_le_add
      (mul_le_mul hw2 (hprod i j) (norm_nonneg _) (by norm_num))
      (mul_le_mul hsq hv2 (by positivity) (by positivity))).trans_eq (by ring)
  have he:finiteBoundaryCorrection c α q w-finiteBoundaryCorrection c α m v=
      c*(∑i:I,∑j:I,if i=j then 0 else A^2*(w i*w j)-B^2*(v i*v j)):=by
    simp only [finiteBoundaryCorrection,A,B,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;>ring
  rw [he,norm_mul]
  have hsum:‖∑i:I,∑j:I,if i=j then 0 else A^2*(w i*w j)-B^2*(v i*v j)‖≤
      (Fintype.card I:ℝ)^2*((8*C*H+4*C^2)*‖q-m‖):=by
    apply ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _=>norm_sum_le _ _))).trans
    calc
      _≤∑_i:I,∑_j:I,(8*C*H+4*C^2)*‖q-m‖:=by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        by_cases hij:i=j
        · simp only [hij,if_true,norm_zero];positivity
        · simpa only [hij,if_false] using hpoint i j
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring
  exact (mul_le_mul_of_nonneg_left hsum (norm_nonneg _)).trans_eq (by ring)

end SpectralConsequences
#print axioms SpectralConsequences.finiteBoundaryCorrection_continuity
