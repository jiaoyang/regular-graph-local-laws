import LocalLaw.DiagonalSchurComparison
import LocalLaw.PartialTripleSurgery

/-! # Common-index padding of a partially retained leaf block

Omitted leaves have the scalar block p and zero target weights. The padded
matrix is genuinely invertible whenever the retained block is, and its
Schur target correction is exactly the retained correction.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance scalarLeafPaddingDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {I:Type} [Fintype I] [DecidableEq I]

def scalarLeafPadding (E:Set I) (R:Matrix E E ℂ) (p:ℂ):Matrix I I ℂ:=
  (Matrix.fromBlocks R 0 0 (Matrix.diagonal (fun _:(Eᶜ:Set I)=>p))).submatrix
    (Equiv.Set.sumCompl E).symm (Equiv.Set.sumCompl E).symm

def scalarLeafPaddedVector (E:Set I) (a:E→ℂ):I→ℂ:=
  fun i=>Sum.elim a (fun _:(Eᶜ:Set I)=>0) ((Equiv.Set.sumCompl E).symm i)

theorem scalarLeafPadding_inverse (E:Set I) (R:Matrix E E ℂ) (p:ℂ)
    (hR:IsUnit R) (hp:p≠0) :
    IsUnit (scalarLeafPadding E R p)∧
      (scalarLeafPadding E R p)⁻¹=scalarLeafPadding E R⁻¹ p⁻¹ := by
  have hd:=scalar_diagonal_inverse (I:=(Eᶜ:Set I)) p hp
  have hb:=blockDiagonal_inverse R (Matrix.diagonal (fun _:(Eᶜ:Set I)=>p)) hR hd.1
  constructor
  · exact (Matrix.isUnit_submatrix_equiv (Equiv.Set.sumCompl E).symm (Equiv.Set.sumCompl E).symm).mpr hb.1
  · unfold scalarLeafPadding
    rw [Matrix.inv_submatrix_equiv,hb.2,hd.2]

omit [DecidableEq I] in
theorem scalarLeafPaddedVector_sum_norm (E:Set I) (a:E→ℂ) :
    (∑i:I,‖scalarLeafPaddedVector E a i‖)=∑i:E,‖a i‖ := by
  unfold scalarLeafPaddedVector
  have hh:=(Equiv.Set.sumCompl E).symm.sum_comp
    (fun x:E⊕(Eᶜ:Set I)=>‖Sum.elim a (fun _:(Eᶜ:Set I)=>0) x‖)
  rw [hh]
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,norm_zero,Finset.sum_const_zero,add_zero]

theorem scalarLeafPadding_bilinear (E:Set I) (R:Matrix E E ℂ) (p:ℂ) (a b:E→ℂ) :
    schurBilinear (scalarLeafPaddedVector E a) (scalarLeafPadding E R p) (scalarLeafPaddedVector E b)=
      schurBilinear a R b := by
  let φ: I≃E⊕(Eᶜ:Set I):=(Equiv.Set.sumCompl E).symm
  let M:=Matrix.fromBlocks R 0 0 (Matrix.diagonal (fun _:(Eᶜ:Set I)=>p))
  let f:E⊕(Eᶜ:Set I)→E⊕(Eᶜ:Set I)→ℂ:=fun x y=>
    Sum.elim a (fun _=>0) x*M x y*Sum.elim b (fun _=>0) y
  change (∑i:I,∑j:I,f (φ i) (φ j))=schurBilinear a R b
  calc
    _=∑i:I,∑j:E⊕(Eᶜ:Set I),f (φ i) j:=by
      apply Finset.sum_congr rfl
      intro i _
      exact φ.sum_comp (fun j=>f (φ i) j)
    _=∑i:E⊕(Eᶜ:Set I),∑j:E⊕(Eᶜ:Set I),f i j:=φ.sum_comp (fun i=>∑j:E⊕(Eᶜ:Set I),f i j)
    _=schurBilinear a R b:=by
      simp only [Fintype.sum_sum_type,f,M,Sum.elim_inl,Sum.elim_inr,
        Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
        zero_mul,mul_zero,Finset.sum_const_zero,zero_add,add_zero,schurBilinear]

theorem scalarLeafPadding_inverse_bilinear (E:Set I) (R:Matrix E E ℂ) (p:ℂ)
    (hR:IsUnit R) (hp:p≠0) (a b:E→ℂ) :
    schurBilinear (scalarLeafPaddedVector E a) (scalarLeafPadding E R p)⁻¹ (scalarLeafPaddedVector E b)=
      schurBilinear a R⁻¹ b := by
  rw [(scalarLeafPadding_inverse E R p hR hp).2]
  exact scalarLeafPadding_bilinear E R⁻¹ p⁻¹ a b

end LocalLaw
