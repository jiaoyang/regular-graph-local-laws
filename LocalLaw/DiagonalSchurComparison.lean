import LocalLaw.MatrixEntryStability

/-! # Diagonal leaf-block comparison with weighted target rows

The leaf count appears only in the inverse contraction. Target corrections
pay the actual row and column weights, rather than the square of that count.
Both models use one global leaf index; zero target weights and a scalar
diagonal on omitted leaves implement partial retention without extra terms.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance diagonalSchurComparisonDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {I:Type} [Fintype I] [DecidableEq I]

theorem scalar_diagonal_inverse (p:ℂ) (hp:p≠0) :
    IsUnit (Matrix.diagonal (fun _:I=>p))∧
      (Matrix.diagonal (fun _:I=>p))⁻¹=Matrix.diagonal (fun _:I=>p⁻¹) := by
  have hprod:Matrix.diagonal (fun _:I=>p)*Matrix.diagonal (fun _:I=>p⁻¹)=1:=by
    ext i j
    by_cases hij:i=j <;>
      simp [Matrix.diagonal_apply,Matrix.mul_apply,Matrix.one_apply,hij,hp]
  exact ⟨Matrix.isUnit_of_right_inverse hprod,Matrix.inv_eq_right_inv hprod⟩

theorem scalar_diagonal_inverse_stability (R:Matrix I I ℂ) (p:ℂ) (hp:p≠0) (hR:IsUnit R)
    (δ:ℝ) (hδ:0≤δ)
    (herror:∀i j,‖R i j-(if i=j then p else 0)‖≤δ)
    (hsmall:(Fintype.card I:ℝ)*‖p⁻¹‖*δ≤1/2) :
    ∀i j,‖R⁻¹ i j-(if i=j then p⁻¹ else 0)‖≤2*‖p⁻¹‖^2*δ := by
  let D:Matrix I I ℂ:=Matrix.diagonal (fun _=>p)
  have hd:=scalar_diagonal_inverse (I:=I) p hp
  have hsum:∀i,∑j,‖D⁻¹ i j‖≤‖p⁻¹‖:=by
    intro i
    rw [hd.2]
    simp [Matrix.diagonal_apply,apply_ite norm]
  have hcol:∀j,∑i,‖D⁻¹ i j‖≤‖p⁻¹‖:=by
    intro j
    rw [hd.2]
    simp [Matrix.diagonal_apply,apply_ite norm]
  have hunit:IsUnit (D+(R-D)):=by simpa only [add_sub_cancel] using hR
  have herr:∀i j,‖(R-D) i j‖≤δ:=by
    intro i j
    simpa only [Matrix.sub_apply,D,Matrix.diagonal_apply] using herror i j
  intro i j
  have hh:=inverse_entry_stability D (R-D) hd.1 hunit ‖p⁻¹‖ δ (norm_nonneg _) hδ hsum hcol herr hsmall i j
  have hi:D⁻¹=Matrix.diagonal (fun _:I=>p⁻¹):=hd.2
  simpa only [add_sub_cancel,Matrix.sub_apply,hi,Matrix.diagonal_apply] using hh

def schurBilinear (a:I→ℂ) (M:Matrix I I ℂ) (b:I→ℂ):ℂ:=
  ∑i,∑j,a i*M i j*b j

theorem schurBilinear_diagonal (a b:I→ℂ) (p:ℂ) :
    schurBilinear a (Matrix.diagonal (fun _:I=>p)) b=p*∑i,a i*b i := by
  unfold schurBilinear
  simp only [Matrix.diagonal_apply]
  have hh:(∑i,∑j,a i*(if i=j then p else 0)*b j)=∑i,a i*p*b i:=by simp
  rw [hh,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [DecidableEq I] in
theorem schurBilinear_entry_error (a b:I→ℂ) (M D:Matrix I I ℂ)
    (σ A B:ℝ) (hσ:0≤σ) (hA:0≤A) (_hB:0≤B)
    (ha:(∑i,‖a i‖)≤A) (hb:(∑i,‖b i‖)≤B)
    (herror:∀i j,‖M i j-D i j‖≤σ) :
    ‖schurBilinear a M b-schurBilinear a D b‖≤σ*A*B := by
  have hid:schurBilinear a M b-schurBilinear a D b=
      ∑i,∑j,a i*(M i j-D i j)*b j:=by
    unfold schurBilinear
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hid]
  calc
    _≤∑i,∑j,‖a i*(M i j-D i j)*b j‖:=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _=>norm_sum_le _ _))
    _≤∑i,∑j,‖a i‖*σ*‖b j‖:=by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (herror i j) (norm_nonneg _)) (norm_nonneg _)
    _=σ*(∑i,‖a i‖)*(∑i,‖b i‖):=by
      simp only [←Finset.mul_sum,←Finset.sum_mul]
      ring
    _≤σ*A*B:=by
      have hh:=mul_le_mul ha hb (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) hA
      convert (mul_le_mul_of_nonneg_left hh hσ) using 1 <;> ring

theorem diagonal_schur_correction_bound (a b:I→ℂ) (R:Matrix I I ℂ) (p:ℂ)
    (σ A B:ℝ) (hσ:0≤σ) (hA:0≤A) (hB:0≤B)
    (ha:(∑i,‖a i‖)≤A) (hb:(∑i,‖b i‖)≤B)
    (herror:∀i j,‖R⁻¹ i j-(if i=j then p⁻¹ else 0)‖≤σ) :
    ‖schurBilinear a R⁻¹ b-p⁻¹*∑i,a i*b i‖≤σ*A*B := by
  rw [←schurBilinear_diagonal a b p⁻¹]
  apply schurBilinear_entry_error a b R⁻¹ (Matrix.diagonal (fun _:I=>p⁻¹)) σ A B hσ hA hB ha hb
  intro i j
  simpa only [Matrix.diagonal_apply] using herror i j

theorem two_diagonal_schur_target_bound (x y p:ℂ) (a b a' b':I→ℂ) (R S:Matrix I I ℂ)
    (δ σ A B A' B':ℝ) (hσ:0≤σ) (hA:0≤A) (hB:0≤B) (hA':0≤A') (hB':0≤B')
    (hxy:‖x-y‖≤δ)
    (ha:(∑i,‖a i‖)≤A) (hb:(∑i,‖b i‖)≤B)
    (ha':(∑i,‖a' i‖)≤A') (hb':(∑i,‖b' i‖)≤B')
    (hR:∀i j,‖R⁻¹ i j-(if i=j then p⁻¹ else 0)‖≤σ)
    (hS:∀i j,‖S⁻¹ i j-(if i=j then p⁻¹ else 0)‖≤σ) :
    ‖(x-schurBilinear a R⁻¹ b)-(y-schurBilinear a' S⁻¹ b')‖≤
      δ+‖p⁻¹‖*(∑i,‖a i*b i-a' i*b' i‖)+σ*(A*B+A'*B') := by
  let eR:=schurBilinear a R⁻¹ b-p⁻¹*∑i,a i*b i
  let eS:=schurBilinear a' S⁻¹ b'-p⁻¹*∑i,a' i*b' i
  have hr:‖eR‖≤σ*A*B:=diagonal_schur_correction_bound a b R p σ A B hσ hA hB ha hb hR
  have hs:‖eS‖≤σ*A'*B':=diagonal_schur_correction_bound a' b' S p σ A' B' hσ hA' hB' ha' hb' hS
  have hprod:‖p⁻¹*((∑i,a i*b i)-(∑i,a' i*b' i))‖≤
      ‖p⁻¹‖*(∑i,‖a i*b i-a' i*b' i‖):=by
    rw [norm_mul,←Finset.sum_sub_distrib]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
  have heq:(x-schurBilinear a R⁻¹ b)-(y-schurBilinear a' S⁻¹ b')=
      ((x-y)-eR)-p⁻¹*((∑i,a i*b i)-(∑i,a' i*b' i))+eS:=by
    dsimp only [eR,eS]
    ring
  rw [heq]
  calc
    _≤(‖x-y‖+‖eR‖)+‖p⁻¹*((∑i,a i*b i)-(∑i,a' i*b' i))‖+‖eS‖:=
      (norm_add_le _ _).trans (add_le_add_right ((norm_sub_le _ _).trans
        (add_le_add_right (norm_sub_le _ _) _)) _)
    _≤(δ+σ*A*B)+‖p⁻¹‖*(∑i,‖a i*b i-a' i*b' i‖)+σ*A'*B':=
      add_le_add (add_le_add (add_le_add hxy hr) hprod) hs
    _=_:=by ring

theorem two_scalar_leaf_schur_target_bound (x y p:ℂ) (a b a' b':I→ℂ) (R S:Matrix I I ℂ)
    (hp:p≠0) (hRunit:IsUnit R) (hSunit:IsUnit S)
    (δtarget δleaf A B A' B':ℝ) (hδleaf:0≤δleaf)
    (hA:0≤A) (hB:0≤B) (hA':0≤A') (hB':0≤B') (hxy:‖x-y‖≤δtarget)
    (ha:(∑i,‖a i‖)≤A) (hb:(∑i,‖b i‖)≤B)
    (ha':(∑i,‖a' i‖)≤A') (hb':(∑i,‖b' i‖)≤B')
    (hR:∀i j,‖R i j-(if i=j then p else 0)‖≤δleaf)
    (hS:∀i j,‖S i j-(if i=j then p else 0)‖≤δleaf)
    (hsmall:(Fintype.card I:ℝ)*‖p⁻¹‖*δleaf≤1/2) :
    ‖(x-schurBilinear a R⁻¹ b)-(y-schurBilinear a' S⁻¹ b')‖≤
      δtarget+‖p⁻¹‖*(∑i,‖a i*b i-a' i*b' i‖)+
        (2*‖p⁻¹‖^2*δleaf)*(A*B+A'*B') := by
  exact two_diagonal_schur_target_bound x y p a b a' b' R S
    δtarget (2*‖p⁻¹‖^2*δleaf) A B A' B' (by positivity) hA hB hA' hB' hxy ha hb ha' hb'
    (scalar_diagonal_inverse_stability R p hp hRunit δleaf hδleaf hR hsmall)
    (scalar_diagonal_inverse_stability S p hp hSunit δleaf hδleaf hS hsmall)

end LocalLaw
