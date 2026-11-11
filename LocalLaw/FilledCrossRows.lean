import LocalLaw.CrossBoundarySchur
import LocalLaw.CutRowAlgebra

/-! # Actual cut-labelled cross rows for filled finite references -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance filledCrossRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Selection
variable {I J V : Type*} [Fintype V] [DecidableEq V]

theorem cutOuterProjection_mul (G : SimpleGraph V) (T : Set V)
    (Q : Matrix (Tᶜ:Set V) J ℂ) (a : BoundaryOrientedEdge G T) (j : J) :
    (cutOuterProjection G T*Q) a j=Q (boundaryOutsideVertex G T a) j := by
  have hpred (v : (Tᶜ:Set V)) : a.val.2=v.val ↔ v=boundaryOutsideVertex G T a :=
    ⟨fun h => Subtype.ext h.symm,fun h => (congrArg Subtype.val h).symm⟩
  simp only [Matrix.mul_apply,cutOuterProjection,hpred,ite_mul,one_mul,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,if_true]

theorem cut_cross_row_formula (G : SimpleGraph V) (d : ℕ) (T : Set V)
    (R : Matrix I T ℂ) (Q : Matrix (Tᶜ:Set V) J ℂ) (i : I) (j : J) :
    (R*(normalizedAdjacency G d).submatrix (Subtype.val:T→V) (Subtype.val:(Tᶜ:Set V)→V)*Q) i j=
      (↑((Real.sqrt ((d:ℝ)-1))⁻¹):ℂ)*
        ∑ a,R i (cutInsideVertex G T a)*Q (boundaryOutsideVertex G T a) j := by
  rw [normalized_cut_incidence]
  calc
    _ = (R*cutInnerCoupling G d T*(cutOuterProjection G T*Q)) i j := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      change (∑ a,(R*cutInnerCoupling G d T) i a*(cutOuterProjection G T*Q) a j)=_
      simp only [mul_cutInnerCoupling,cutOuterProjection_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

end Selection

namespace RegularGraph
variable {N d : ℕ}

theorem physical_cross_row (g : RegularGraph N d) (T : Set (Fin N)) (z : ℂ) (hz : 0<z.im)
    (i : T) (j : (Tᶜ:Set (Fin N))) :
    g.G z i.val j.val= -(↑((Real.sqrt ((d:ℝ)-1))⁻¹):ℂ)*
      ∑ a,g.G z i.val (cutInsideVertex g.graph T a).val*
        (g.deficient.delete T).G z (boundaryOutsideVertex g.graph T a) j := by
  have hh := green_principal_cross T g.H (normalizedAdjacency_isHermitian _ _) z hz
  have hdel : green (g.H.submatrix (Subtype.val:(Tᶜ:Set (Fin N))→Fin N) Subtype.val) z=
      (g.deficient.delete T).G z := by
    change green (g.deficient.H.submatrix (Subtype.val:(Tᶜ:Set (Fin N))→Fin N) Subtype.val) z=_
    rw [←g.deficient.H_delete T]
    rfl
  rw [hdel] at hh
  have he := congrArg (fun A : Matrix T (Tᶜ:Set (Fin N)) ℂ => A i j) hh
  dsimp only [Matrix.submatrix_apply,Matrix.neg_apply] at he
  change g.G z i.val j.val= -((g.G z).submatrix (Subtype.val:T→Fin N) (Subtype.val:T→Fin N)*
    (normalizedAdjacency g.graph d).submatrix (Subtype.val:T→Fin N) (Subtype.val:(Tᶜ:Set (Fin N))→Fin N)*
      (g.deficient.delete T).G z) i j at he
  rw [cut_cross_row_formula g.graph d T] at he
  exact he.trans (by simp only [neg_mul]; rfl)

end RegularGraph

section Bound
variable {F : Type*} [Fintype F]

theorem cut_cross_row_error_bound (c u v : ℂ) (R P X Y : F → ℂ)
    (M Γ e S : ℝ) (hM : 0≤M) (hΓ : 0≤Γ) (hc : ‖c‖≤1)
    (hu : u= -c*∑ a,R a*X a) (hv : v= -c*∑ a,P a*Y a)
    (hR : ∀ a,‖R a‖≤M) (herror : ∀ a,‖R a-P a‖≤Γ)
    (hcolumn : ∑ a,‖X a-Y a‖≤e) (hmodel : ∑ a,‖Y a‖≤S) :
    ‖u-v‖≤M*e+Γ*S := by
  have hdecomp : u-v= -c*((∑ a,R a*(X a-Y a))+(∑ a,(R a-P a)*Y a)) := by
    rw [hu,hv]
    simp only [Finset.sum_sub_distrib, mul_sub,sub_mul,Finset.sum_mul]
    ring
  have hfirst : ‖∑ a,R a*(X a-Y a)‖≤M*e := by
    calc
      _ ≤ ∑ a,‖R a*(X a-Y a)‖ := norm_sum_le _ _
      _ ≤ ∑ a,M*‖X a-Y a‖ := Finset.sum_le_sum (fun a _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hR a) (norm_nonneg _))
      _ = M*∑ a,‖X a-Y a‖ := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hcolumn hM
  have hsecond : ‖∑ a,(R a-P a)*Y a‖≤Γ*S := by
    calc
      _ ≤ ∑ a,‖(R a-P a)*Y a‖ := norm_sum_le _ _
      _ ≤ ∑ a,Γ*‖Y a‖ := Finset.sum_le_sum (fun a _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (herror a) (norm_nonneg _))
      _ = Γ*∑ a,‖Y a‖ := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hmodel hΓ
  rw [hdecomp,norm_mul,norm_neg]
  calc
    _ ≤ ‖(∑ a,R a*(X a-Y a))+(∑ a,(R a-P a)*Y a)‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hc
    _ ≤ ‖∑ a,R a*(X a-Y a)‖+‖∑ a,(R a-P a)*Y a‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hfirst hsecond

end Bound
end LocalLaw
