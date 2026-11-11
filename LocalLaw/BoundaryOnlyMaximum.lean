import LocalLaw.BoundaryMaxBootstrap

/-! # Boundary maximum using only columns on the boundary

The finite maximum tests boundary targets only. Its contraction therefore
uses the sharper boundary-column sum, without the square-root volume loss
needed for arbitrary targets.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance boundaryOnlyMaximumDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {I F : Type*} [Fintype F]

theorem boundary_row_max_from_boundary_columns
    (R P : Matrix I I ℂ) (l : F → I) (D : Matrix F F ℂ) (c : ℂ) (i : I)
    (M e S : ℝ) (hM : 0≤M) (he : 0≤e) (hS : 0≤S) (hc : ‖c‖≤1)
    (hroot : ∀ a,‖P i (l a)‖≤M)
    (hD : ∀ b,∑ a,‖D a b‖≤e)
    (hP : ∀ β,∑ b,‖P (l b) (l β)‖≤S)
    (hidentity : ∀ β,
      R i (l β)-P i (l β)=c*(∑ a,∑ b,P i (l a)*D a b*P (l b) (l β))+
        c*(∑ a,∑ b,(R i (l a)-P i (l a))*D a b*P (l b) (l β)))
    (hsmall : e*S≤1/2) :
    ∀ a,‖R i (l a)-P i (l a)‖≤2*M*e*S := by
  rcases isEmpty_or_nonempty F with hF|hF
  · letI : IsEmpty F := hF
    exact fun a => isEmptyElim a
  · letI : Nonempty F := hF
    let Γ : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun a => ‖R i (l a)-P i (l a)‖)
    have hpoint (a : F) : ‖R i (l a)-P i (l a)‖≤Γ :=
      Finset.le_sup' (fun a => ‖R i (l a)-P i (l a)‖) (Finset.mem_univ a)
    have hΓ : 0≤Γ := (norm_nonneg _).trans (hpoint (Classical.choice hF))
    have hlead (β : F) : ‖c*(∑ a,∑ b,P i (l a)*D a b*P (l b) (l β))‖≤M*e*S := by
      rw [norm_mul]
      have hh := boundary_double_sum_bound (fun a => P i (l a)) D (fun b => P (l b) (l β))
        M e S hM he hroot hD (hP β)
      exact (mul_le_mul_of_nonneg_left hh (norm_nonneg c)).trans
        (mul_le_of_le_one_left (by positivity) hc)
    have hrem (β : F) : ‖c*(∑ a,∑ b,(R i (l a)-P i (l a))*D a b*P (l b) (l β))‖≤Γ*e*S := by
      rw [norm_mul]
      have hh := boundary_double_sum_bound (fun a => R i (l a)-P i (l a)) D (fun b => P (l b) (l β))
        Γ e S hΓ he hpoint hD (hP β)
      exact (mul_le_mul_of_nonneg_left hh (norm_nonneg c)).trans
        (mul_le_of_le_one_left (by positivity) hc)
    have hbound (β : F) : ‖R i (l β)-P i (l β)‖≤(M+Γ)*e*S := by
      rw [hidentity β]
      exact ((norm_add_le _ _).trans (add_le_add (hlead β) (hrem β))).trans_eq (by ring)
    have hmax : Γ≤(M+Γ)*e*S :=
      Finset.sup'_le Finset.univ_nonempty (fun a => ‖R i (l a)-P i (l a)‖) (fun a _ => hbound a)
    have hcontract : e*S*Γ≤Γ/2 := by
      exact (mul_le_mul_of_nonneg_right hsmall hΓ).trans_eq (by ring)
    have hΓbound : Γ≤2*M*e*S := by nlinarith only [hmax,hcontract]
    exact fun a => (hpoint a).trans hΓbound

end LocalLaw
