import LocalLaw.BoundaryMaxRemainderParameters

/-! # A proved model profile supplies the maximum bootstrap inputs -/

open scoped BigOperators
namespace LocalLaw

structure BoundaryMaxProfile {I F : Type*} [Fintype F] (P : Matrix I I ℂ) (l : F → I)
    (root : I) (a : ℕ) (L U M0 W0 : ℝ) where
  M : ℝ
  S : ℝ
  W : ℝ
  root_nonnegative : 0≤M
  column_nonnegative : 0≤S
  square_nonnegative : 0≤W
  root_bound : ∀ α, ‖P root (l α)‖≤M
  column_bound : ∀ j, ∑ α, ‖P (l α) j‖≤S
  column_square : S^2≤(Fintype.card F:ℝ)*W
  root_count : M*Real.sqrt (Fintype.card F)≤M0
  count : (Fintype.card F:ℝ)≤U*L^(2*a)
  row_log : W≤W0*L

/-- Restrict target vertices and transport the actual boundary labels. -/
noncomputable def BoundaryMaxProfile.pullback {I F J G : Type*} [Fintype F] [Fintype G]
    (P : Matrix I I ℂ) (l : F → I) (root : I) (a : ℕ) (L U M0 W0 : ℝ)
    (profile : BoundaryMaxProfile P l root a L U M0 W0)
    (e : J → I) (labels : G ≃ F) (leaf : G → J) (center : J)
    (hcenter : e center=root) (hleaf : ∀ α,e (leaf α)=l (labels α)) :
    BoundaryMaxProfile (P.submatrix e e) leaf center a L U M0 W0 where
  M := profile.M
  S := profile.S
  W := profile.W
  root_nonnegative := profile.root_nonnegative
  column_nonnegative := profile.column_nonnegative
  square_nonnegative := profile.square_nonnegative
  root_bound := by
    intro α
    simpa only [Matrix.submatrix_apply,hcenter,hleaf] using profile.root_bound (labels α)
  column_bound := by
    intro j
    have heq : (∑ α,‖P (l (labels α)) (e j)‖)=(∑ β,‖P (l β) (e j)‖) :=
      labels.sum_comp (fun β => ‖P (l β) (e j)‖)
    simpa only [Matrix.submatrix_apply,hleaf,heq] using profile.column_bound (e j)
  column_square := by simpa only [Fintype.card_congr labels] using profile.column_square
  root_count := by simpa only [Fintype.card_congr labels] using profile.root_count
  count := by simpa only [Fintype.card_congr labels] using profile.count
  row_log := profile.row_log

/-- The actual row equation, actual D columns and model profile imply the
nonlinear source budget. Neither a row-error nor remainder conclusion is input. -/
theorem BoundaryMaxProfile.bootstrap {I F : Type*} [Fintype F]
    (P R : Matrix I I ℂ) (l : F → I) (root : I) (a : ℕ) (L U M0 W0 ε E e : ℝ)
    (profile : BoundaryMaxProfile P l root a L U M0 W0)
    (D : Matrix F F ℂ) (c : ℂ)
    (ha : 12≤a) (hL : 1≤L) (hε : 0≤ε) (hU : 0≤U) (hM0 : 0≤M0) (hW0 : 0≤W0)
    (hE : 0≤E) (he : 0≤e) (hc : ‖c‖≤1)
    (hcap : ε*L^(4*a)≤1) (herror : e≤E*L^5*ε)
    (hD : ∀ β, ∑ α, ‖D α β‖≤e)
    (hidentity : ∀ j,R root j-P root j =
      c*(∑ α,∑ β,P root (l α)*D α β*P (l β) j)+
      c*(∑ α,∑ β,(R root (l α)-P root (l α))*D α β*P (l β) j))
    (hlargeFeedback : 2*(E*(U+W0+1))≤L)
    (hlargeRemainder : 2*(2*M0*(U+1)*E^2*W0)≤L) :
    (∀ α, ‖R root (l α)-P root (l α)‖≤2*profile.M*e*profile.S) ∧
      ∀ j,‖c*(∑ α,∑ β,(R root (l α)-P root (l α))*D α β*P (l β) j)‖≤ε/(2*L^2) := by
  have hnum := boundary_max_parameter_budgets a L ε (Fintype.card F) profile.M e profile.S profile.W
    U M0 E W0 ha hL hε (Nat.cast_nonneg _) profile.root_nonnegative he profile.column_nonnegative
    profile.square_nonnegative hU hM0 hE hW0 hcap profile.count profile.root_count herror
    profile.column_square profile.row_log hlargeFeedback hlargeRemainder
  have hboot := boundary_row_max_and_remainder R P l D c root profile.M e profile.S
    profile.root_nonnegative he profile.column_nonnegative hc profile.root_bound hD profile.column_bound hidentity hnum.1
  exact ⟨hboot.1,fun j => (hboot.2 j).trans hnum.2⟩

end LocalLaw
