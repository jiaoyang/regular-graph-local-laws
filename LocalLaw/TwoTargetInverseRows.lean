import LocalLaw.TwoTargetRowExtension

/-! New augmented two-target rows from actual inverse identities. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance twoTargetInverseRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V]

theorem inverse_supported_two_target_rows (A B : Matrix V V ℂ) (hA : IsUnit A) (hB : IsUnit B)
    (e : I ↪ V) (hsupport : ∀ u v, u ∉ Set.range e ∨ v ∉ Set.range e → (B-A) u v=0)
    (x y : V) (K a C b w : ℝ) (hK : 0 ≤ K) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hb : 0 ≤ b) (hw : 0 ≤ w) (hsym : B⁻¹.IsSymm)
    (hOldEntry : ∀ s, s=x ∨ s=y → ∀ t, t=x ∨ t=y → ‖A⁻¹ s t‖ ≤ K)
    (hOldTarget : ∀ s, s=x ∨ s=y → ∑ i, ‖A⁻¹ s (e i)‖ ≤ a)
    (hNewEndpoint : ∀ i, ∑ j, ‖B⁻¹ (e i) (e j)‖ ≤ C)
    (hNewTarget : ∀ s, s=x ∨ s=y → ∑ i, ‖B⁻¹ s (e i)‖ ≤ b)
    (hW : ∀ i, ∑ j, ‖(B-A) (e i) (e j)‖ ≤ w) :
    ∀ v : twoTargetIndexSet e x y,
      ∑ u : twoTargetIndexSet e x y, ‖B⁻¹ v.val u.val‖ ≤ C+3*b+2*(K+a*w*b) := by
  have hpoint (s : V) (hs : s=x ∨ s=y) (t : V) (ht : t=x ∨ t=y) :
      ‖B⁻¹ s t‖ ≤ K+a*w*b := by
    apply inverse_supported_target_entry_bound A B hA hB e hsupport K a b w hK ha hb hw s t
      (hOldEntry s hs t ht) (hOldTarget s hs) ?_ hW
    intro i
    rw [hsym.apply]
    exact (Finset.single_le_sum (fun j _ => norm_nonneg (B⁻¹ t (e j))) (Finset.mem_univ i)).trans
      (hNewTarget t ht)
  exact two_target_row_extension e x y B⁻¹ hsym C b (K+a*w*b) hC hb (by positivity)
    hNewEndpoint hNewTarget hpoint

end LocalLaw
