import LocalLaw.ActualOmittedLeafCovariance
import LocalLaw.OmittedLeafIdentification

/-! # Actual kept-slot row bounds and q normalization

The scalar old-slot covariance controls a genuine complement deletion.
This proves the kept leaf rows; the normalized update is then applied to
the actual common deficient model and gives the true restored core.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 3500000
namespace LocalLaw
local instance actualOmittedKeptRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}{ι : Type}[Fintype ι]

abbrev omittedKeptCompletion (g : RegularGraph N d)(hd : 1≤d)(T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T)(samples : LocalSamplingFiber g.graph T)
    (selector : ℕ)(S : Set (Tᶜ : Set (Fin N))) :=
  (g.omittedCommonModel T labels samples selector S).attachLeaves hd
    ((g.admissibleState T labels samples).omittedAllMate selector S ∘
      (g.admissibleState T labels samples).omittedKeptEmbedding selector S)
    (g.omittedKeptMate_restore_budget T labels samples selector S)

theorem actual_omitted_kept_rows (g : RegularGraph N d)(hd : 3≤d)(T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T)(samples : LocalSamplingFiber g.graph T)
    (selector : ℕ)(S : Set (Tᶜ : Set (Fin N)))(q p z : ℂ)(hz : 0<z.im)(hq : 0≤q.im)
    (hp : p≠0)(σ W : ℝ)(hσ : 0≤σ)(hW : 0≤W) :
    let s := g.admissibleState T labels samples
    let I := s.OmittedOldLeaves selector S ⊕ s.OmittedExtraLeaves selector S
    let J := s.OmittedOrdinaryLeaves selector S ⊕ s.OmittedExtraLeaves selector S
    letI : DecidableEq (s.OmittedCore selector S) := fun a b => Classical.propDecidable (a=b)
    letI : DecidableEq I := fun a b => Classical.propDecidable (a=b)
    letI : DecidableEq J := fun a b => Classical.propDecidable (a=b)
    let H := g.omittedAllCompletion (by omega) T labels samples selector S
    (∀i j:s.OmittedOldLeaves selector S,
      ‖H.extensionGreen q z (.inr (.inl i)) (.inr (.inl j))-(if i=j then p else 0)‖≤σ) →
    ((Fintype.card I:ℝ)*‖p⁻¹‖*σ≤1/2) →
    (∀x,∑l:I,‖H.extensionGreen q z x (.inr l)‖≤W) →
    let K := g.omittedKeptCompletion (by omega) T labels samples selector S
    (∀x,∑j:J,‖K.extensionGreen q z x (.inr j)‖≤W+2*W*‖p⁻¹‖*W) ∧
      (∀x,∑j:J,‖K.extensionGreen q z (.inr j) x‖≤W+2*W*‖p⁻¹‖*W) := by
  dsimp only
  let s := g.admissibleState T labels samples
  letI : DecidableEq (s.OmittedCore selector S) := fun a b => Classical.propDecidable (a=b)
  letI : DecidableEq (s.OmittedOldLeaves selector S ⊕ s.OmittedExtraLeaves selector S) := fun a b => Classical.propDecidable (a=b)
  letI : DecidableEq (s.OmittedOrdinaryLeaves selector S ⊕ s.OmittedExtraLeaves selector S) := fun a b => Classical.propDecidable (a=b)
  let C := g.omittedCommonModel T labels samples selector S
  let H := g.omittedAllCompletion (by omega:1≤d) T labels samples selector S
  let e := s.omittedKeptEmbedding selector S
  intro hcov hsmall hrows
  have hr : ∀l k:LeafFamilyComplement e,
      ‖H.extensionGreen q z (.inr l.val) (.inr k.val)-(if l=k then p else 0)‖≤σ := by
    intro l k
    obtain ⟨i,hi⟩ := s.omittedComplement_is_old selector S l
    obtain ⟨j,hj⟩ := s.omittedComplement_is_old selector S k
    have heq : l=k ↔ i=j := by
      constructor
      · intro h
        exact Sum.inl.inj (hi.symm.trans ((congrArg Subtype.val h).trans hj))
      · intro h
        exact Subtype.ext (hi.trans ((congrArg Sum.inl h).trans hj.symm))
    simpa only [hi,hj,heq] using hcov i j
  have hc : (Fintype.card (LeafFamilyComplement e):ℝ) ≤
      (Fintype.card (s.OmittedOldLeaves selector S ⊕ s.OmittedExtraLeaves selector S):ℝ) := by
    exact_mod_cast Fintype.card_subtype_le (fun l => l ∉ Set.range e)
  have hsmall' : (Fintype.card (LeafFamilyComplement e):ℝ)*‖p⁻¹‖*σ≤1/2 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (norm_nonneg _)) hσ).trans hsmall
  exact C.attachLeaves_subfamily_rows_cols hd (s.omittedAllMate selector S)
    (g.omittedAllMate_restore_budget T labels samples selector S) e q z p hz hq hp σ W hσ hW hr hsmall' hrows

theorem actual_omitted_kept_normalization (g : RegularGraph N d)(hd : 3≤d)(T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T)(samples : LocalSamplingFiber g.graph T)
    (selector : ℕ)(S : Set (Tᶜ : Set (Fin N)))(q z : ℂ)(hq0 : q≠0)(hz : 0<z.im)(hq : 0≤q.im)
    (C : ℝ)(hC : 0≤C) :
    let s := g.admissibleState T labels samples
    let J := s.OmittedOrdinaryLeaves selector S ⊕ s.OmittedExtraLeaves selector S
    letI : DecidableEq (s.OmittedCore selector S) := fun a b => Classical.propDecidable (a=b)
    letI : DecidableEq J := fun a b => Classical.propDecidable (a=b)
    let K := g.omittedKeptCompletion (by omega) T labels samples selector S
    (∀x,∑j:J,‖K.extensionGreen q z x (.inr j)‖≤C) →
    ((Fintype.card J:ℝ)*C*‖(1+z*q+q^2)/q‖≤1/2) →
    ∀x y:s.OmittedCore selector S,
      ‖K.extensionGreen q z (.inl x) (.inl y)-
        (g.omittedKeptRestoredModel T labels samples selector S).extensionGreen q z x y‖≤
      C*‖(1+z*q+q^2)/q‖*(C*(1+‖(1+z*q+q^2)/q‖*(2*C))) := by
  dsimp only
  intro hrows hsmall x y
  exact (g.omittedCommonModel T labels samples selector S).normalized_leaf_target_stability hd _
    (g.omittedKeptMate_restore_budget T labels samples selector S) q z hq0 hz hq C C C hC hC hC
    (fun j => hrows (.inr j)) hsmall x y (hrows (.inl x)) (hrows (.inl y))

end RegularGraph
end LocalLaw
