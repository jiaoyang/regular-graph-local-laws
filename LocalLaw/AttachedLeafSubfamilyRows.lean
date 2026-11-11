import LocalLaw.AttachedLeafPartition
import LocalLaw.NormalizedLeafTargetStability

/-! # Proved rows and normalization after deleting an arbitrary leaf subfamily

Only the deleted leaves require scalar covariance. The kept leaves may be
arbitrary deficit-consuming attachments. Full/kept precision units and the
exact principal model identity are derived from genuine deficient models.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 3000000
namespace LocalLaw
local instance attachedLeafSubfamilyRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V L J : Type}[Fintype V][Fintype L][Fintype J]

theorem finite_norm_sum_embedding_le {I K : Type}[Fintype I][Fintype K]
    (e : I↪K)(f : K→ℂ) : (∑i:I,‖f (e i)‖) ≤ ∑k:K,‖f k‖ := by
  classical
  calc
    _ = ∑k∈Finset.univ.image e,‖f k‖ := by
      rw [Finset.sum_image]
      intro a _ b _ h
      exact e.injective h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => norm_nonneg _)

namespace DeficientGraph
variable {d : ℕ}

theorem attachLeaves_subfamily_rows_cols (g : DeficientGraph V d)(hd : 3≤d)(mate : L→V)
    (hr : ∀v,multiLeafMultiplicity mate v≤g.deficit v)(e : J↪L)(q z p : ℂ)
    (hz : 0<z.im)(hq : 0≤q.im)(hp : p≠0)(δ W : ℝ)(hδ : 0≤δ)(hW : 0≤W)
    (herror : ∀l k:LeafFamilyComplement e,
      ‖(g.attachLeaves (by omega) mate hr).extensionGreen q z (.inr l.val) (.inr k.val)-
        (if l=k then p else 0)‖ ≤ δ)
    (hsmall : (Fintype.card (LeafFamilyComplement e):ℝ)*‖p⁻¹‖*δ≤1/2)
    (hrows : ∀x:V⊕L,∑l:L,‖(g.attachLeaves (by omega) mate hr).extensionGreen q z x (.inr l)‖≤W) :
    let kept := g.attachLeaves (by omega) (mate∘e)
      (fun v => (subfamily_leaf_multiplicity_le mate e v).trans (hr v))
    (∀x:V⊕J,∑j:J,‖kept.extensionGreen q z x (.inr j)‖≤W+2*W*‖p⁻¹‖*W) ∧
      (∀x:V⊕J,∑j:J,‖kept.extensionGreen q z (.inr j) x‖≤W+2*W*‖p⁻¹‖*W) := by
  dsimp only
  let H := g.attachLeaves (by omega) mate hr
  let M := g.leafSubfamilyMatrix hd mate hr e q z
  let f := leafBlockPartition (V:=V) e
  let kept := g.attachLeaves (by omega) (mate∘e)
    (fun v => (subfamily_leaf_multiplicity_le mate e v).trans (hr v))
  have hi (a b:(V⊕J)⊕LeafFamilyComplement e) : M⁻¹ a b=H.extensionGreen q z (f a) (f b) :=
    congrArg (fun P => P a b) (g.leafSubfamilyMatrix_inverse hd mate hr e q z)
  have hsub (x:V⊕L) (k:J↪L) :
      (∑i:J,‖H.extensionGreen q z x (.inr (k i))‖)≤W :=
    (finite_norm_sum_embedding_le k (fun l => H.extensionGreen q z x (.inr l))).trans (hrows x)
  have hu := g.leafSubfamilyMatrix_units hd mate hr e q z hz hq
  have he : ∀l k:LeafFamilyComplement e,
      ‖M⁻¹ (.inr l) (.inr k)-(if l=k then p else 0)‖≤δ := by
    intro l k
    simpa only [hi,leafBlockPartition_removed] using herror l k
  have hb : ∀i:V⊕J,∑j:J,‖M⁻¹ (.inl i) (.inl (.inr j))‖≤W := by
    intro i
    simpa only [hi,leafBlockPartition_kept] using hsub (f (.inl i)) e
  have hc : ∀i:V⊕J,∑l:LeafFamilyComplement e,‖M⁻¹ (.inl i) (.inr l)‖≤W := by
    intro i
    simpa only [hi,leafBlockPartition_removed] using
      (finite_norm_sum_embedding_le (Function.Embedding.subtype (fun l:L => l ∉ Set.range e))
        (fun l => H.extensionGreen q z (f (.inl i)) (.inr l))).trans (hrows (f (.inl i)))
  have hrm : ∀l:LeafFamilyComplement e,∑j:J,‖M⁻¹ (.inr l) (.inl (.inr j))‖≤W := by
    intro l
    simpa only [hi,leafBlockPartition_removed,leafBlockPartition_kept] using hsub (.inr l.val) e
  have hrow := core_inverse_scalar_leaf_remaining_rows M hu.1 hu.2 Sum.inr p hp δ W W W hδ hW he hsmall hb hc hrm
  rw [g.leafSubfamilyMatrix_core hd mate hr e q z] at hrow
  change ∀x:V⊕J,∑j:J,‖kept.extensionGreen q z x (.inr j)‖≤W+2*W*‖p⁻¹‖*W at hrow
  refine ⟨hrow,fun x => ?_⟩
  change (∑j:J,‖kept.extensionGreen q z (.inr j) x‖)≤W+2*W*‖p⁻¹‖*W
  calc
    _ = ∑j:J,‖kept.extensionGreen q z x (.inr j)‖ := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg norm ((kept.extensionGreen_isSymm q z).apply (.inr j) x).symm
    _ ≤ _ := hrow x

end DeficientGraph
end LocalLaw
