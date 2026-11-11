import LocalLaw.SelectedFirstWeightedCharge
import LocalLaw.ExteriorResolvent

/-! # Actual new-selected-B cut-coupling L1 bound

The normalized adjacency and triangle inequality reduce the matrix row to
actual new incidences. Their old-slot/A charging is proved combinatorially,
including repeated ordinary mates and every accepted attachment.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance selectedFirstCutRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type}[Fintype V]

theorem normalized_cut_product_row_sum (G : SimpleGraph V)(d : ℕ)(U W : Set V)(a : U→ℂ) :
    (∑b:W,‖∑v:U,a v*normalizedAdjacency G d v.val b.val‖) ≤
      (Real.sqrt ((d:ℝ)-1))⁻¹ *
        ∑v:U,(Nat.card {b:W // G.Adj b.val v.val}:ℝ)*‖a v‖ := by
  let α := (Real.sqrt ((d:ℝ)-1))⁻¹
  have hn (v:U) : (∑b:W,‖normalizedAdjacency G d v.val b.val‖)=
      (Nat.card {b:W // G.Adj b.val v.val}:ℝ)*α := by
    simp only [normalizedAdjacency_norm,G.adj_comm,Finset.sum_ite,Finset.sum_const,
      mul_zero,add_zero,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,
      Fintype.card_subtype,α]
  calc
    _ ≤ ∑b:W,∑v:U,‖a v‖*‖normalizedAdjacency G d v.val b.val‖ := by
      apply Finset.sum_le_sum
      intro b _
      simpa only [norm_mul] using norm_sum_le Finset.univ (fun v:U => a v*normalizedAdjacency G d v.val b.val)
    _ = ∑v:U,‖a v‖*(∑b:W,‖normalizedAdjacency G d v.val b.val‖) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [hn]
      ring

namespace LabelledResamplingState
variable {T : Set V}{ι : Type}[Fintype ι]

theorem selectedFirst_new_cut_product_rows (s : LabelledResamplingState V T ι)
    (d selector : ℕ)(a : ((s.selectedFirstSet selector)ᶜ : Set (Tᶜ : Set V))→ℂ) :
    (∑b:s.selectedFirstSet selector,
      ‖∑v:((s.selectedFirstSet selector)ᶜ : Set (Tᶜ : Set V)),
        a v*normalizedAdjacency (outsideGraph (s.fullResample selector).graph T) d v.val b.val‖) ≤
      (Real.sqrt ((d:ℝ)-1))⁻¹ *
        ((∑l:DeletedLeafIndex (outsideGraph s.graph T) (s.selectedFirstSet selector),‖a l.1‖)+
          ∑i:s.AdmissibleSampleIndex selector,‖a (s.admissibleBoundaryCommonVertex selector i)‖) := by
  have hn := normalized_cut_product_row_sum (outsideGraph (s.fullResample selector).graph T) d
    (s.selectedFirstSet selector)ᶜ (s.selectedFirstSet selector) a
  have hc := s.selectedFirst_weighted_neighbor_charge selector (fun v => ‖a v‖) (fun v => norm_nonneg _)
  simp only [←finsum_eq_sum_of_fintype] at hn hc ⊢
  exact hn.trans (mul_le_mul_of_nonneg_left hc
    (inv_nonneg.mpr (Real.sqrt_nonneg _)))

end LabelledResamplingState
end LocalLaw
