import LocalLaw.SelectedDepthCounting
import LocalLaw.FullEndpointCardinality
import LocalLaw.FullEndpointMasks
import LocalLaw.KernelSquareSum

/-! # Full switching rows retain a logarithmic gain at a = 12 -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance fullEndpointLogRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} [Fintype V] {T : Set V} {ι : Type} [Fintype ι]

theorem fullPartialIndex_card (s : LabelledResamplingState V T ι) (selector : ℕ)
    (S : Set V) (hs : 1 ≤ selector) :
    Nat.card (s.FullEndpointIndex selector S) ≤
      Nat.card T + 3 * Nat.card (BoundaryOrientedEdge s.graph T) := by
  have hmem (u : s.FullEndpointIndex selector S) :
      (s.fullPartialEmbedding selector S hs u).val ∈ s.fullEndpointRoots selector := by
    rcases u with k | (b | c)
    · rcases k.property.2 with hk | ⟨v,hv,he⟩
      · exact Or.inl hk
      · exact Or.inr ⟨v,Or.inl hv,he⟩
    · exact Or.inr ⟨s.admissibleSampleVertex selector b.val,
        Or.inr (Set.mem_iUnion.mpr ⟨b.val,Or.inl rfl⟩),rfl⟩
    · exact Or.inr ⟨s.admissibleSecondVertex selector c.val,
        Or.inr (Set.mem_iUnion.mpr ⟨c.val,Or.inr rfl⟩),rfl⟩
  let f : s.FullEndpointIndex selector S → s.fullEndpointRoots selector :=
    fun u => ⟨(s.fullPartialEmbedding selector S hs u).val,hmem u⟩
  have hf : Function.Injective f := by
    intro u v h
    apply (s.fullPartialEmbedding selector S hs).injective
    exact Subtype.ext (congrArg (fun x : s.fullEndpointRoots selector => x.val) h)
  exact (Nat.card_le_card_of_injective f hf).trans (s.fullEndpointRoots_card selector)

end LabelledResamplingState

theorem eventually_actual_fullPartialIndex_count (a d : ℕ) (ha : 12 ≤ a) (hd : 3 ≤ d) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (selector : ℕ) (_hs : 1 ≤ selector) (S : Set (Fin N)),
      (Nat.card ((g.admissibleState _ labels samples).FullEndpointIndex selector S) : ℝ) ≤
        fullEndpointCountConstant d * Real.log (N : ℝ) ^ (2 * a - 4) := by
  filter_upwards [eventually_actual_selected_counts a d ha hd] with N hcount
  intro g o z ι _ labels samples selector hs S
  have hc := (g.admissibleState _ labels samples).fullPartialIndex_card selector S hs
  have hr : (Nat.card ((g.admissibleState _ labels samples).FullEndpointIndex selector S) : ℝ) ≤
      (Nat.card (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)) : ℝ) +
      3 * (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))) : ℝ) := by
    exact_mod_cast hc
  have hh := hcount g o z
  dsimp only at hh
  unfold fullEndpointCountConstant
  nlinarith only [hr,hh.1,hh.2]

/-- Cauchy--Schwarz converts the sharper count and actual squared-row bound
into exponent a-1, leaving the necessary spare logarithm. -/
theorem full_mask_log_row_bound {I : Type} [Fintype I] (f : I → ℂ) (a : ℕ)
    (L U S : ℝ) (ha : 2 ≤ a) (hL : 1 ≤ L) (hU : 0 ≤ U) (hS : 0 ≤ S)
    (hcount : (Fintype.card I : ℝ) ≤ U * L ^ (2 * a - 4))
    (hsquare : (∑ i, ‖f i‖ ^ 2) ≤ S * L) :
    (∑ i, ‖f i‖) ≤ (U * S + 1) * L ^ (a - 1) := by
  have hL0 : 0 ≤ L := by linarith
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset I)) (f := fun i => ‖f i‖)
  simp only [Finset.card_univ] at hcs
  have hsq0 : 0 ≤ ∑ i, ‖f i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp : L ^ (2 * a - 4) * L ≤ (L ^ (a - 1)) ^ 2 := by
    calc
      _ = L ^ (2 * a - 3) := by rw [← pow_succ]; congr 1; omega
      _ ≤ L ^ (2 * (a - 1)) := pow_le_pow_right₀ hL (by omega)
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hm := mul_le_mul hcount hsquare hsq0 (mul_nonneg hU (pow_nonneg hL0 _))
  have hfinal : (Fintype.card I : ℝ) * (∑ i, ‖f i‖ ^ 2) ≤
      U * S * (L ^ (a - 1)) ^ 2 := by
    calc
      _ ≤ (U * L ^ (2 * a - 4)) * (S * L) := hm
      _ = U * S * (L ^ (2 * a - 4) * L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (mul_nonneg hU hS)
  have hsum0 : 0 ≤ ∑ i, ‖f i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have htarget0 : 0 ≤ (U * S + 1) * L ^ (a - 1) := by positivity
  have hUS : 0 ≤ U * S := mul_nonneg hU hS
  have hpower0 : 0 ≤ (L ^ (a - 1)) ^ 2 := sq_nonneg _
  nlinarith only [hcs,hfinal,hsum0,htarget0,hUS,hpower0,
    sq_nonneg (U*S),mul_nonneg hUS hpower0]

end LocalLaw
