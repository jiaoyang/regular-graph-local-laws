import LocalLaw.OmittedLeafSeparation
import LocalLaw.WholeLeafCovariance
import LocalLaw.AttachedLeafSubfamilyRows
import LocalLaw.OmittedLeafDiameter
import LocalLaw.SeparatedTargetLeafRows

/-! # Genuine sampled-leaf covariance and kept rows in the actual completion

Every geometric hypothesis is derived from I/J and the old model budget.
Only explicit scalar/logarithmic numeric budgets remain in this finite
lemma. The kept A slots do not require tree covariance.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
namespace LocalLaw
local instance actualOmittedCovarianceDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type}[Fintype V]{T : Set V}{ι : Type}[Fintype ι]

omit [Fintype V] [Fintype ι] in
theorem omittedComplement_is_old (s : LabelledResamplingState V T ι)(selector : ℕ)
    (S : Set (Tᶜ : Set V))(l : LeafFamilyComplement (s.omittedKeptEmbedding selector S)) :
    ∃i : s.OmittedOldLeaves selector S,l.val=.inl i := by
  cases h:l.val with
  | inl i => exact ⟨i,rfl⟩
  | inr i => exact False.elim (l.property ⟨.inr i,h.symm⟩)

end LabelledResamplingState
namespace RegularGraph
variable {N d : ℕ}{ι : Type}[Fintype ι]

theorem actual_omitted_leaf_covariance_rows (g : RegularGraph N d)(hd : 3≤d)
    (T : Set (Fin N))(labels : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T)(selector r : ℕ)(hsep : 2*r+1≤selector)
    (S : Set (Tᶜ : Set (Fin N)))
    (hb : ((g.deficient.delete T).restrict S).ComponentFiniteReferenceBudget)
    (D : ℕ)(hD : ∀u v,((g.deficient.delete T).restrict S).graph.dist u v≤D)
    (q p z : ℂ)(hq : q≠0)(hp : p*(q⁻¹-q/((d:ℂ)-1))=1)(hz : 0<z.im)(hqim : 0≤q.im)
    (B C1 ε L A : ℝ)(hzB : ‖z‖≤B)(num : SourceObservationBounds d r z B C1 ε L A)
    (hprior : ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z) ε)
    (hRlog : ((hereditaryReferenceRadius d D+2:ℕ):ℝ)+1≤A*L)
    (hpbound : ‖p‖≤4)(hqinv : ‖q⁻¹‖≤2*(B+1))(hqpow : ∀n≤4*r+1,‖q‖^n≤2)
    (hcount : (Fintype.card ((g.admissibleState T labels samples).OmittedOldLeaves selector S ⊕
      (g.admissibleState T labels samples).OmittedExtraLeaves selector S):ℝ)*physicalTransfer d z^r≤1) :
    let s := g.admissibleState T labels samples
    letI : DecidableEq (s.OmittedCore selector S) := fun a b => Classical.propDecidable (a=b)
    letI : DecidableEq (s.OmittedOldLeaves selector S ⊕ s.OmittedExtraLeaves selector S) := fun a b => Classical.propDecidable (a=b)
    let H := g.omittedAllCompletion (by omega) T labels samples selector S
    let σ := (treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d)*C1^2*L*ε
    (∀i j:s.OmittedOldLeaves selector S,
      ‖H.extensionGreen q z (.inr (.inl i)) (.inr (.inl j))-(if i=j then p else 0)‖≤σ) ∧
    (∀x,∑l:s.OmittedOldLeaves selector S ⊕ s.OmittedExtraLeaves selector S,
      ‖H.extensionGreen q z x (.inr l)‖≤4*finiteExtraReferenceConstant d) := by
  dsimp only
  let s := g.admissibleState T labels samples
  letI : DecidableEq (s.OmittedCore selector S) := fun a b => Classical.propDecidable (a=b)
  letI : DecidableEq (s.OmittedOldLeaves selector S ⊕ s.OmittedExtraLeaves selector S) := fun a b => Classical.propDecidable (a=b)
  let H := g.omittedAllCompletion (by omega:1≤d) T labels samples selector S
  let R := hereditaryReferenceRadius d D+2
  have hbudget := g.omittedAllCompletion_component_budget (by omega) T labels samples selector S hb
  have hdiam := g.omittedAllCompletion_diameter (by omega) T labels samples selector S hb D hD
  let e : s.OmittedOldLeaves selector S ↪
      (s.OmittedCore selector S ⊕ (s.OmittedOldLeaves selector S ⊕ s.OmittedExtraLeaves selector S)) :=
    {toFun := fun i => .inr (.inl i),inj' := fun _ _ h => Sum.inl.inj (Sum.inr.inj h)}
  have ht (i : s.OmittedOldLeaves selector S) :=
    g.omittedAllCompletion_old_leaf_geometry (by omega) T labels samples selector r (by omega) S i
  have hs (i j : s.OmittedOldLeaves selector S)(hne : i≠j) :
      ((2*r:ℕ):ℕ∞)≤H.graph.edist (e i) (e j) :=
    (g.omittedAllCompletion_leaves_separated (by omega) T labels samples selector (2*r) hsep S
      (.inl i) (.inl j) (fun h => hne (Sum.inl.inj h))).le
  have hcov := H.whole_leaf_scalar_covariance hd hbudget e r R (fun i => (ht i).1)
    (fun i => (ht i).2) hs q p z hq hp hz hqim B C1 ε L A hzB num hprior hdiam hRlog hpbound hqinv hqpow
  have hprior' := hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative num.coefficient_one)
  have hsmall := (DeficientGraph.weak_localization_feedback_budgets d hd z q hz B (C1^2*ε)
    L A (mul_nonneg (sq_nonneg C1) num.error_nonnegative) num.log_one num.log_cap_nonnegative
    num.error_scaled hprior' R R hRlog hRlog num.localization_large).1
  have hrows := H.separated_target_leaf_rows hd hbudget Sum.inr r
    (fun i j hne => g.omittedAllCompletion_leaves_separated (by omega) T labels samples selector (2*r) hsep S i j hne)
    q z hz hqim R hdiam hsmall hcount
  exact ⟨hcov.2,hrows.1⟩

end RegularGraph
end LocalLaw
