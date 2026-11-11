import LocalLaw.VertexDeletionModel
import LocalLaw.ComponentWeakLocalization

/-!
# Actual singleton observations from pair-model approximations

The model radius and the weak error budget are independent. Four pair-model
approximations are transported to one genuine finite matrix, its physical
singleton Schur comparison is proved, and its deleted matrix is localized
back to the actual deficient pair model. No observation or kernel estimate
is assumed.
-/

noncomputable section
namespace LocalLaw
local instance singletonObservationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

def singletonObservationBudget (d : ℕ) (B A L ε δ : ℝ) : ℝ :=
  let E := localizationWeakConstant d B A * L * ε
  2 * (2 * finiteExtraReferenceConstant d * (d : ℝ) + 1) ^ 2 * (δ + E) + E

/-- A genuine observation estimate for a finite common model. Its base
reference class, finite localization and scalar inverse ratios discharge
all analytic model bounds. The radius `r` need not be the radius used to
define `ε`. -/
theorem embedded_singleton_pair_observation {W : Type} [Fintype W] [DecidableEq W]
    (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hzero : ∀ v, g.deficit v = 0) (hbudget : g.ComponentReferenceBudget)
    (H : Matrix W W ℂ) (hH : H.IsHermitian) (e : V ↪ W)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (B : ℝ) (hB : ‖z‖ ≤ B)
    (ε L A δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hL : 1 ≤ L) (hA : 0 ≤ A)
    (hcap : ε * L ^ 4 ≤ 1)
    (hprior : ‖q - semicircleRoot z‖ ≤ scalarScale (spectralScale z) ε)
    (R r : ℕ) (b : V) (i : {v : V // v ≠ b})
    (hR : ∀ k l, g.graph.dist k l ≤ R)
    (hRdel : ∀ k l, (g.deleteVertex b).graph.dist k l ≤ R)
    (hRlog : (R : ℝ) + 1 ≤ A * L) (hrlog : ((4 * r + 1 : ℕ) + 1 : ℝ) ≤ A * L)
    (hlarge : localizationBudgetConstant d B A ≤ L)
    (htail : physicalTransfer d z ^ (2 * r) ≤ ε)
    (hcc : ‖green H z (e i.val) (e i.val) - g.P r z q i.val i.val‖ ≤ δ)
    (hcb : ‖green H z (e i.val) (e b) - g.P r z q i.val b‖ ≤ δ)
    (hbc : ‖green H z (e b) (e i.val) - g.P r z q b i.val‖ ≤ δ)
    (hbb : ‖green H z (e b) (e b) - g.P r z q b b‖ ≤ δ)
    (smallPivot : singletonPivotBudget d q z (2 * finiteExtraReferenceConstant d) *
      (δ + localizationWeakConstant d B A * L * ε) ≤ 1 / 2) :
    ‖green (deletedMatrix H (e b)) z
        ⟨e i.val, fun hh => i.property (e.injective hh)⟩
        ⟨e i.val, fun hh => i.property (e.injective hh)⟩ -
      (g.deleteVertex b).P r z q i i‖ ≤ singletonObservationBudget d B A L ε δ := by
  let E := localizationWeakConstant d B A * L * ε
  have hlocal (k l : V) : ‖g.extensionGreen q z k l - g.P r z q k l‖ ≤ E :=
    g.componentwise_weak_pair_localization hd hbudget.to_componentFinite q z hz hq B hB
      ε L A hε hL hA hcap hprior R r hR hRlog hrlog hlarge htail k l
  have hE : 0 ≤ E := (norm_nonneg _).trans (hlocal b b)
  have transfer (k l : V) (hkl : ‖green H z (e k) (e l) - g.P r z q k l‖ ≤ δ) :
      ‖green H z (e k) (e l) - g.extensionGreen q z k l‖ ≤ δ + E := by
    calc
      _ ≤ ‖green H z (e k) (e l) - g.P r z q k l‖ +
          ‖g.P r z q k l - g.extensionGreen q z k l‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ δ + E := add_le_add hkl (by simpa only [norm_sub_rev] using hlocal k l)
  obtain ⟨smallRef, _, _, _, _⟩ := weak_localization_feedback_budgets d hd z q hz B ε L A
    hε hL hA hcap hprior R (4 * r + 1) hRlog hrlog hlarge
  have hminor := g.embedded_singleton_minor_comparison_of_budget hd hzero hbudget H hH e q z
    hz hq b i R hRdel smallRef (δ + E) (add_nonneg hδ hE)
    (transfer _ _ hcc) (transfer _ _ hcb) (transfer _ _ hbc) (transfer _ _ hbb) smallPivot
  have hdeleted := (g.deleteVertex b).componentwise_weak_pair_localization hd
    (g.deleteVertex_component_budget b hzero hbudget) q z hz hq B hB ε L A hε hL hA hcap hprior
      R r hRdel hRlog hrlog hlarge htail i i
  calc
    _ ≤ ‖green (deletedMatrix H (e b)) z
        ⟨e i.val, fun hh => i.property (e.injective hh)⟩
        ⟨e i.val, fun hh => i.property (e.injective hh)⟩ -
          (g.deleteVertex b).extensionGreen q z i i‖ +
        ‖(g.deleteVertex b).extensionGreen q z i i - (g.deleteVertex b).P r z q i i‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * (2 * finiteExtraReferenceConstant d * (d : ℝ) + 1) ^ 2 * (δ + E) + E :=
      add_le_add hminor hdeleted
    _ = _ := rfl

end DeficientGraph
end LocalLaw
