import LocalLaw.PairedBoundaryParameters

/-! # Derived log-five column budget from the proved paired entry pattern -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance boundaryColumnParametersDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The entry pattern, actual endpoint count and quadratic-log exception
count imply the source column budget. No D column conclusion is assumed. -/
theorem boundary_defect_source_column_budget {I : Type*} [Fintype I]
    (Dmat : I → I → ℂ) (bad : Finset I) (a : ℕ)
    (L ε nEndpoint δold δ φ C w U V D0 : ℝ)
    (ha : 1≤a) (hL : 1≤L) (hε : 0≤ε) (hn : 0≤nEndpoint)
    (hδold : 0≤δold) (hδ : δold≤δ) (hφ : 0≤φ) (hC : 0≤C) (hw : 0≤w)
    (hU : 0≤U) (hV : 0≤V) (hD0 : 0≤D0)
    (hcap : ε*L^(4*a)≤1) (hcount : nEndpoint≤U*L^(2*a))
    (hlabelcount : (Fintype.card I:ℝ)≤nEndpoint)
    (hbad : (bad.card:ℝ)≤V*L^2) (herror : δ≤D0*L^3*ε) (hcorrelation : φ*L^(4*a)≤ε)
    (hglobal : ∀ i j, ‖Dmat i j‖≤δ)
    (hgood : ∀ i j, i≠j → (i∉bad ∨ j∉bad) →
      ‖Dmat i j‖≤pairedEndpointGoodError C w δold nEndpoint φ) (j : I) :
    ∑ i, ‖Dmat i j‖≤sparseBoundaryColumnConstant U V D0 (pairedBoundaryCoefficient C w)*L^5*ε := by
  have hδ0 : 0≤δ := hδold.trans hδ
  let γ := pairedEndpointGoodError C w δold nEndpoint φ
  have hγ : 0≤γ := by dsimp only [γ,pairedEndpointGoodError]; positivity
  have hG : 0≤pairedBoundaryCoefficient C w := by unfold pairedBoundaryCoefficient; positivity
  have hbase := sparse_boundary_defect_column_sum Dmat bad bad.card δ γ le_rfl hδ0 hγ hglobal hgood j
  have hmore : ((bad.card:ℝ)+1)*δ+(Fintype.card I:ℝ)*γ≤((bad.card:ℝ)+1)*δ+nEndpoint*γ :=
    add_le_add_left (mul_le_mul_of_nonneg_right hlabelcount hγ) _
  exact hbase.trans (hmore.trans (sparse_boundary_source_column_budget a L ε nEndpoint (bad.card:ℝ) δ φ γ
    U V D0 (pairedBoundaryCoefficient C w) ha hL hε hn (Nat.cast_nonneg _) hδ0 hφ hγ
      hU hV hD0 hG hcap hcount hbad herror hcorrelation
      (pairedEndpointGoodError_monomial_bound C w δold δ nEndpoint φ hC hw hδold hδ hn hφ)))

end LocalLaw
