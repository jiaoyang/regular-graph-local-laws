import SpectralConsequences.EmpiricalCDF

/-! # Exact empirical CDF values outside a spectral box -/

noncomputable section
namespace SpectralConsequences
local instance empiricalSupportDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem empiricalCDF_eq_zero_of_lt_all {N : ℕ} (values : Fin N → ℝ) (E : ℝ)
    (hvalues : ∀j,E < values j) : empiricalCDF values E=0 := by
  have heq : Finset.univ.filter (fun j => values j ≤ E)=(∅ : Finset (Fin N)) := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro j hj
    exact (not_le_of_gt (hvalues j)) (Finset.mem_filter.mp hj).2
  simp only [empiricalCDF,heq,Finset.card_empty,Nat.cast_zero,zero_div]

theorem empiricalCDF_eq_one_of_all_le {N : ℕ} (hN : 0 < N) (values : Fin N → ℝ) (E : ℝ)
    (hvalues : ∀j,values j ≤ E) : empiricalCDF values E=1 := by
  have heq : Finset.univ.filter (fun j => values j ≤ E)=(Finset.univ : Finset (Fin N)) :=
    Finset.filter_eq_self.mpr (fun j _ => hvalues j)
  simp only [empiricalCDF,heq,Finset.card_univ,Fintype.card_fin,
    div_self (show (N : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))]

end SpectralConsequences
