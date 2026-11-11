import SpectralConsequences.ResampledRootNeighbors
import LocalLaw.MinorIdentity

/-! A one-pivot tree-vacuum comparison, retaining the genuine actual pivot. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem one_pivot_formal_error (a b c v p t q:ℂ) (C P δ:ℝ)
    (hv:v≠0) (hq:q=p-p*t^2) (hC:0≤C) (_hP:0≤P) (hδ:0≤δ)
    (hp:‖p‖≤4) (ht:‖t‖≤1) (hc:‖c‖≤C) (hvP:‖v⁻¹‖≤P)
    (ha:‖a-p‖≤δ) (hb:‖b-p*t‖≤δ) (hc':‖c-p*t‖≤δ) (hv':‖v-p‖≤δ) :
    ‖a-b*c/v-q‖≤(1+(C+8)*P)*δ := by
  have hid:a-b*c/v-q=(a-p)-(b-p*t)*c*v⁻¹-(p*t)*(c-p*t)*v⁻¹+
      (p*t^2)*(v-p)*v⁻¹:=by
    rw [hq,div_eq_mul_inv]
    have hi:v*v⁻¹=1:=mul_inv_cancel₀ hv
    linear_combination -(p*t^2)*hi
  have hpt:‖p*t‖≤4:=by
    rw [norm_mul]
    exact (mul_le_mul hp ht (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  have hpt2:‖p*t^2‖≤4:=by
    rw [norm_mul,norm_pow]
    exact (mul_le_mul hp (pow_le_one₀ (norm_nonneg _) ht) (by positivity) (by norm_num)).trans_eq (by ring)
  rw [hid]
  have h1:‖(b-p*t)*c*v⁻¹‖≤δ*C*P:=by
    simp only [norm_mul]
    exact mul_le_mul (mul_le_mul hb hc (norm_nonneg _) hδ) hvP (norm_nonneg _) (mul_nonneg hδ hC)
  have h2:‖(p*t)*(c-p*t)*v⁻¹‖≤4*δ*P:=by
    rw [norm_mul,norm_mul]
    exact mul_le_mul (mul_le_mul hpt hc' (norm_nonneg _) (by norm_num)) hvP
      (norm_nonneg _) (by positivity)
  have h3:‖(p*t^2)*(v-p)*v⁻¹‖≤4*δ*P:=by
    rw [norm_mul,norm_mul]
    exact mul_le_mul (mul_le_mul hpt2 hv' (norm_nonneg _) (by norm_num)) hvP
      (norm_nonneg _) (by positivity)
  exact ((norm_add_le _ _).trans (add_le_add_right
    ((norm_sub_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)) _)).trans
    (by nlinarith only [ha,h1,h2,h3])

namespace RegularGraph
variable {N d:ℕ}

theorem cavityAtVertex_formal_error (g:LocalLaw.RegularGraph N d) (hd:0<d)
    (o:Fin N) (z:ℂ) (hz:0<z.im) (p t q:ℂ) (C P δ:ℝ)
    (hq:q=p-p*t^2) (hC:0≤C) (hP:0≤P) (hδ:0≤δ) (hp:‖p‖≤4) (ht:‖t‖≤1)
    (hcap:∀v,‖g.G z v o‖≤C) (hpiv:∀v,‖(g.G z v v)⁻¹‖≤P)
    (hdiag:‖g.G z o o-p‖≤δ)
    (hvals:∀v:g.graph.neighborSet o,‖g.G z v.val v.val-p‖≤δ ∧
      ‖g.G z o v.val-p*t‖≤δ ∧ ‖g.G z v.val o-p*t‖≤δ) :
    ‖cavityAtVertex g.graph d z o-q‖≤(1+(C+8)*P)*δ := by
  classical
  have hc:Fintype.card (g.graph.neighborSet o)=d:=by
    rw [SimpleGraph.card_neighborSet_eq_degree]
    exact g.regular o
  letI:Nonempty (g.graph.neighborSet o):=Fintype.card_pos_iff.mp (by simpa only [hc] using hd)
  have hmean:cavityAtVertex g.graph d z o=finiteComplexMean (neighborMinorValue g.graph d z o):=by
    rw [cavityAtVertex_neighbor_sum]
    simp only [finiteComplexMean,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast,hc]
  rw [hmean,←finiteComplexMean_const (E:=g.graph.neighborSet o) q,←finiteComplexMean_sub]
  apply finiteComplexMean_norm_bound
  intro v
  unfold neighborMinorValue
  rw [green_deleted_vertex (normalizedAdjacency g.graph d) (normalizedAdjacency_isHermitian g.graph d) z hz]
  exact one_pivot_formal_error _ _ _ _ p t q C P δ
    (green_diagonal_ne_zero _ (normalizedAdjacency_isHermitian g.graph d) z hz v.val)
    hq hC hP hδ hp ht (hcap _) (hpiv _) hdiag (hvals v).2.1 (hvals v).2.2 (hvals v).1

end RegularGraph
end SpectralConsequences
