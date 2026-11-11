import LocalLaw.OrdinaryComponentFeedback
import LocalLaw.SchurLocalizationEstimate
import LocalLaw.BoundarySchurRows
import LocalLaw.DeficitLocalization

/-!
# Actual ordinary cut self-energy is diagonal

Uniqueness of the literal cut boundary edge forces both interior and exterior
endpoints to agree. Genuine deleted Green support then makes the ordinary
component self-energy diagonal, before any norm estimates are applied.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance cutSelfEnergyDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) cutSelfEnergyComponentMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _

variable {V : Type} [Fintype V] [DecidableEq V]

def ordinaryCutVertex (G : SimpleGraph V) (S : Set V) (a : (Sᶜ : Set V)) : Prop :=
  cutExcessCharge G S ((outsideGraph G S).connectedComponentMk a) = 0

theorem ordinary_boundary_pair_unique (G : SimpleGraph V) (S : Set V)
    (hG : G.Connected) (hS : S.Nonempty) (u v : S) (a b : (Sᶜ : Set V))
    (hua : G.Adj u.val a.val) (hvb : G.Adj v.val b.val)
    (hcomp : (outsideGraph G S).connectedComponentMk a = (outsideGraph G S).connectedComponentMk b)
    (hordinary : ordinaryCutVertex G S a) : u = v ∧ a = b := by
  let c := (outsideGraph G S).connectedComponentMk a
  let e : CutBoundaryEdge G S c := ⟨⟨(u.val, a.val), hua, u.property, a.property⟩, rfl⟩
  let f : CutBoundaryEdge G S c := ⟨⟨(v.val, b.val), hvb, v.property, b.property⟩, hcomp.symm⟩
  have hcount : cutMultiplicity G S c = 1 :=
    ((cut_charge_zero_iff G S hG hS c).mp hordinary).2
  letI : Subsingleton (CutBoundaryEdge G S c) := (Nat.card_eq_one_iff_unique.mp hcount).1
  have hef : e = f := Subsingleton.elim _ _
  constructor
  · exact Subtype.ext (congrArg (fun x : CutBoundaryEdge G S c => x.val.val.1) hef)
  · exact Subtype.ext (congrArg (fun x : CutBoundaryEdge G S c => x.val.val.2) hef)

def ordinaryCutCoupling (G : SimpleGraph V) (d : ℕ) (S : Set V) : Matrix S (Sᶜ : Set V) ℂ :=
  fun u a => if ordinaryCutVertex G S a ∧ G.Adj u.val a.val then treeEdgeWeight d else 0

namespace DeficientGraph
variable {d : ℕ}

theorem ordinary_deleted_cross_term_zero (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (hG : g.graph.Connected) (hS : S.Nonempty)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (u v : S) (a b : (Sᶜ : Set V))
    (hua : g.graph.Adj u.val a.val) (hvb : g.graph.Adj v.val b.val)
    (hordinary : ordinaryCutVertex g.graph S a) (hne : u ≠ v ∨ a ≠ b) :
    (g.delete S).extensionGreen q z a b = 0 := by
  by_cases hcomp : (outsideGraph g.graph S).connectedComponentMk a =
      (outsideGraph g.graph S).connectedComponentMk b
  · have hh := ordinary_boundary_pair_unique g.graph S hG hS u v a b hua hvb hcomp hordinary
    exact False.elim (hne.elim (fun h => h hh.1) (fun h => h hh.2))
  · exact g.deleted_extensionGreen_component_zero hd S q z hz hq a b hcomp

/-- The actual ordinary component contribution to the Schur self-energy
has no off-diagonal entries; no component-kernel support premise is assumed. -/
theorem ordinary_cut_self_energy_offDiagonal (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (hG : g.graph.Connected) (hS : S.Nonempty)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (u v : S) (huv : u ≠ v) :
    (ordinaryCutCoupling g.graph d S * (g.delete S).extensionGreen q z *
      (ordinaryCutCoupling g.graph d S).transpose) u v = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : ordinaryCutVertex g.graph S a ∧ g.graph.Adj u.val a.val
  · by_cases hb : ordinaryCutVertex g.graph S b ∧ g.graph.Adj v.val b.val
    · rw [g.ordinary_deleted_cross_term_zero hd S hG hS q z hz hq u v a b ha.2 hb.2 ha.1 (Or.inl huv)]
      simp
    · simp only [ordinaryCutCoupling, Matrix.transpose_apply, if_neg hb, mul_zero]
  · simp only [ordinaryCutCoupling, if_neg ha, zero_mul]

def ordinarySelfEnergyDiagonal (g : DeficientGraph V d) (S : Set V) (q z : ℂ) (u : S) : ℂ :=
  ∑ a : (Sᶜ : Set V), if ordinaryCutVertex g.graph S a ∧ g.graph.Adj u.val a.val then
    (g.delete S).extensionGreen q z a a / ((d : ℂ) - 1) else 0

def ordinarySelfEnergyError (g : DeficientGraph V d) (S : Set V) (q z : ℂ) (u : S) : ℂ :=
  ∑ a : (Sᶜ : Set V), if ordinaryCutVertex g.graph S a ∧ g.graph.Adj u.val a.val then
    ((g.delete S).extensionGreen q z a a - q) / ((d : ℂ) - 1) else 0

def ordinaryCutCharge (G : SimpleGraph V) (d : ℕ) (S : Set V) (u : S) : ℝ :=
  ∑ a : (Sᶜ : Set V), if ordinaryCutVertex G S a ∧ G.Adj u.val a.val then
    1 / ((d : ℝ) - 1) else 0

def ordinaryFeedbackBudget (z q : ℂ) (B : ℝ) (R : ℕ) : ℝ :=
  ((2 * R : ℕ) + 1 : ℝ) * (Real.sqrt (B + 2) * Real.sqrt (spectralScale z) *
    ‖q - semicircleRoot z‖ + 128 * ‖q - semicircleRoot z‖ ^ 2)

/-- The actual refined cavity estimate bounds every ordinary diagonal
self-energy error, weighted by its actual incident edge charge. -/
theorem ordinarySelfEnergyError_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (hzero : ∀ v ∉ S, g.deficit v = 0)
    (hG : g.graph.Connected) (hS : S.Nonempty)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (B : ℝ) (hB : ‖z‖ ≤ B)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * 3 * (3 / 2 : ℝ) * ((2 * R : ℕ) + 1 : ℝ) ≤ 1 / 2)
    (u : S) :
    ‖g.ordinarySelfEnergyError S q z u‖ ≤ ordinaryFeedbackBudget z q B R *
      ordinaryCutCharge g.graph d S u := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hk : 0 < (d : ℝ) - 1 := by linarith
  have hkNorm : ‖(d : ℂ) - 1‖ = (d : ℝ) - 1 := by
    have heq : (d : ℂ) - 1 = (((d : ℝ) - 1 : ℝ) : ℂ) := by simp
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
  unfold ordinarySelfEnergyError
  apply (norm_sum_le _ _).trans
  change (∑ a : (Sᶜ : Set V), ‖if ordinaryCutVertex g.graph S a ∧ g.graph.Adj u.val a.val then
      ((g.delete S).extensionGreen q z a a - q) / ((d : ℂ) - 1) else 0‖) ≤ _
  rw [ordinaryCutCharge, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : ordinaryCutVertex g.graph S a ∧ g.graph.Adj u.val a.val
  · let c := (outsideGraph g.graph S).connectedComponentMk a
    let e : CutBoundaryEdge g.graph S c := ⟨⟨(u.val, a.val), ha.2, u.property, a.property⟩, rfl⟩
    have hf := g.ordinary_deleted_component_feedback hd S hzero hG hS c ha.1 e z q hz hq B hB R hR small
    simp only [if_pos ha, norm_div, hkNorm, mul_one_div]
    exact div_le_div_of_nonneg_right hf hk.le
  · simp only [if_neg ha, norm_zero, mul_zero, le_refl]

omit [DecidableEq V] in
theorem ordinaryCutCharge_le_restrictionLoss (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (u : S) : ordinaryCutCharge g.graph d S u ≤ g.restrictionLoss S u := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hk : 0 < (d : ℝ) - 1 := by linarith
  let φ : {a : (Sᶜ : Set V) // g.graph.Adj u.val a.val} ≃
      {v : V // v ∉ S ∧ g.graph.Adj u.val v} :=
    { toFun := fun a => ⟨a.val.val, a.val.property, a.property⟩
      invFun := fun v => ⟨⟨v.val, v.property.1⟩, v.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard := Nat.card_congr φ
  have hcount : (∑ a : (Sᶜ : Set V), if g.graph.Adj u.val a.val then (1 : ℝ) else 0) =
      (outsideCoreNeighborCount g.graph S u : ℝ) := by
    have hi : (∑ a : (Sᶜ : Set V), if g.graph.Adj u.val a.val then (1 : ℝ) else 0) =
        (Nat.card {a : (Sᶜ : Set V) // g.graph.Adj u.val a.val} : ℝ) := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_boole]
    rw [hi, hcard]
    rfl
  have hdegree := core_neighbor_degree_partition g.graph S u
  have hdegreeR : (g.graph.degree u.val : ℝ) = ((g.graph.induce S).degree u : ℝ) +
      (outsideCoreNeighborCount g.graph S u : ℝ) := by exact_mod_cast hdegree
  calc
    ordinaryCutCharge g.graph d S u ≤
        ∑ a : (Sᶜ : Set V), if g.graph.Adj u.val a.val then 1 / ((d : ℝ) - 1) else 0 := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : g.graph.Adj u.val a.val
      · by_cases ho : ordinaryCutVertex g.graph S a <;> simp [ordinaryCutCharge, ha, ho, hk.le]
      · simp [ordinaryCutCharge, ha]
    _ = (∑ a : (Sᶜ : Set V), if g.graph.Adj u.val a.val then (1 : ℝ) else 0) / ((d : ℝ) - 1) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    _ = (outsideCoreNeighborCount g.graph S u : ℝ) / ((d : ℝ) - 1) := by rw [hcount]
    _ = g.restrictionLoss S u := by unfold restrictionLoss; rw [hdegreeR]; ring

omit [DecidableEq V] in
theorem ordinaryCutCharge_le_model_boundary (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (u : S) : ordinaryCutCharge g.graph d S u ≤ (g.restrict S).boundaryCoefficient u := by
  apply (g.ordinaryCutCharge_le_restrictionLoss hd S u).trans
  rw [g.restrict_boundaryCoefficient S u]
  have h := g.boundaryCoefficient_nonnegative hd u.val
  linarith

theorem ordinaryFeedbackBudget_nonnegative (z q : ℂ) (B : ℝ) (R : ℕ) :
    0 ≤ ordinaryFeedbackBudget z q B R := by unfold ordinaryFeedbackBudget; positivity

/-- The diagonal error is bounded by the actual boundary weight required
by the nonuniform kernel perturbation theorem. -/
theorem ordinarySelfEnergyError_model_bound (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (hzero : ∀ v ∉ S, g.deficit v = 0)
    (hG : g.graph.Connected) (hS : S.Nonempty)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (B : ℝ) (hB : ‖z‖ ≤ B)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * 3 * (3 / 2 : ℝ) * ((2 * R : ℕ) + 1 : ℝ) ≤ 1 / 2)
    (u : S) : ‖g.ordinarySelfEnergyError S q z u‖ ≤
      ordinaryFeedbackBudget z q B R * (g.restrict S).boundaryCoefficient u :=
  (g.ordinarySelfEnergyError_bound hd S hzero hG hS q z hz hq B hB R hR small u).trans
    (mul_le_mul_of_nonneg_left (g.ordinaryCutCharge_le_model_boundary hd S u)
      (ordinaryFeedbackBudget_nonnegative z q B R))

theorem ordinarySelfEnergyError_eq (g : DeficientGraph V d) (S : Set V) (q z : ℂ) (u : S) :
    g.ordinarySelfEnergyError S q z u = g.ordinarySelfEnergyDiagonal S q z u -
      q * (ordinaryCutCharge g.graph d S u : ℂ) := by
  unfold ordinarySelfEnergyError ordinarySelfEnergyDiagonal ordinaryCutCharge
  simp only [Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : ordinaryCutVertex g.graph S a ∧ g.graph.Adj u.val a.val
  · simp only [if_pos ha, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_sub,
      Complex.ofReal_natCast]
    ring
  · simp only [if_neg ha, Complex.ofReal_zero, mul_zero, sub_zero]

theorem ordinarySelfEnergyDiagonal_im_nonnegative (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (u : S) :
    0 ≤ (g.ordinarySelfEnergyDiagonal S q z u).im := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hk : 0 ≤ (d : ℝ) - 1 := by linarith
  unfold ordinarySelfEnergyDiagonal
  rw [Complex.im_sum]
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · have hkC : (d : ℂ) - 1 = (((d : ℝ) - 1 : ℝ) : ℂ) := by simp
    rw [hkC, Complex.div_ofReal_im]
    exact div_nonneg ((g.delete S).extensionGreen_diagonal_im_nonnegative hd q z hz hq a) hk
  · simp

/-- Keeping only the ordinary Schur component self-energies still gives a
genuine inverse: the total imaginary diagonal remains nonnegative. -/
theorem ordinary_self_energy_matrix_isUnit (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    IsUnit ((g.restrict S).extensionMatrix q z - Matrix.diagonal (g.ordinarySelfEnergyError S q z)) := by
  let E : S → ℂ := fun u => q * ((g.restrict S).boundaryCoefficient u : ℂ) + g.ordinarySelfEnergyError S q z u
  have hE : ∀ u, 0 ≤ (E u).im := by
    intro u
    have heq : E u = q * (((g.restrict S).boundaryCoefficient u - ordinaryCutCharge g.graph d S u : ℝ) : ℂ) +
        g.ordinarySelfEnergyDiagonal S q z u := by
      dsimp only [E]
      rw [g.ordinarySelfEnergyError_eq S q z u, Complex.ofReal_sub]
      ring
    rw [heq, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
    exact add_nonneg (mul_nonneg hq (sub_nonneg.mpr (g.ordinaryCutCharge_le_model_boundary hd S u)))
      (g.ordinarySelfEnergyDiagonal_im_nonnegative hd S q z hz hq u)
  have hunit := complex_diagonal_spectral_isUnit (g.restrict S).H
    (normalizedAdjacency_isHermitian (g.graph.induce S) d) E hE z hz
  have hid : (g.restrict S).extensionMatrix q z - Matrix.diagonal (g.ordinarySelfEnergyError S q z) =
      spectralMatrix (g.restrict S).H z - Matrix.diagonal E := by
    ext u v
    by_cases huv : u = v
    · subst v
      simp only [extensionMatrix, boundaryMatrix, boundaryDiagonal, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul, E]
      ring
    · simp only [extensionMatrix, boundaryMatrix, boundaryDiagonal, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.diagonal_apply_ne _ huv, smul_eq_mul, mul_zero, sub_zero]
  rw [hid]
  exact hunit

/-- Actual one-attachment incidence reduces the whole ordinary Schur
product to its literal deleted diagonal values. -/
theorem ordinary_cut_self_energy_diagonal (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (hG : g.graph.Connected) (hS : S.Nonempty)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (u : S) :
    (ordinaryCutCoupling g.graph d S * (g.delete S).extensionGreen q z *
      (ordinaryCutCoupling g.graph d S).transpose) u u = g.ordinarySelfEnergyDiagonal S q z u := by
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro b _
  change ((ordinaryCutCoupling g.graph d S * (g.delete S).extensionGreen q z) u b) *
    ordinaryCutCoupling g.graph d S u b = _
  by_cases hb : ordinaryCutVertex g.graph S b ∧ g.graph.Adj u.val b.val
  · have hinner : (ordinaryCutCoupling g.graph d S * (g.delete S).extensionGreen q z) u b =
        treeEdgeWeight d * (g.delete S).extensionGreen q z b b := by
      rw [Matrix.mul_apply, Finset.sum_eq_single b]
      · simp only [ordinaryCutCoupling, if_pos hb]
      · intro a _ hab
        by_cases ha : ordinaryCutVertex g.graph S a ∧ g.graph.Adj u.val a.val
        · rw [g.ordinary_deleted_cross_term_zero hd S hG hS q z hz hq u u a b ha.2 hb.2 ha.1 (Or.inr hab)]
          simp
        · simp only [ordinaryCutCoupling, if_neg ha, zero_mul]
      · intro hn
        exact False.elim (hn (Finset.mem_univ b))
    rw [hinner]
    simp only [ordinaryCutCoupling, if_pos hb]
    calc
      _ = (g.delete S).extensionGreen q z b b * treeEdgeWeight d ^ 2 := by ring
      _ = _ := by rw [treeEdgeWeight_sq d hd]; ring
  · simp only [ordinaryCutCoupling, if_neg hb, mul_zero]

theorem ordinary_cut_self_energy_eq_diagonal (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (hG : g.graph.Connected) (hS : S.Nonempty)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    ordinaryCutCoupling g.graph d S * (g.delete S).extensionGreen q z *
      (ordinaryCutCoupling g.graph d S).transpose = Matrix.diagonal (g.ordinarySelfEnergyDiagonal S q z) := by
  ext u v
  by_cases huv : u = v
  · subst v
    rw [Matrix.diagonal_apply_eq]
    exact g.ordinary_cut_self_energy_diagonal hd S hG hS q z hz hq u
  · rw [Matrix.diagonal_apply_ne _ huv]
    exact g.ordinary_cut_self_energy_offDiagonal hd S hG hS q z hz hq u v huv

end DeficientGraph
end LocalLaw
