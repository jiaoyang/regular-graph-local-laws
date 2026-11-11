import LocalLaw.VerticalForest
import LocalLaw.EventualGraphMesh

/-!
# A polynomial-size bootstrap forest on the actual bounded domain

The working disk has twice the target radius. Vertical chains start at the
fixed height B and end exactly at every branch-aware representative. All
geometry, transport, continuum coverage, and the O(N^36) node count are proved.
The source exterior weak anchor is an explicit input to this bootstrap
interface and is proved in `ExteriorStrictAnchorEffective`.
-/

namespace LocalLaw

noncomputable def spectralGridCount (N : ℕ) (B : ℝ) : ℕ :=
  ⌈B * (N : ℝ) ^ 12⌉₊

theorem spectralGridCount_covers (N : ℕ) (B : ℝ) (hN : 0 < N) :
    B ≤ (spectralGridCount N B : ℝ) * (1 / (N : ℝ) ^ 12) := by
  have hn : (0 : ℝ) < (N : ℝ) ^ 12 := pow_pos (Nat.cast_pos.mpr hN) _
  have h := Nat.le_ceil (B * (N : ℝ) ^ 12)
  simpa only [spectralGridCount, mul_one_div] using (le_div_iff₀ hn).mpr h

theorem spectralGridCount_bound (N : ℕ) (B : ℝ) (hN : 1 ≤ N) (hB : 0 ≤ B) :
    ((spectralGridCount N B + 1 : ℕ) : ℝ) ≤ (B + 2) * (N : ℝ) ^ 12 := by
  have hn : (1 : ℝ) ≤ (N : ℝ) ^ 12 := one_le_pow₀ (by exact_mod_cast hN)
  have h := Nat.ceil_lt_add_one (show 0 ≤ B * (N : ℝ) ^ 12 by positivity)
  rw [Nat.cast_add, Nat.cast_one]
  dsimp [spectralGridCount] at *
  nlinarith

theorem verticalHeight_upper (top bottom h : ℝ) (k : ℕ)
    (horder : bottom ≤ top) (hh : 0 ≤ h) : verticalHeight top bottom h k ≤ top := by
  apply max_le horder
  have hp : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh
  linarith

/-- A numerical mesh gives an actual ordered net on the bounded source domain,
with no supplied transport, branch-continuity, or event-cover hypotheses. -/
theorem bounded_graph_ordered_forest (N d a b r : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (structural : RegularGraph N d → Prop)
    (mesh : UniformGraphMesh N d a r (boundedLocalLawDomain N b (2 * B))
      (2 / (N : ℝ) ^ 12))
    (anchor : ∀ E : ℝ, |E| ≤ B → ∀ g, structural g →
      (graphLocalLawFamily N d a r).weak (⟨E, B⟩ : ℂ) g) :
    ∃ (T : ℕ) (node : Fin T → ℂ),
      (T : ℝ) ≤ (2 * (2 * B + 2) * (B + 2) ^ 2) * (N : ℝ) ^ 36 ∧
      (∀ t, node t ∈ boundedLocalLawDomain N b (2 * B)) ∧
      (∀ t g, structural g →
        (∀ p, p < t → (graphLocalLawFamily N d a r).strict (node p) g) →
        (graphLocalLawFamily N d a r).weak (node t) g) ∧
      (∀ g, structural g → (∀ t, (graphLocalLawFamily N d a r).strict (node t) g) →
        ∀ z ∈ boundedLocalLawDomain N b B, (graphLocalLawFamily N d a r).weak z g) := by
  have hN := mesh.vertexPositive
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hh : 0 < 1 / (N : ℝ) ^ 12 := by positivity
  have hheight : 0 < Real.log (N : ℝ) ^ b / (N : ℝ) := by
    exact div_pos (pow_pos (by linarith [mesh.logLarge]) _) hn
  have hpoint : ∀ z ∈ boundedLocalLawDomain N b B,
      |z.re| ≤ B ∧ 0 ≤ z.im ∧ z.im ≤ B := by
    intro z hz
    exact ⟨(Complex.abs_re_le_norm z).trans hz.1,
      (hheight.trans_le hz.2).le, (Complex.im_le_norm z).trans hz.1⟩
  have rectangle : boundedLocalLawDomain N b B ⊆ spectralRectangle (-B) 0
      (1 / (N : ℝ) ^ 12) (spectralGridCount N (2 * B)) (spectralGridCount N B) := by
    intro z hz
    obtain ⟨hre, hη, hηB⟩ := hpoint z hz
    have hx := spectralGridCount_covers N (2 * B) hN
    have hy := spectralGridCount_covers N B hN
    exact ⟨⟨(abs_le.mp hre).1, by linarith [(abs_le.mp hre).2]⟩,
      ⟨hη, by linarith⟩⟩
  have subset : boundedLocalLawDomain N b B ⊆ boundedLocalLawDomain N b (2 * B) := by
    intro z hz
    exact ⟨hz.1.trans (by linarith), hz.2⟩
  have inside : ∀ z ∈ boundedLocalLawDomain N b B, ∀ k ≤ spectralGridCount N B,
      verticalSpectralPoint z.re B z.im (1 / (N : ℝ) ^ 12) k ∈
        boundedLocalLawDomain N b (2 * B) := by
    intro z hz k _
    obtain ⟨hre, hη, hηB⟩ := hpoint z hz
    have hlo := verticalHeight_lower B z.im (1 / (N : ℝ) ^ 12) k
    have hup := verticalHeight_upper B z.im (1 / (N : ℝ) ^ 12) k hηB hh.le
    have hnonneg : 0 ≤ verticalHeight B z.im (1 / (N : ℝ) ^ 12) k := hη.trans hlo
    constructor
    · have hnorm := Complex.norm_le_abs_re_add_abs_im
        (verticalSpectralPoint z.re B z.im (1 / (N : ℝ) ^ 12) k)
      simp only [verticalSpectralPoint, abs_of_nonneg hnonneg] at hnorm
      change ‖(⟨z.re, verticalHeight B z.im (1 / (N : ℝ) ^ 12) k⟩ : ℂ)‖ ≤ 2 * B
      linarith
    · exact hz.2.trans hlo
  have mesh' : UniformGraphMesh N d a r (boundedLocalLawDomain N b (2 * B))
      (2 * (1 / (N : ℝ) ^ 12)) := by
    simpa only [mul_one_div] using mesh
  obtain ⟨T, node, hT, hnode, htransport, hcover⟩ := actual_graph_ordered_forest N d a r
    (boundedLocalLawDomain N b B) (boundedLocalLawDomain N b (2 * B)) structural
    (-B) 0 (1 / (N : ℝ) ^ 12) B (spectralGridCount N (2 * B)) (spectralGridCount N B)
    (spectralGridCount N B) hh rectangle mesh' subset inside
    (by intro z hz; linarith [(hpoint z hz).2.1, spectralGridCount_covers N B hN])
    (by
      intro z hz g hg
      have heq : verticalSpectralPoint z.re B z.im (1 / (N : ℝ) ^ 12) 0 = (⟨z.re, B⟩ : ℂ) := by
        apply Complex.ext
        · rfl
        · exact verticalHeight_zero B z.im _ (hpoint z hz).2.2
      rw [heq]
      exact anchor z.re (hpoint z hz).1 g hg)
  refine ⟨T, node, ?_, hnode, htransport, hcover⟩
  have hTc : (T : ℝ) ≤
      (((spectralGridCount N (2 * B) + 1 : ℕ) : ℝ) *
        ((spectralGridCount N B + 1 : ℕ) : ℝ) * 2) *
        ((spectralGridCount N B + 1 : ℕ) : ℝ) := by exact_mod_cast hT
  have hx := spectralGridCount_bound N (2 * B) (by omega) (by positivity)
  have hy := spectralGridCount_bound N B (by omega) hB
  calc
    (T : ℝ) ≤ _ := hTc
    _ ≤ (((2 * B + 2) * (N : ℝ) ^ 12) * ((B + 2) * (N : ℝ) ^ 12) * 2) *
        ((B + 2) * (N : ℝ) ^ 12) := by
      gcongr
    _ = (2 * (2 * B + 2) * (B + 2) ^ 2) * (N : ℝ) ^ 36 := by ring

/-- The actual logarithmic source parameters eventually provide all mesh and
finite-net inputs; only the independent exterior-anchor theorem is requested. -/
theorem eventually_bounded_graph_ordered_forest (a b d : ℕ) (β B : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d)
    (hβ : 0 < β) (hβ₁ : β ≤ 1) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ (structural : RegularGraph N d → Prop),
      (∀ E : ℝ, |E| ≤ B → ∀ g, structural g →
        (graphLocalLawFamily N d a (logarithmicRadius β d N)).weak (⟨E, B⟩ : ℂ) g) →
      ∃ (T : ℕ) (node : Fin T → ℂ),
        (T : ℝ) ≤ (2 * (2 * B + 2) * (B + 2) ^ 2) * (N : ℝ) ^ 36 ∧
        (∀ t, node t ∈ boundedLocalLawDomain N b (2 * B)) ∧
        (∀ t g, structural g →
          (∀ p, p < t → (graphLocalLawFamily N d a (logarithmicRadius β d N)).strict (node p) g) →
          (graphLocalLawFamily N d a (logarithmicRadius β d N)).weak (node t) g) ∧
        (∀ g, structural g →
          (∀ t, (graphLocalLawFamily N d a (logarithmicRadius β d N)).strict (node t) g) →
          ∀ z ∈ boundedLocalLawDomain N b B,
            (graphLocalLawFamily N d a (logarithmicRadius β d N)).weak z g) := by
  filter_upwards [eventually_polynomial_graph_mesh a b d β (2 * B) ha hb hd hβ hβ₁
    (by positivity)] with N hmesh
  intro structural anchor
  exact bounded_graph_ordered_forest N d a b (logarithmicRadius β d N) B hB structural
    (Classical.choice hmesh) anchor

end LocalLaw
