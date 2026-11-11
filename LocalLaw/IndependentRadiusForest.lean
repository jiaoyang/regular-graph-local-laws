import LocalLaw.IndependentRadiusMesh
import LocalLaw.BoundedVerticalForest

/-!
# Ordered continuum coverage with separate model and nominal error radii

The actual branch-aware representatives and downward chains use the nominal
error budgets and internal physical model. Every predecessor, coverage and
polynomial node-count conclusion is constructed by the same finite geometry.
-/

namespace LocalLaw
theorem actual_vertical_forest_transportWithRadii {N d a rModel rError S K : ℕ}
    {domain : Set ℂ} {radius : ℝ}
    (M : UniformGraphMesh N d a rError domain radius)
    (structural : RegularGraph N d → Prop) (targets : Fin S → ℂ) (top h : ℝ)
    (hh : 0 ≤ h) (hstep : h ≤ radius)
    (inside : ∀ s k, k ≤ K → verticalSpectralPoint
      (targets s).re top (targets s).im h k ∈ domain)
    (anchor : ∀ s g, structural g → (graphLocalLawFamilyWithRadii N d a rModel rError).weak
      (verticalSpectralPoint (targets s).re top (targets s).im h 0) g) :
    ∀ t g, structural g →
      (∀ p, p < t → (graphLocalLawFamilyWithRadii N d a rModel rError).strict
        (verticalForestNode targets top h K p) g) →
      (graphLocalLawFamilyWithRadii N d a rModel rError).weak (verticalForestNode targets top h K t) g := by
  intro t g hg previous
  obtain ⟨⟨s, k⟩, rfl⟩ := finProdFinEquiv.surjective t
  change (graphLocalLawFamilyWithRadii N d a rModel rError).weak
    (verticalForestNode targets top h K (flattenChain s k)) g
  rw [verticalForestNode_flatten]
  apply actual_vertical_chain_transportWithRadii M structural (targets s).re top (targets s).im h
    hh hstep (inside s) (anchor s) k g hg
  intro p hp
  have hpflat : flattenChain s p < flattenChain s k := by
    change p.val + (K + 1) * s.val < k.val + (K + 1) * s.val
    exact Nat.add_lt_add_right hp _
  simpa only [verticalForestNode_flatten] using previous (flattenChain s p) hpflat

/-- Attaching vertical chains to a branch-aware rectangular net yields an
ordered finite net and genuine continuum coverage. Its node count is explicit.
No event-transport or event-cover hypothesis is assumed. -/
theorem actual_graph_ordered_forestWithRadii (N d a rModel rError : ℕ) (domain workingDomain : Set ℂ)
    (structural : RegularGraph N d → Prop) (x₀ y₀ h top : ℝ) (M V K : ℕ)
    (hh : 0 < h) (rectangle : domain ⊆ spectralRectangle x₀ y₀ h M V)
    (mesh : UniformGraphMesh N d a rError workingDomain (2 * h))
    (subset : domain ⊆ workingDomain)
    (verticalInside : ∀ z ∈ domain, ∀ k ≤ K,
      verticalSpectralPoint z.re top z.im h k ∈ workingDomain)
    (verticalCover : ∀ z ∈ domain, top - z.im ≤ (K : ℝ) * h)
    (anchor : ∀ z ∈ domain, ∀ g, structural g → (graphLocalLawFamilyWithRadii N d a rModel rError).weak
      (verticalSpectralPoint z.re top z.im h 0) g) :
    ∃ (T : ℕ) (node : Fin T → ℂ),
      T ≤ ((M + 1) * (V + 1) * 2) * (K + 1) ∧
      (∀ t, node t ∈ workingDomain) ∧
      (∀ t g, structural g →
        (∀ p, p < t → (graphLocalLawFamilyWithRadii N d a rModel rError).strict (node p) g) →
        (graphLocalLawFamilyWithRadii N d a rModel rError).weak (node t) g) ∧
      (∀ g, structural g → (∀ t, (graphLocalLawFamilyWithRadii N d a rModel rError).strict (node t) g) →
        ∀ z ∈ domain, (graphLocalLawFamilyWithRadii N d a rModel rError).weak z g) := by
  classical
  obtain ⟨net⟩ := exists_errorBranch_rectangular_net domain (Real.log (N : ℝ))
    (graphBaseError a d N rError) spectralScale x₀ y₀ h M V hh rectangle
  let e := net.centers.equivFin
  let targets : Fin net.centers.card → ℂ := fun s => (e.symm s).val
  have htargets : ∀ s, targets s ∈ domain := fun s => net.in_domain _ (e.symm s).property
  refine ⟨net.centers.card * (K + 1), verticalForestNode targets top h K,
    Nat.mul_le_mul_right _ net.cardinality, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨⟨s, k⟩, rfl⟩ := finProdFinEquiv.surjective t
    change verticalForestNode targets top h K (flattenChain s k) ∈ workingDomain
    rw [verticalForestNode_flatten]
    exact verticalInside _ (htargets s) k.val (by omega)
  · apply actual_vertical_forest_transportWithRadii mesh structural targets top h hh.le (by linarith)
    · exact fun s => verticalInside _ (htargets s)
    · exact fun s => anchor _ (htargets s)
  · intro g hg hall z hz
    obtain ⟨w, hw, branch, hdist⟩ := net.cover z hz
    let s := e ⟨w, hw⟩
    have hs : targets s = w := by
      change (e.symm (e ⟨w, hw⟩)).val = w
      rw [Equiv.symm_apply_apply]
    have htarget := hall (flattenChain s (Fin.last K))
    rw [verticalForestNode_last targets top h s (verticalCover _ (htargets s)), hs] at htarget
    exact (mesh.stepWithRadii rModel structural z w (subset hz) (subset (net.in_domain w hw)) branch hdist).strict_to_weak
      g hg htarget

theorem bounded_graph_ordered_forestWithRadii (N d a b rModel rError : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (structural : RegularGraph N d → Prop)
    (mesh : UniformGraphMesh N d a rError (boundedLocalLawDomain N b (2 * B))
      (2 / (N : ℝ) ^ 12))
    (anchor : ∀ E : ℝ, |E| ≤ B → ∀ g, structural g →
      (graphLocalLawFamilyWithRadii N d a rModel rError).weak (⟨E, B⟩ : ℂ) g) :
    ∃ (T : ℕ) (node : Fin T → ℂ),
      (T : ℝ) ≤ (2 * (2 * B + 2) * (B + 2) ^ 2) * (N : ℝ) ^ 36 ∧
      (∀ t, node t ∈ boundedLocalLawDomain N b (2 * B)) ∧
      (∀ t g, structural g →
        (∀ p, p < t → (graphLocalLawFamilyWithRadii N d a rModel rError).strict (node p) g) →
        (graphLocalLawFamilyWithRadii N d a rModel rError).weak (node t) g) ∧
      (∀ g, structural g → (∀ t, (graphLocalLawFamilyWithRadii N d a rModel rError).strict (node t) g) →
        ∀ z ∈ boundedLocalLawDomain N b B, (graphLocalLawFamilyWithRadii N d a rModel rError).weak z g) := by
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
  have mesh' : UniformGraphMesh N d a rError (boundedLocalLawDomain N b (2 * B))
      (2 * (1 / (N : ℝ) ^ 12)) := by
    simpa only [mul_one_div] using mesh
  obtain ⟨T, node, hT, hnode, htransport, hcover⟩ := actual_graph_ordered_forestWithRadii N d a rModel rError
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


end LocalLaw
