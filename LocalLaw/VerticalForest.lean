import LocalLaw.GraphVerticalTransport

/-!
# A finite ordered forest of actual vertical spectral chains

Each branch-aware net representative has its own downward chain. The finite
product is flattened in chain order, so the ordered first-failure theorem can
use the preceding point in the same chain. The last points are exactly the
selected representatives; no continuity of the error branch is required.
-/

namespace LocalLaw

/-- Row-major indexing keeps every chain predecessor earlier in the net. -/
def flattenChain {S K : ℕ} (s : Fin S) (k : Fin (K + 1)) : Fin (S * (K + 1)) :=
  finProdFinEquiv (s, k)

@[simp] theorem flattenChain_val {S K : ℕ} (s : Fin S) (k : Fin (K + 1)) :
    (flattenChain s k).val = k.val + (K + 1) * s.val := rfl

@[simp] theorem unflattenChain_flatten {S K : ℕ} (s : Fin S) (k : Fin (K + 1)) :
    finProdFinEquiv.symm (flattenChain s k) = (s, k) :=
  finProdFinEquiv.symm_apply_apply (s, k)

/-- A node retains the target's real coordinate, with a capped vertical height. -/
def verticalForestNode {S : ℕ} (targets : Fin S → ℂ) (top h : ℝ) (K : ℕ)
    (t : Fin (S * (K + 1))) : ℂ :=
  let p := finProdFinEquiv.symm t
  verticalSpectralPoint (targets p.1).re top (targets p.1).im h p.2.val

@[simp] theorem verticalForestNode_flatten {S K : ℕ} (targets : Fin S → ℂ)
    (top h : ℝ) (s : Fin S) (k : Fin (K + 1)) :
    verticalForestNode targets top h K (flattenChain s k) =
      verticalSpectralPoint (targets s).re top (targets s).im h k.val := by
  simp only [verticalForestNode, unflattenChain_flatten]

/-- The final node is literally the target point, rather than only a nearby point. -/
theorem verticalForestNode_last {S K : ℕ} (targets : Fin S → ℂ) (top h : ℝ)
    (s : Fin S) (hcover : top - (targets s).im ≤ (K : ℝ) * h) :
    verticalForestNode targets top h K (flattenChain s (Fin.last K)) = targets s := by
  rw [verticalForestNode_flatten]
  apply Complex.ext
  · rfl
  · exact verticalHeight_last top (targets s).im h K hcover

/-- Concrete ordered transport on the flattened forest. The only event input
is the weak exterior anchor at the top of each actual chain. -/
theorem actual_vertical_forest_transport {N d a r S K : ℕ}
    {domain : Set ℂ} {radius : ℝ}
    (M : UniformGraphMesh N d a r domain radius)
    (structural : RegularGraph N d → Prop) (targets : Fin S → ℂ) (top h : ℝ)
    (hh : 0 ≤ h) (hstep : h ≤ radius)
    (inside : ∀ s k, k ≤ K → verticalSpectralPoint
      (targets s).re top (targets s).im h k ∈ domain)
    (anchor : ∀ s g, structural g → (graphLocalLawFamily N d a r).weak
      (verticalSpectralPoint (targets s).re top (targets s).im h 0) g) :
    ∀ t g, structural g →
      (∀ p, p < t → (graphLocalLawFamily N d a r).strict
        (verticalForestNode targets top h K p) g) →
      (graphLocalLawFamily N d a r).weak (verticalForestNode targets top h K t) g := by
  intro t g hg previous
  obtain ⟨⟨s, k⟩, rfl⟩ := finProdFinEquiv.surjective t
  change (graphLocalLawFamily N d a r).weak
    (verticalForestNode targets top h K (flattenChain s k)) g
  rw [verticalForestNode_flatten]
  apply actual_vertical_chain_transport M structural (targets s).re top (targets s).im h
    hh hstep (inside s) (anchor s) k g hg
  intro p hp
  have hpflat : flattenChain s p < flattenChain s k := by
    change p.val + (K + 1) * s.val < k.val + (K + 1) * s.val
    exact Nat.add_lt_add_right hp _
  simpa only [verticalForestNode_flatten] using previous (flattenChain s p) hpflat

/-- Attaching vertical chains to a branch-aware rectangular net yields an
ordered finite net and genuine continuum coverage. Its node count is explicit.
No event-transport or event-cover hypothesis is assumed. -/
theorem actual_graph_ordered_forest (N d a r : ℕ) (domain workingDomain : Set ℂ)
    (structural : RegularGraph N d → Prop) (x₀ y₀ h top : ℝ) (M V K : ℕ)
    (hh : 0 < h) (rectangle : domain ⊆ spectralRectangle x₀ y₀ h M V)
    (mesh : UniformGraphMesh N d a r workingDomain (2 * h))
    (subset : domain ⊆ workingDomain)
    (verticalInside : ∀ z ∈ domain, ∀ k ≤ K,
      verticalSpectralPoint z.re top z.im h k ∈ workingDomain)
    (verticalCover : ∀ z ∈ domain, top - z.im ≤ (K : ℝ) * h)
    (anchor : ∀ z ∈ domain, ∀ g, structural g → (graphLocalLawFamily N d a r).weak
      (verticalSpectralPoint z.re top z.im h 0) g) :
    ∃ (T : ℕ) (node : Fin T → ℂ),
      T ≤ ((M + 1) * (V + 1) * 2) * (K + 1) ∧
      (∀ t, node t ∈ workingDomain) ∧
      (∀ t g, structural g →
        (∀ p, p < t → (graphLocalLawFamily N d a r).strict (node p) g) →
        (graphLocalLawFamily N d a r).weak (node t) g) ∧
      (∀ g, structural g → (∀ t, (graphLocalLawFamily N d a r).strict (node t) g) →
        ∀ z ∈ domain, (graphLocalLawFamily N d a r).weak z g) := by
  classical
  obtain ⟨net⟩ := exists_errorBranch_rectangular_net domain (Real.log (N : ℝ))
    (graphBaseError a d N r) spectralScale x₀ y₀ h M V hh rectangle
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
  · apply actual_vertical_forest_transport mesh structural targets top h hh.le (by linarith)
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
    exact (mesh.step structural z w (subset hz) (subset (net.in_domain w hw)) branch hdist).strict_to_weak
      g hg htarget

end LocalLaw
