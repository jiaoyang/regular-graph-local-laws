import LocalLaw.DirichletCavityLimit

/-! # Kesten--McKay reference from ordinary finite regular-tree resolvents -/

open Filter
open scoped Topology
noncomputable section
namespace LocalLaw

theorem dirichlet_regularTree_inverse_root (d : ℕ) (hd : 3≤d) (n : ℕ) (z : ℂ) (hz : 0<z.im) :
    IsUnit (regularTreeMatrix d n z 0) ∧
      (regularTreeMatrix d n z 0)⁻¹ (Sum.inl ()) (Sum.inl ())=
        kestenMcKayTransform d (cavityIterate z 0 (n+1)) z := by
  have hk : 0<d-1 := by omega
  obtain ⟨hu,hg⟩ := dirichlet_cavityTree_inverse_root (d-1) hk z hz n
  have hschur : rootSchurValue (-z)
      (branchRootCoupling d (cavityTreeRoot (d-1) n) (normalizedCavityEdge (d-1)))
      (identicalBranches d (cavityTreeMatrix (d-1) (normalizedCavityEdge (d-1)) z 0 n))=
      -z-((d:ℂ)/((d-1:ℕ):ℂ))*cavityIterate z 0 (n+1) := by
    rw [rootSchurValue,identicalBranches_self_energy d _ hu,normalizedCavityEdge_sq (d-1) hk,hg]
    ring
  have hresult := rootBlock_inverse_root (-z)
    (branchRootCoupling d (cavityTreeRoot (d-1) n) (normalizedCavityEdge (d-1)))
    (identicalBranches d (cavityTreeMatrix (d-1) (normalizedCavityEdge (d-1)) z 0 n))
    (identicalBranches_isUnit d _ hu) (by
      rw [hschur]
      exact kestenMcKay_denominator_ne_zero d _ z hz (cavityIterate_im_nonnegative z 0 hz (by norm_num) (n+1)))
  exact ⟨hresult.1,by simpa only [hschur,kestenMcKayTransform] using hresult.2⟩

theorem dirichlet_regularTree_root_tendsto (d : ℕ) (hd : 3≤d) (z : ℂ) (hz : 0<z.im) :
    Tendsto (fun n : ℕ => (regularTreeMatrix d n z 0)⁻¹ (Sum.inl ()) (Sum.inl ())) atTop
      (𝓝 (kestenMcKayTransform d (semicircleRoot z) z)) := by
  have hcavity := (cavityIterate_zero_tendsto_physical z hz).comp (tendsto_add_atTop_nat 1)
  have hcont : Continuous (fun w : ℂ => -z-((d:ℂ)/((d-1:ℕ):ℂ))*w) := by fun_prop
  have hmap : ContinuousAt (fun w : ℂ => kestenMcKayTransform d w z) (semicircleRoot z) := by
    exact hcont.continuousAt.inv₀ (kestenMcKay_denominator_ne_zero d _ z hz (semicircleRoot_im_pos hz).le)
  have h := hmap.tendsto.comp hcavity
  exact h.congr' (Filter.Eventually.of_forall (fun n => (dirichlet_regularTree_inverse_root d hd n z hz).2.symm))

end LocalLaw
