import LocalLaw.GraphBranchNet

/-!
# Actual finite graph-law coverage from uniform numerical mesh bounds

The analytic estimates and branch-aware cells produce a finite continuum
cover. Inputs are numerical scale, cap, and mesh inequalities; no continuity
or final event-inclusion premise is required.
-/

namespace LocalLaw

noncomputable def localizationErrorFloor (a d N r : ℕ) : ℝ :=
  Real.log (N : ℝ) ^ (8 * a) * (((d - 1 : ℕ) : ℝ) ^ r)⁻¹

theorem graphBaseError_lower (a d N r : ℕ) (z : ℂ)
    (hlog : 0 ≤ Real.log (N : ℝ)) (hz : 0 ≤ z.im) :
    localizationErrorFloor a d N r ≤ graphBaseError a d N r z :=
  (baseError_component_bounds (Real.log (N : ℝ)) a d N r z.im _ hlog hz).1

theorem graphPaperError_lower (a d N r : ℕ) (z : ℂ)
    (hlog : 1 ≤ Real.log (N : ℝ)) (hz : 0 ≤ z.im) :
    localizationErrorFloor a d N r ≤ graphPaperError a d N r z := by
  have he0 : 0 ≤ graphBaseError a d N r z :=
    baseError_nonnegative _ a d N r z.im _ (by linarith) hz
  exact (graphBaseError_lower a d N r z (by linarith) hz).trans
    (inflateError_bounds (s := spectralScale z) hlog he0).1

theorem baseErrorModulus_mono (a N : ℕ) (η x y : ℝ)
    (hη : 0 < η) (hlog : 0 ≤ Real.log (N : ℝ)) (hxy : x ≤ y) :
    baseErrorModulus a N η x ≤ baseErrorModulus a N η y := by
  unfold baseErrorModulus
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hlog _)
  apply add_le_add
  · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hxy (by positivity))
  · exact mul_le_mul_of_nonneg_left hxy (by positivity)

/-- Uniform finite numerical conditions sufficient for source-specific
same-branch transport. Large-N asymptotics are a separate proof obligation. -/
structure UniformGraphMesh (N d a r : ℕ) (domain : Set ℂ) (radius : ℝ) where
  vertexPositive : 0 < N
  degreeAtLeastThree : 3 ≤ d
  logLarge : 1 ≤ Real.log (N : ℝ)
  etaFloor : ℝ
  etaPositive : 0 < etaFloor
  lowerImaginary : ∀ z ∈ domain, etaFloor ≤ z.im
  cap : ℝ
  capPositive : 0 < cap
  totalCap : ∀ z ∈ domain, spectralScale z + graphPaperError a d N r z ≤ cap
  baseMesh : baseErrorModulus a N etaFloor radius ≤ localizationErrorFloor a d N r / 8
  scaleMesh : 2 * radius ≤ etaFloor / 8
  cavityMesh : (1 / etaFloor ^ 2 + 1 / etaFloor) * radius ≤
    (localizationErrorFloor a d N r / Real.sqrt cap) / 4
  entryMesh : (1 / etaFloor ^ 2 + ((1 + 2 / etaFloor ^ 2) / etaFloor ^ 2)) * radius ≤
    localizationErrorFloor a d N r / 4

namespace UniformGraphMesh

variable {N d a r : ℕ} {domain : Set ℂ} {radius : ℝ}

theorem scale_budget_lower (M : UniformGraphMesh N d a r domain radius) (z : ℂ) (hz : z ∈ domain) :
    localizationErrorFloor a d N r / Real.sqrt M.cap ≤
      scalarScale (spectralScale z) (graphPaperError a d N r z) := by
  have hzp : 0 < z.im := M.etaPositive.trans_le (M.lowerImaginary z hz)
  have hεp : 0 ≤ graphPaperError a d N r z :=
    graphPaperError_nonnegative a d N r z (Nat.succ_le_of_lt M.vertexPositive) hzp.le
  have hroot : 0 < Real.sqrt (spectralScale z + graphPaperError a d N r z) :=
    Real.sqrt_pos.mpr (by linarith [spectralScale_pos hzp])
  exact div_le_div₀ hεp (graphPaperError_lower a d N r z M.logLarge hzp.le)
    hroot (Real.sqrt_le_sqrt (M.totalCap z hz))

noncomputable def step (M : UniformGraphMesh N d a r domain radius)
    (structural : RegularGraph N d → Prop) (z w : ℂ) (hz : z ∈ domain) (hw : w ∈ domain)
    (branch : graphErrorBranch a d N r w = graphErrorBranch a d N r z)
    (hdist : dist z w ≤ radius) :
    LocalLawTransportStep (graphLocalLawFamily N d a r) structural w z := by
  have hEta := M.etaPositive
  have hzp := M.etaPositive.trans_le (M.lowerImaginary z hz)
  have hεlower := graphPaperError_lower a d N r z M.logLarge hzp.le
  have hbaselower := graphBaseError_lower a d N r z (by linarith [M.logLarge]) hzp.le
  have hslower : M.etaFloor ≤ spectralScale z := by
    unfold spectralScale
    linarith [edgeDistance_nonneg z, M.lowerImaginary z hz]
  apply graphSameBranchStep N d a r M.vertexPositive M.degreeAtLeastThree structural z w
    M.etaFloor M.etaPositive (M.lowerImaginary z hz) (M.lowerImaginary w hw) M.logLarge branch
  · exact (baseErrorModulus_mono a N M.etaFloor _ _ M.etaPositive
      (by linarith [M.logLarge]) hdist).trans (M.baseMesh.trans (by linarith))
  · linarith [M.scaleMesh]
  · have hC : 0 ≤ 1 / M.etaFloor ^ 2 + 1 / M.etaFloor := by positivity
    have hmul := mul_le_mul_of_nonneg_left hdist hC
    exact hmul.trans (M.cavityMesh.trans (by linarith [M.scale_budget_lower z hz]))
  · have hC : 0 ≤ 1 / M.etaFloor ^ 2 + ((1 + 2 / M.etaFloor ^ 2) / M.etaFloor ^ 2) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hdist hC
    exact hmul.trans (M.entryMesh.trans (by linarith))

end UniformGraphMesh

/-- An actual finite continuum-cover theorem, including the explicit bound
on representative count. Its hypothesis is only a numerical mesh budget. -/
theorem actual_graph_finite_branch_cover (N d a r : ℕ) (domain : Set ℂ)
    (structural : RegularGraph N d → Prop) (x₀ y₀ h : ℝ) (M K : ℕ) (hh : 0 < h)
    (rectangle : domain ⊆ spectralRectangle x₀ y₀ h M K)
    (mesh : UniformGraphMesh N d a r domain (2 * h)) :
    ∃ centers : Finset ℂ, (∀ w ∈ centers, w ∈ domain) ∧
      centers.card ≤ (M + 1) * (K + 1) * 2 ∧
      ∀ g, structural g → (∀ w ∈ centers, (graphLocalLawFamily N d a r).strict w g) →
        ∀ z ∈ domain, (graphLocalLawFamily N d a r).weak z g := by
  obtain ⟨net⟩ := exists_errorBranch_rectangular_net domain (Real.log (N : ℝ))
    (graphBaseError a d N r) spectralScale x₀ y₀ h M K hh rectangle
  refine ⟨net.centers, net.in_domain, net.cardinality, ?_⟩
  apply branchNet_uniform_cover (graphLocalLawFamily N d a r) structural domain
    (fun z => graphErrorBranch a d N r z) (2 * h) ((M + 1) * (K + 1) * 2) net
  intro z hz w hw branch hdist
  exact ⟨mesh.step structural z w hz (net.in_domain w hw) branch hdist⟩

end LocalLaw
