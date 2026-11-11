import SpectralConsequences.ExteriorSourceParameters
import SpectralConsequences.ExteriorMesh
import SpectralConsequences.SourceCorrectedTrace
import SpectralConsequences.SourceRigidityAssembly

/-! # The literal corrected-trace grid gives the source confinement event

This deterministic grid implication takes a pointwise corrected-trace
estimate as an explicit hypothesis. `SourceExteriorResidualBound` derives
that estimate from physical residual bounds, whose tails are proved by
`SourceActualHighMoments` and `SourceMomentTailBridge`. Grid coverage,
positivity, the single removed mode and the reference imaginary-part
contribution are all derived here.
-/
open Set
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceExteriorConfinementDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceSpectralBox (d:ℕ):ℝ:=max 2 (regularSpectralRadius d)
def sourceExteriorMesh (d N:ℕ) (β:ℝ):Finset ℝ:=
  exteriorMesh (N^2) (sourceSpectralBox d) (edgeWindow β N) (exteriorHeight β N)

theorem sourceExteriorMesh_card_le (d N:ℕ) (β:ℝ) (hN:3≤N):
    (sourceExteriorMesh d N β).card≤N^3:=exteriorMesh_card_le_cube N hN _ _ _

theorem sourceExteriorMesh_spectral_bounds (a b:ℝ) (d N:ℕ) (β:ℝ)
    (num:ExteriorSourceParameters a b d N β (sourceSpectralBox d)) (E:ℝ)
    (hE:E∈sourceExteriorMesh d N β):
    let z:ℂ:=(E:ℂ)+(exteriorHeight β N:ℂ)*Complex.I
    0<z.im ∧ Real.log (N:ℝ)^b/(N:ℝ)≤z.im ∧ ‖z‖≤sourceSpectralBox d+2 ∧
      edgeWindow β N/2≤spectralScale z := by
  dsimp only
  have he:=exteriorMesh_energy_bounds (N^2) (sourceSpectralBox d) (edgeWindow β N)
    (exteriorHeight β N) E hE
  refine ⟨by simpa using num.height_positive,by simpa using num.height_floor,?_,?_⟩
  · calc
      _≤‖(E:ℂ)‖+‖(exteriorHeight β N:ℂ)*Complex.I‖:=norm_add_le _ _
      _=|E|+exteriorHeight β N:=by simp only[norm_mul,Complex.norm_real,Real.norm_eq_abs,
        Complex.norm_I,mul_one,abs_of_pos num.height_positive]
      _≤_:=by linarith only[he.1,num.height_one]
  · exact spectralScale_exterior_lower E (exteriorHeight β N) (edgeWindow β N) num.height_positive.le he.2

theorem source_confinement_of_scaled_corrected_trace (a b:ℝ) {d N:ℕ} (β:ℝ)
    (g:RegularGraph N d) (num:ExteriorSourceParameters a b d N β (sourceSpectralBox d))
    (htrace:∀E∈sourceExteriorMesh d N β,
      ((N:ℝ)*exteriorHeight β N)*
        ‖RegularGraph.correctedSourceTrace g ((E:ℂ)+(exteriorHeight β N:ℂ)*Complex.I)-
          kestenMcKayStieltjes d ((E:ℂ)+(exteriorHeight β N:ℂ)*Complex.I)‖≤1/16):
    SourceConfinementGood β g := by
  let M:=sourceSpectralBox d
  let η:=exteriorHeight β N
  let Δ:=edgeWindow β N
  let values:=sortedEigenvalues g.H_hermitian
  let i0:Fin N:=⟨0,num.size_positive⟩
  have hNp:0<(N:ℝ):=Nat.cast_pos.mpr num.size_positive
  have hscale:0<(N:ℝ)*η:=mul_pos hNp num.height_positive
  have hbox:∀i,-M≤values i ∧ values i≤M:=by
    intro i
    exact abs_le.mp ((RegularGraph.sorted_eigenvalues_box g i).trans (le_max_right _ _))
  have hcover:∀x,(-M≤x∧x< -2-Δ)∨(2+Δ<x∧x≤M)→
      ∃E∈sourceExteriorMesh d N β,|x-E|≤η:=by
    intro x hx
    have hM:2≤M:=le_max_left _ _
    have hxbox:|x|≤M:=by
      rcases hx with hx|hx
      · apply abs_le.mpr
        exact ⟨hx.1,by linarith [num.window_positive]⟩
      · apply abs_le.mpr
        exact ⟨by linarith [num.window_positive],hx.2⟩
    have hout:2+Δ < |x|:=by
      rcases hx with hx|hx
      · rw [abs_of_neg (by linarith [num.window_positive]:x<0)]
        linarith only[hx.2]
      · exact hx.1.trans_le (le_abs_self _)
    exact exteriorMesh_cover (N^2) M Δ η num.height_positive num.mesh_margin num.mesh_width x hxbox hout
  have hpositive:∀E∈sourceExteriorMesh d N β,
      (correctedFiniteStieltjes values {i0} ((E:ℂ)+(η:ℂ)*Complex.I)).im<1/(2*(N:ℝ)*η):=by
    intro E hE
    let z:ℂ:=(E:ℂ)+(η:ℂ)*Complex.I
    have hz:0<z.im:=by simpa [z,η] using num.height_positive
    have he:=exteriorMesh_energy_bounds (N^2) M Δ η E hE
    have href:=num.reference_trace_small E he.2
    have hdiff:=htrace E hE
    have hi:=Complex.im_le_norm (RegularGraph.correctedSourceTrace g z-kestenMcKayStieltjes d z)
    simp only[Complex.sub_im] at hi
    have him:((N:ℝ)*η)*(RegularGraph.correctedSourceTrace g z).im≤1/8:=by
      have hh:=mul_le_mul_of_nonneg_left hi hscale.le
      nlinarith only[hh,href,hdiff]
    rw [←RegularGraph.correctedSourceTrace_eq_positive_sum g num.size_positive z hz]
    apply (lt_div_iff₀ (show 0<2*(N:ℝ)*η by nlinarith only[hscale])).mpr
    have hh:2*(((N:ℝ)*η)*(RegularGraph.correctedSourceTrace g z).im)≤1/4:=by linarith only[him]
    nlinarith only[hh]
  have hconf:=finite_grid_confinement values {i0} num.size_positive M (-2) 2 Δ η num.height_positive
    (sourceExteriorMesh d N β) hbox hcover hpositive
  intro i hi
  exact hconf i (by simp only[Finset.mem_singleton];intro hh;exact hi (congrArg Fin.val hh))

end SpectralConsequences
