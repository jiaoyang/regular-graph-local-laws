import SpectralConsequences.EigenvectorWard
import SpectralConsequences.SourceDiagonalCap

/-! # Graph delocalization from the checked source local law

The logarithmic choices a=12, b=300 are fixed. Every eigenvector is covered,
including unnormalized vectors. Probability is conditioned on the original
structural event; no Green bound or concentration estimate is assumed.
-/
open scoped BigOperators
open Matrix
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceTheorem14Decidable (p:Prop):Decidable p:=Classical.propDecidable p

def SourceDelocalized {N d:ℕ}(g:LocalLaw.RegularGraph N d):Prop:=
  ∀eig:ℝ,∀v:Fin N→ℂ,g.H *ᵥ v=(eig:ℂ) • v→∀i:Fin N,
    ‖v i‖^2≤sourceEigenvectorConstant d*(Real.log (N:ℝ)^300/(N:ℝ))*(∑j,‖v j‖^2)

theorem eventually_source_local_law_implies_delocalized (d:ℕ)(c β:ℝ)
    (hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32):
    ∀ᶠ N:ℕ in Filter.atTop,∀g:LocalLaw.RegularGraph N d,
      LocalLaw.RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g→
      SourceLocalLawGood g (by omega) β→SourceDelocalized g:=by
  filter_upwards [RegularGraph.eventually_source_local_law_diagonal_cap d c β hd hc hβ hβc,
    eventually_log_ge_nat 1,Filter.eventually_ge_atTop 1] with N hdiag hlog hN
  intro g hstruct hlaw eig v heig i
  let η:=Real.log (N:ℝ)^300/(N:ℝ)
  let z:ℂ:=(eig:ℂ)+(η:ℂ)*Complex.I
  have hNp:0<(N:ℝ):=Nat.cast_pos.mpr (by omega)
  have hLp:0<Real.log (N:ℝ):=by linarith
  have hη:0<η:=div_pos (pow_pos hLp _) hNp
  have hz:0<z.im:=by simpa only[z,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
    Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] using hη
  have hfloor:Real.log (N:ℝ)^300/(N:ℝ)≤z.im:=by
    simp only[z,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add]
    exact le_rfl
  have hcap:(green g.H z i i).im≤sourceEigenvectorConstant d:=
    (Complex.im_le_norm _).trans (hdiag g hstruct hlaw z hz hfloor i)
  have hh:=eigenvector_coordinate_sq_le_of_green_im_bound g.H g.H_hermitian eig η
    (sourceEigenvectorConstant d) hη v heig i hcap
  exact hh.trans_eq (by ring)

theorem source_theorem_1_4_conditional (d:ℕ)(c β:ℝ)
    (hd:3≤d)(hc:0<c)(hc1:c<1)(hβ:0<β)(hβc:β≤c/32):
    ∀D:ℕ,∀ᶠ N:ℕ in Filter.atTop,Nonempty (LocalLaw.RegularGraph N d)→
      eventMass (LocalLaw.RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        LocalLaw.RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g ∧
          ¬SourceDelocalized g)/
        eventMass (LocalLaw.RegularGraph.weight (N:=N) (d:=d))
          (LocalLaw.RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊)≤
        1/(N:ℝ)^D:=by
  intro D
  filter_upwards [source_theorem_4_2 d 12 300 c β hd (by norm_num) (by norm_num) hc hc1 hβ hβc D,
    eventually_source_local_law_implies_delocalized d c β hd hc hβ hβc]
    with N hlocal hdeloc
  intro hnonempty
  have hnum:eventMass (LocalLaw.RegularGraph.weight (N:=N) (d:=d)) (fun g=>
      LocalLaw.RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g ∧
        ¬SourceDelocalized g)≤
      eventMass (LocalLaw.RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        LocalLaw.RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g ∧
          ¬∀z:ℂ,0<z.im→Real.log (N:ℝ)^(300:ℝ)/(N:ℝ)≤z.im→
            RealSourceLocalLawAt (by omega) 12 (logarithmicRadius β d N) (sourceUniformLawConstant d) z g):=by
    apply eventMass_mono LocalLaw.RegularGraph.weight LocalLaw.RegularGraph.weight_nonnegative
    intro g hg
    refine ⟨hg.1,?_⟩
    intro hall
    apply hg.2
    apply hdeloc g hg.1
    intro z hz hfloor
    apply hall z hz
    rw [show (300:ℝ)=((300:ℕ):ℝ) by norm_num,Real.rpow_natCast]
    exact hfloor
  have hden:0≤eventMass (LocalLaw.RegularGraph.weight (N:=N) (d:=d))
      (LocalLaw.RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊):=by
    unfold eventMass
    exact Finset.sum_nonneg (fun g _=>by
      split_ifs
      · exact LocalLaw.RegularGraph.weight_nonnegative g
      · exact le_rfl)
  exact (div_le_div_of_nonneg_right hnum hden).trans (hlocal hnonempty)

end SpectralConsequences

#print axioms SpectralConsequences.source_theorem_1_4_conditional
