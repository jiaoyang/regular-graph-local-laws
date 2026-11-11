import LocalLaw.ActualGoodExternalComparison
import LocalLaw.SourceSurgeryCorrections

/-! Summing the physical external-tip error retains the source prime scale. -/
noncomputable section
namespace LocalLaw
local instance goodExternalColumnParametersDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceGoodExternalColumnConstant (d : ℕ) (B D U : ℝ) : ℝ :=
  let C := guardedGreenEntryCap d
  let P := sourceGreenPivotCap d B
  (1+C*P)*U+3*(1+C*P)*endpointSurgeryCouplingCap d*(C+C^2*P)*U^2+U*D^2*P

theorem good_external_column_absorption (a d : ℕ) (B D U L ε μ φ δ : ℝ)
    (ha : 2≤a) (hd : 3≤d) (hB : 0≤B) (hD : 0≤D) (hU : 0≤U)
    (hL : 1≤L) (hε : 0≤ε) (hμ : 0≤μ) (hφ : 0≤φ) (hδ : 0≤δ)
    (hsmall : ε*L^(4*a)≤1) (hcount : μ≤U*L^(2*a))
    (hphi : φ≤ε/L^(4*a)) (hdelta : δ≤D*L^3*ε) :
    μ*sourceGoodExternalBudget d B μ φ δ≤sourceGoodExternalColumnConstant d B D U*(L^3*ε) := by
  let C := guardedGreenEntryCap d
  let P := sourceGreenPivotCap d B
  let w := endpointSurgeryCouplingCap d
  have hCextra := finiteExtraReferenceConstant_ge_one d hd
  have hC : 0≤C := by dsimp only [C,guardedGreenEntryCap,commonGreenEntryCap]; linarith
  have hP : 0≤P := by dsimp only [P,sourceGreenPivotCap]; have hh:=finiteReferenceConstant_ge_one d hd; positivity
  have hw : 0≤w := by dsimp only [w,endpointSurgeryCouplingCap]; positivity
  have hLp : 0<L := by linarith
  have hφpower : L^(4*a)*φ≤ε := by
    have hh:=(le_div_iff₀ (pow_pos hLp _)).mp hphi
    simpa only [mul_comm] using hh
  have hpow : L^(2*a)≤L^(4*a) := pow_le_pow_right₀ hL (by omega)
  have hμφ : μ*φ≤U*ε := by
    calc
      _ ≤ U*L^(2*a)*φ := mul_le_mul_of_nonneg_right hcount hφ
      _ ≤ U*(L^(4*a)*φ) := by nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hφ) hU]
      _ ≤ _ := mul_le_mul_of_nonneg_left hφpower hU
  have hμsq : μ^2≤U^2*L^(4*a) := by
    have hh:=pow_le_pow_left₀ hμ hcount 2
    exact hh.trans_eq (by rw [mul_pow,←pow_mul]; congr 2; omega)
  have hμsqφ : μ^2*φ≤U^2*ε := by
    calc
      _ ≤ U^2*L^(4*a)*φ := mul_le_mul_of_nonneg_right hμsq hφ
      _ = U^2*(L^(4*a)*φ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hφpower (sq_nonneg U)
  have hsmall' : ε*L^(2*a+3)≤1 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega : 2*a+3≤4*a)) hε).trans hsmall
  have hμδ : μ*δ≤U*D := by
    calc
      _ ≤ (U*L^(2*a))*(D*L^3*ε) := mul_le_mul hcount hdelta hδ (by positivity)
      _ = U*D*(ε*L^(2*a+3)) := by rw [pow_add]; ring
      _ ≤ U*D*1 := mul_le_mul_of_nonneg_left hsmall' (mul_nonneg hU hD)
      _ = _ := mul_one _
  have hμδsq : μ*δ^2≤U*D^2*(L^3*ε) := by
    have hh:=mul_le_mul hμδ hdelta hδ (mul_nonneg hU hD)
    exact (show μ*δ^2≤(U*D)*(D*L^3*ε) by nlinarith only [hh]).trans_eq (by ring)
  have hεprime : ε≤L^3*ε := le_mul_of_one_le_left hε (one_le_pow₀ hL)
  calc
    _ = (1+C*P)*(μ*φ)+(3*(1+C*P)*w*(C+C^2*P))*(μ^2*φ)+P*(μ*δ^2) := by unfold sourceGoodExternalBudget; dsimp only [C,P,w]; ring
    _ ≤ (1+C*P)*(U*ε)+(3*(1+C*P)*w*(C+C^2*P))*(U^2*ε)+P*(U*D^2*(L^3*ε)) := by
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hμφ (by positivity))
        (mul_le_mul_of_nonneg_left hμsqφ (by positivity))) (mul_le_mul_of_nonneg_left hμδsq hP)
    _ ≤ (1+C*P)*(U*(L^3*ε))+(3*(1+C*P)*w*(C+C^2*P))*(U^2*(L^3*ε))+P*(U*D^2*(L^3*ε)) := by
      exact add_le_add_right (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hεprime hU) (by positivity))
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hεprime (sq_nonneg U)) (by positivity))) _
    _ = _ := by unfold sourceGoodExternalColumnConstant; dsimp only [C,P,w]; ring

namespace RegularGraph

theorem eventually_good_external_column_absorption (a b d : ℕ) (β B D : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hβ : 0<β) (hB : 0≤B) (hD : 0≤D) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (ell : ℕ),
      ell≤doubleLogRadius a d N → ∀ z : ℂ, 0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      let μ := (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)):ℝ)
      let ε := graphPaperError a d N (logarithmicRadius β d N) z
      let φ := correlationThreshold (Real.log (N:ℝ)) a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
      μ*sourceGoodExternalBudget d B μ φ (D*g.sourcePrime a (logarithmicRadius β d N) z)≤
        sourceGoodExternalColumnConstant d B D ((d:ℝ)*((d:ℝ)+1))*g.sourcePrime a (logarithmicRadius β d N) z := by
  filter_upwards [eventually_paperError_small a b d β ha hb hd hβ,eventually_log_ge_nat 9,Filter.eventually_ge_atTop 1]
    with N hsmall hL hN
  intro g o ell hell z hz hfloor
  dsimp only
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  have hL1 : 1≤L := by dsimp only [L]; linarith
  have hε : 0≤ε := graphPaperError_nonnegative a d N _ z hN hz.le
  have hcap : ε*L^(4*a)≤1 := (le_div_iff₀ (pow_pos (by linarith : 0<L) _)).mp
    (by simpa only [one_div] using hsmall z hz hfloor)
  have hcount:=g.boundary_card_log_bound o a ell hd hL1 hell
  have hphi:=sourceCorrelationThreshold_le_error a b d N (logarithmicRadius β d N) z ha hb (by omega) hz hL hfloor
  apply good_external_column_absorption a d B D ((d:ℝ)*((d:ℝ)+1)) L ε _ _ _ (by omega) hd hB hD (by positivity)
    hL1 hε (Nat.cast_nonneg _) (by unfold correlationThreshold; positivity) ?_ hcap hcount hphi
  · unfold sourcePrime inflatedPrime
    exact le_of_eq (by ring)
  · unfold sourcePrime inflatedPrime
    exact mul_nonneg hD (mul_nonneg (pow_nonneg (by linarith : 0≤Real.log (N:ℝ)) _) hε)

end RegularGraph
end LocalLaw
