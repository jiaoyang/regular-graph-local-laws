import LocalLaw.Theorem42
import LocalLaw.LocalStrongClosure

/-! # Averaged local certificate closure with quadratic-log row feedback -/

open scoped BigOperators
namespace LocalLaw

structure StrongClosureBudget (z m : ℂ) (s ε : ℝ) where
  depth : ℕ
  L : ℝ
  gapConstant : ℝ
  spectralRadius : ℝ
  U : ℝ
  V : ℝ
  residualConstant : ℝ
  rowBase : ℝ
  rowFeedback : ℝ
  cavityError : ℝ
  exceptionalCavity : ℝ
  root : m^2+z*m+1=0
  rootNorm : ‖m‖≤1
  spectralBound : ‖z‖≤spectralRadius
  small : (depth:ℝ)*scalarScale s ε≤1/2
  nonresonant : 1/2≤‖cavitySum m depth‖
  scalePositive : 0<s
  errorPositive : 0<ε
  gapNonnegative : 0≤gapConstant
  UNonnegative : 0≤U
  VNonnegative : 0≤V
  residualNonnegative : 0≤residualConstant
  large : 2≤L
  gapLower : Real.sqrt s≤‖m⁻¹-m‖
  gapUpper : ‖m⁻¹-m‖≤gapConstant*Real.sqrt s
  regime : ε≤s/L ∨ L^3*s≤ε
  cavityErrorNonnegative : 0≤cavityError
  rowBaseBound : rowBase≤U*ε/L
  rowFeedbackBound : rowFeedback≤V*L^2
  scalarLarge : 2*strongLocalNormConstant spectralRadius gapConstant residualConstant≤L
  rowLarge : 2*(U+V*strongLocalFeedbackConstant spectralRadius gapConstant residualConstant)≤L

namespace StrongClosureBudget

/-- Reuse proved physical/spectral/depth data while replacing only the
quantitative analytic budgets. -/
noncomputable def ofClosureBudget {z m : ℂ} {s ε : ℝ} (D : ClosureBudget z m s ε)
    (U V M0 rowBase rowFeedback cavityError : ℝ)
    (hU : 0≤U) (hV : 0≤V) (hM : 0≤M0) (ht : 0≤cavityError)
    (hu : rowBase≤U*ε/D.L) (hv : rowFeedback≤V*D.L^2)
    (hscalar : 2*strongLocalNormConstant D.spectralRadius D.gapConstant M0≤D.L)
    (hrow : 2*(U+V*strongLocalFeedbackConstant D.spectralRadius D.gapConstant M0)≤D.L) :
    StrongClosureBudget z m s ε where
  depth := D.depth
  L := D.L
  gapConstant := D.gapConstant
  spectralRadius := D.spectralRadius
  U := U
  V := V
  residualConstant := M0
  rowBase := rowBase
  rowFeedback := rowFeedback
  cavityError := cavityError
  exceptionalCavity := D.exceptionalCavity
  root := D.root
  rootNorm := D.rootNorm
  spectralBound := D.spectralBound
  small := D.small
  nonresonant := D.nonresonant
  scalePositive := D.scalePositive
  errorPositive := D.errorPositive
  gapNonnegative := D.gapNonnegative
  UNonnegative := hU
  VNonnegative := hV
  residualNonnegative := hM
  large := D.large
  gapLower := D.gapLower
  gapUpper := D.gapUpper
  regime := D.regime
  cavityErrorNonnegative := ht
  rowBaseBound := hu
  rowFeedbackBound := hv
  scalarLarge := hscalar
  rowLarge := hrow

/-- The physical root and actual spectral gap are proved by existing scalar
algebra; only concrete finite-scale bounds remain constructor arguments. -/
noncomputable def ofSemicircle (z : ℂ) (ε : ℝ) (depth : ℕ)
    (L B U V M0 rowBase rowFeedback cavityError exceptional : ℝ)
    (hz : 0<z.im) (hB : ‖z‖≤B)
    (hsmall : (depth:ℝ)*scalarScale (spectralScale z) ε≤1/2)
    (hnonresonant : 1/2≤‖cavitySum (semicircleRoot z) depth‖)
    (hε : 0<ε) (hU : 0≤U) (hV : 0≤V) (hM : 0≤M0) (hL : 2≤L)
    (hregime : ε≤spectralScale z/L ∨ L^3*spectralScale z≤ε)
    (ht : 0≤cavityError) (hu : rowBase≤U*ε/L) (hv : rowFeedback≤V*L^2)
    (hscalar : 2*strongLocalNormConstant B (Real.sqrt (B+2)) M0≤L)
    (hrow : 2*(U+V*strongLocalFeedbackConstant B (Real.sqrt (B+2)) M0)≤L) :
    StrongClosureBudget z (semicircleRoot z) (spectralScale z) ε where
  depth := depth
  L := L
  gapConstant := Real.sqrt (B+2)
  spectralRadius := B
  U := U
  V := V
  residualConstant := M0
  rowBase := rowBase
  rowFeedback := rowFeedback
  cavityError := cavityError
  exceptionalCavity := exceptional
  root := semicircleRoot_equation z
  rootNorm := semicircleRoot_norm_le_one z
  spectralBound := hB
  small := hsmall
  nonresonant := hnonresonant
  scalePositive := spectralScale_pos hz
  errorPositive := hε
  gapNonnegative := Real.sqrt_nonneg _
  UNonnegative := hU
  VNonnegative := hV
  residualNonnegative := hM
  large := hL
  gapLower := (cavity_root_gap_bounds (semicircleRoot_equation z) hz hB).1
  gapUpper := (cavity_root_gap_bounds (semicircleRoot_equation z) hz hB).2
  regime := hregime
  cavityErrorNonnegative := ht
  rowBaseBound := hu
  rowFeedbackBound := hv
  scalarLarge := hscalar
  rowLarge := hrow

end StrongClosureBudget

section ActualEvents
variable {V : Type*} [Fintype V] [DecidableEq V]

def StrongCavityRowCertificate (q m z : ℂ) (s ε : ℝ)
    (D : StrongClosureBudget z m s ε) (G : V → V → ℂ) (P : ℂ → V → V → ℂ)
    (cavity : V → ℂ) (bad : Finset V) (i : V) : Prop :=
  (i∉bad → ‖cavity i-cavityIterate z q D.depth‖≤D.cavityError) ∧
    ∀ j,‖G i j-P q i j‖≤D.rowBase+D.rowFeedback*(Real.sqrt s*‖q-m‖+‖q-m‖^2)

theorem actual_strong_local_certificate_closure
    (q m z : ℂ) (s ε : ℝ) (D : StrongClosureBudget z m s ε)
    (G : V → V → ℂ) (P : ℂ → V → V → ℂ) (cavity : V → ℂ) (bad : Finset V)
    (hcard : 0<Fintype.card V) (average : q=(Fintype.card V:ℝ)⁻¹ • ∑ i,cavity i)
    (exceptional : ∀ i∈bad,‖cavity i-cavityIterate z q D.depth‖≤D.exceptionalCavity)
    (absorption : D.cavityError+((bad.card:ℝ)/(Fintype.card V:ℝ))*D.exceptionalCavity≤D.residualConstant*ε/D.L^4)
    (weak : WeakLocalLawAt q m s ε G P)
    (certificates : ∀ i,StrongCavityRowCertificate q m z s ε D G P cavity bad i) :
    StrictLocalLawAt q m s ε G P := by
  have hsmall : (D.depth:ℝ)*‖q-m‖≤1/2 :=
    (mul_le_mul_of_nonneg_left weak.1 (Nat.cast_nonneg _)).trans D.small
  have hresidual : ‖q-cavityIterate z q D.depth‖≤D.residualConstant*ε/D.L^4 :=
    (averaged_cavity_residual cavity q (cavityIterate z q D.depth) bad D.cavityError D.exceptionalCavity
      hcard D.cavityErrorNonnegative average (fun i hi => (certificates i).1 hi) exceptional).trans absorption
  have result := local_certificate_strong_closure q m z D.depth s ε D.L 1 D.gapConstant D.spectralRadius
    D.residualConstant D.U D.V D.rowBase D.rowFeedback
    (fun ij : V×V => ‖G ij.1 ij.2-P q ij.1 ij.2‖)
    D.root D.rootNorm D.spectralBound hsmall D.nonresonant D.scalePositive D.errorPositive (by norm_num)
    D.gapNonnegative D.residualNonnegative D.VNonnegative D.large (by simpa using D.large)
    D.gapLower D.gapUpper (by simpa using weak.1) hresidual D.regime (fun ij => (certificates ij.1).2 ij.2)
    D.rowBaseBound D.rowFeedbackBound D.scalarLarge D.rowLarge
  exact ⟨result.1,fun i j => result.2 (i,j)⟩

end ActualEvents
end LocalLaw
