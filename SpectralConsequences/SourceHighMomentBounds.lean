import SpectralConsequences.SourceMomentEvents
import SpectralConsequences.SourceMomentObservables
import SpectralConsequences.SourceWardVarianceBound
import SpectralConsequences.FiniteMomentIdentity

/-! An explicit target family for the actual Section7 moment proof.
The family is proved in the source recurrence modules; it is not an axiom. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceHighMomentBoundsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceHighMomentScale (a d N:ℕ)(β B:ℝ)(z:ℂ):ℝ:=
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  ε^2+Real.sqrt (ε*sourceMomentVariance a d N (logarithmicRadius β d N)
    (sourceWardVarianceConstant d B) z)

def SourceHighMomentBounds (a b d:ℕ)(c β B:ℝ):Prop:=
  ∀p:ℕ,2≤p→∃C:ℝ,1≤C ∧∃q:ℕ,
    ∀ᶠ N:ℕ in Filter.atTop,∀z:ℂ,0<z.im→‖z‖≤B→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→
      ∀cavity:Bool,truncatedMoment (RegularGraph.weight (N:=N) (d:=d))
        (momentSourceEvent N d a c β z)
        (fun g=>momentResidual cavity g (actualCavityDepth a d N z-1) z) p≤
          (C*Real.log (N:ℝ)^q*sourceHighMomentScale a d N β B z)^(2*p)

theorem sourceHighMomentScale_nonnegative (a d N:ℕ)(β B:ℝ)(z:ℂ):
    0≤sourceHighMomentScale a d N β B z:=by unfold sourceHighMomentScale;positivity

end SpectralConsequences
