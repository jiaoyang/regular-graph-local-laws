import LocalLaw.BoundaryMaxBootstrap
import LocalLaw.BoundaryMaxProfile

/-! # A quadratic boundary-row remainder without a switched regularity event

The existing finite maximum bootstrap applies directly after converting an
entrywise boundary error to its actual column mass. Its conclusion controls
the unknown physical row; no physical row bound is a hypothesis.
-/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
variable {I F:Type*} [Fintype F]

/-- Raw quadratic Schur error, retaining the exact boundary count. -/
theorem boundary_entry_quadratic_remainder (R P:Matrix I I ℂ) (l:F→I)
    (D:Matrix F F ℂ) (c:ℂ) (root:I) (M δ S:ℝ)
    (hM:0≤M) (hδ:0≤δ) (hS:0≤S) (hc:‖c‖≤1)
    (hroot:∀a,‖P root (l a)‖≤M) (hD:∀a b,‖D a b‖≤δ)
    (hP:∀j,∑b,‖P (l b) j‖≤S)
    (hidentity:∀j,R root j-P root j=
      c*(∑a,∑b,P root (l a)*D a b*P (l b) j)+
      c*(∑a,∑b,(R root (l a)-P root (l a))*D a b*P (l b) j))
    (hsmall:(Fintype.card F:ℝ)*δ*S≤1/2) :
    (∀a,‖R root (l a)-P root (l a)‖≤2*M*(Fintype.card F:ℝ)*δ*S) ∧
      ∀j,‖c*(∑a,∑b,(R root (l a)-P root (l a))*D a b*P (l b) j)‖≤
        2*M*(Fintype.card F:ℝ)^2*δ^2*S^2 := by
  have hcol (b:F):(∑a,‖D a b‖)≤(Fintype.card F:ℝ)*δ:=by
    calc
      _ ≤ ∑_a:F,δ:=Finset.sum_le_sum (fun a _=>hD a b)
      _ = _:=by simp [nsmul_eq_mul]
  have hh:=boundary_row_max_and_remainder R P l D c root M
    ((Fintype.card F:ℝ)*δ) S hM (by positivity) hS hc hroot hcol hP hidentity hsmall
  constructor
  · intro a
    exact (hh.1 a).trans_eq (by ring)
  · intro j
    exact (hh.2 j).trans_eq (by ring)

/-- A supplied actual finite model profile provides every model weight and
column-mass input. The retained physical row is still derived by absorption. -/
theorem BoundaryMaxProfile.entry_quadratic_remainder (R P:Matrix I I ℂ) (l:F→I)
    (root:I) (a:ℕ) (L U M0 W0:ℝ) (profile:LocalLaw.BoundaryMaxProfile P l root a L U M0 W0)
    (D:Matrix F F ℂ) (c:ℂ) (δ:ℝ) (hδ:0≤δ) (hc:‖c‖≤1)
    (hD:∀a b,‖D a b‖≤δ)
    (hidentity:∀j,R root j-P root j=
      c*(∑a,∑b,P root (l a)*D a b*P (l b) j)+
      c*(∑a,∑b,(R root (l a)-P root (l a))*D a b*P (l b) j))
    (hsmall:(Fintype.card F:ℝ)*δ*profile.S≤1/2) :
    ∀j,‖c*(∑a,∑b,(R root (l a)-P root (l a))*D a b*P (l b) j)‖≤
      2*profile.M*(Fintype.card F:ℝ)^2*δ^2*profile.S^2 :=
  (boundary_entry_quadratic_remainder R P l D c root profile.M δ profile.S
    profile.root_nonnegative hδ profile.column_nonnegative hc profile.root_bound hD
    profile.column_bound hidentity hsmall).2

end SpectralConsequences
