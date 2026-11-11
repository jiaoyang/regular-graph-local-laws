import SpectralConsequences.ExchangeableFinite

/-! Separate geometric exits from the remaining weak-event failure. -/
noncomputable section
namespace SpectralConsequences

theorem exit_integrand_partition (A B G W:Prop) [Decidable A] [Decidable B] [Decidable G] [Decidable W]
    (hcover:¬B↔G∨W) (v:ℂ):
    (if A∧¬B then v else 0)=(if A∧G then v else 0)+(if A∧¬G∧W then v else 0):=by
  by_cases ha:A
  · by_cases hg:G
    · have hb:¬B:=hcover.mpr (Or.inl hg)
      simp [ha,hg,hb]
    · by_cases hw:W
      · have hb:¬B:=hcover.mpr (Or.inr hw)
        simp [ha,hg,hw,hb]
      · have hb:B:=by
          by_contra hn
          exact (hcover.mp hn).elim hg hw
        simp [ha,hg,hw,hb]
  · simp [ha]

theorem exit_expectation_partition {X:Type*}[Fintype X]
    (w:X→ℝ) (A B G W:X→Prop) [DecidablePred A] [DecidablePred B] [DecidablePred G] [DecidablePred W]
    (hcover:∀x,¬B x↔G x∨W x) (f:X→ℂ):
    finiteExpectation w (fun x=>if A x∧¬B x then f x else 0)=
      finiteExpectation w (fun x=>if A x∧G x then f x else 0)+
      finiteExpectation w (fun x=>if A x∧¬G x∧W x then f x else 0):=by
  rw [←finiteExpectation_add]
  congr 1
  funext x
  exact exit_integrand_partition (A x) (B x) (G x) (W x) (hcover x) (f x)

end SpectralConsequences
