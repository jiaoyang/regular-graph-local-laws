import LocalLaw.GraphModel
import LocalLaw.ParameterGrowth
import LocalLaw.FiniteResampling
import LocalLaw.BicyclicBallWitness

/-! # Literal paper radii, exceptional counts and conditional uniform law

Real metric-radius balls equal the induced integer-floor balls exactly.
Likewise an integer exceptional count is at most N^c exactly when it is at
most floor(N^c). Conditioning the original uniform graph law is the uniform
law on the structural subtype, with an explicit positive denominator.
-/
open Filter
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance paperEventDecidable (p:Prop):Decidable p:=Classical.propDecidable p

/-- The real radius R=(c/4) log_(d-1) N in Definition 1.1. -/
def paperRadius (d N:ℕ)(c:ℝ):ℝ:=(c/4)*Real.log (N:ℝ)/Real.log ((d-1:ℕ):ℝ)

/-- Reachability is essential because mathlib's natural distance is zero
between disconnected vertices. This is the literal finite real-radius ball. -/
def paperBallVertices {V:Type*}(G:SimpleGraph V)(o:V)(R:ℝ):Set V:=
  {v | G.Reachable o v ∧ (G.dist o v:ℝ) ≤ R}

def paperBall {V:Type*}(G:SimpleGraph V)(o:V)(R:ℝ):SimpleGraph (paperBallVertices G o R):=
  G.induce (paperBallVertices G o R)

theorem paperBallVertices_eq_floor {V:Type*}(G:SimpleGraph V)(o:V)(R:ℝ)(hR:0≤R):
    paperBallVertices G o R=graphBallVertices G o ⌊R⌋₊:=by
  ext v
  constructor
  · rintro ⟨hr,hd⟩
    have hfin:G.edist o v≠⊤:=SimpleGraph.edist_ne_top_iff_reachable.mpr hr
    have he:(G.dist o v:ℕ∞)=G.edist o v:=ENat.coe_toNat hfin
    change G.edist o v ≤ (⌊R⌋₊:ℕ∞)
    rw [←he]
    exact ENat.coe_le_coe.mpr (Nat.le_floor hd)
  · intro hv
    have hfin:G.edist o v≠⊤:=ne_of_lt (hv.trans_lt (ENat.coe_lt_top _))
    have he:(G.dist o v:ℕ∞)=G.edist o v:=ENat.coe_toNat hfin
    refine ⟨SimpleGraph.reachable_of_edist_ne_top hfin,?_⟩
    apply (Nat.le_floor_iff hR).mp
    exact ENat.coe_le_coe.mp (by rw [he];exact hv)

def paperBallIsoFloor {V:Type*}(G:SimpleGraph V)(o:V)(R:ℝ)(hR:0≤R):
    paperBall G o R ≃g graphBall G o ⌊R⌋₊ where
  toEquiv:=Equiv.setCongr (paperBallVertices_eq_floor G o R hR)
  map_rel_iff':=Iff.rfl

theorem paperBall_isTree_iff {V:Type*}(G:SimpleGraph V)(o:V)(R:ℝ)(hR:0≤R):
    (paperBall G o R).IsTree ↔ (graphBall G o ⌊R⌋₊).IsTree:=by
  exact iff_of_eq (congrArg (fun S:Set V=>(G.induce S).IsTree) (paperBallVertices_eq_floor G o R hR))

theorem paperRadius_nonnegative (d N:ℕ)(c:ℝ)(hd:3≤d)(hN:1≤N)(hc:0≤c):
    0≤paperRadius d N c:=by
  unfold paperRadius
  exact div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hN)))
    (Real.log_nonneg (by exact_mod_cast (show 1≤d-1 by omega)))

@[simp] theorem paperRadius_floor (d N:ℕ)(c:ℝ):
    ⌊paperRadius d N c⌋₊=logarithmicRadius (c/4) d N:=rfl

/-- Exactly Definition 1.1 using a real radius and a real exceptional count. -/
def PaperStructural {N d:ℕ}(c:ℝ)(ω:ℕ)(g:RegularGraph N d):Prop:=
  (∀o,graphExcess (paperBall g.graph o (paperRadius d N c))≤ω) ∧
  ((Finset.univ.filter (fun o=>¬(paperBall g.graph o (paperRadius d N c)).IsTree)).card:ℝ)≤(N:ℝ)^c

theorem paperStructural_iff {N d:ℕ}(c:ℝ)(ω:ℕ)(g:RegularGraph N d)
    (hd:3≤d)(hN:1≤N)(hc:0≤c):
    PaperStructural c ω g↔RegularGraph.structural (logarithmicRadius (c/4) d N) ω ⌊(N:ℝ)^c⌋₊ g:=by
  have hR:=paperRadius_nonnegative d N c hd hN hc
  have hexcess:∀o,graphExcess (paperBall g.graph o (paperRadius d N c))=
      graphBallExcess g.graph o (logarithmicRadius (c/4) d N):=by
    intro o
    simpa only [paperRadius_floor] using graphExcess_iso (paperBallIsoFloor g.graph o (paperRadius d N c) hR)
  have htree:∀o,(paperBall g.graph o (paperRadius d N c)).IsTree ↔
      (graphBall g.graph o (logarithmicRadius (c/4) d N)).IsTree:=by
    intro o
    simpa only [paperRadius_floor] using paperBall_isTree_iff g.graph o (paperRadius d N c) hR
  unfold PaperStructural RegularGraph.structural GraphTreeLike nonTreeCenters
  simp_rw [hexcess,htree]
  rw [←Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) c)]

section UniformConditioning
variable {X:Type*} [Fintype X]

theorem uniform_eventMass_eq_count (P:X→Prop):
    eventMass (finiteUniformWeight X) P=
      ((Finset.univ.filter P).card:ℝ)/(Fintype.card X:ℝ):=by
  unfold eventMass finiteUniformWeight
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one_div]

/-- Nonempty conditioning gives a strictly positive actual denominator. -/
theorem uniform_conditioning_mass_positive (A:X→Prop) [Nonempty {x:X//A x}]:
    0<eventMass (finiteUniformWeight X) A:=by
  letI:Nonempty X:=⟨(Classical.choice (inferInstance:Nonempty {x:X//A x})).val⟩
  rw [uniform_eventMass_eq_count,←Fintype.card_subtype]
  exact div_pos (by positivity) (by positivity)

/-- Conditional probability under the original uniform law is exactly the
uniform probability of the predicate on the conditioning subtype. -/
theorem conditional_uniform_eq_subtype_uniform (A P:X→Prop) [Nonempty {x:X//A x}]:
    eventMass (finiteUniformWeight X) (fun x=>A x∧P x)/eventMass (finiteUniformWeight X) A=
      eventMass (finiteUniformWeight {x:X//A x}) (fun x=>P x.val):=by
  letI:Nonempty X:=⟨(Classical.choice (inferInstance:Nonempty {x:X//A x})).val⟩
  let e:{x:X//A x∧P x} ≃ {x:{x:X//A x}//P x.val}:=
    { toFun:=fun x=>⟨⟨x.val,x.property.1⟩,x.property.2⟩
      invFun:=fun x=>⟨x.val.val,⟨x.val.property,x.property⟩⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl }
  have he:Fintype.card {x:X//A x∧P x}=Fintype.card {x:{x:X//A x}//P x.val}:=Fintype.card_congr e
  simp only [uniform_eventMass_eq_count,←Fintype.card_subtype]
  rw [he]
  have hX:(Fintype.card X:ℝ)≠0:=by positivity
  have hA:(Fintype.card {x:X//A x}:ℝ)≠0:=by positivity
  field_simp [hX,hA]

end UniformConditioning
end SpectralConsequences
