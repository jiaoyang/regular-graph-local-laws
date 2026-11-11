import SpectralConsequences.FiniteGridExclusion
import Mathlib.Algebra.Order.Floor.Ring

/-! An explicit polynomial-size finite mesh for testing nontrivial outliers.
Coverage and the exterior restriction are proved from the literal grid. -/
noncomputable section
namespace SpectralConsequences
local instance exteriorMeshDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def realMesh (K:ℕ)(η:ℝ):Finset ℝ:=
  (Finset.range (2*K+1)).image (fun j:ℕ=>(j:ℝ)*η-(K:ℝ)*η)

def exteriorMesh (K:ℕ)(M Δ η:ℝ):Finset ℝ:=
  (realMesh K η).filter (fun E=>|E|≤M+η ∧2+Δ/2≤|E|)

theorem realMesh_cover (K:ℕ)(M η:ℝ)(hη:0<η)(hwidth:M≤(K:ℝ)*η)
    (x:ℝ)(hx:|x|≤M):∃E∈realMesh K η,|x-E|≤η:=by
  have hxl:-(K:ℝ)*η≤x:=by have hh:=(abs_le.mp hx).1;linarith
  have hxu:x≤(K:ℝ)*η:=(le_abs_self x).trans (hx.trans hwidth)
  let u:ℝ:=(x+(K:ℝ)*η)/η
  let k:ℕ:=⌊u⌋₊
  have hu:0≤u:=div_nonneg (by linarith) hη.le
  have hlu:(k:ℝ)≤u:=Nat.floor_le hu
  have huu:u<(k:ℝ)+1:=Nat.lt_floor_add_one u
  have hlow:(k:ℝ)*η≤x+(K:ℝ)*η:=(le_div_iff₀ hη).mp hlu
  have hhigh:x+(K:ℝ)*η<((k:ℝ)+1)*η:=(div_lt_iff₀ hη).mp huu
  have hk:k≤2*K:=by
    have hreal:(k:ℝ)≤2*(K:ℝ):=by nlinarith
    exact_mod_cast hreal
  refine ⟨(k:ℝ)*η-(K:ℝ)*η,Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr (by omega),rfl⟩,?_⟩
  rw [abs_of_nonneg (by linarith)]
  linarith

theorem exteriorMesh_cover (K:ℕ)(M Δ η:ℝ)(hη:0<η)(hsmall:η≤Δ/2)
    (hwidth:M≤(K:ℝ)*η)(x:ℝ)(hx:|x|≤M)(hout:2+Δ < |x|):
    ∃E∈exteriorMesh K M Δ η,|x-E|≤η:=by
  obtain ⟨E,hE,hnear⟩:=realMesh_cover K M η hη hwidth x hx
  have h1:=abs_abs_sub_abs_le_abs_sub E x
  have h2:=abs_abs_sub_abs_le_abs_sub x E
  have he:|E|≤M+η:=by
    have hh:|E| - |x|≤η:=(le_abs_self _).trans (h1.trans (by simpa only [abs_sub_comm] using hnear))
    linarith
  have ho:2+Δ/2≤|E|:=by
    have hh:|x| - |E|≤η:=(le_abs_self _).trans (h2.trans hnear)
    linarith
  exact ⟨E,Finset.mem_filter.mpr ⟨hE,he,ho⟩,hnear⟩

theorem exteriorMesh_energy_bounds (K:ℕ)(M Δ η:ℝ)(E:ℝ)
    (hE:E∈exteriorMesh K M Δ η):|E|≤M+η ∧2+Δ/2≤|E|:=
  (Finset.mem_filter.mp hE).2

theorem exteriorMesh_card_le (K:ℕ)(M Δ η:ℝ):
    (exteriorMesh K M Δ η).card≤2*K+1:=by
  exact (Finset.card_filter_le _ _).trans ((Finset.card_image_le).trans_eq (Finset.card_range _))

theorem exteriorMesh_card_le_cube (N:ℕ)(hN:3≤N)(M Δ η:ℝ):
    (exteriorMesh (N^2) M Δ η).card≤N^3:=by
  apply (exteriorMesh_card_le (N^2) M Δ η).trans
  have hh:=Nat.mul_le_mul_left (N^2) hN
  have hp:1≤N^2:=by nlinarith
  nlinarith

end SpectralConsequences
