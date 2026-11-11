import LocalLaw.LeafSchurRows

/-! # Uniform actual core caps from constant leaf inverse rows -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance leafSchurUniformDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem schurBilinear_norm_of_row_cap (a b : I→ℂ) (R : Matrix I I ℂ) (A D C : ℝ)
    (hD : 0≤D) (hC : 0≤C) (ha : (∑i,‖a i‖)≤A)
    (hR : ∀i,∑j,‖R i j‖≤D) (hb : ∀j,‖b j‖≤C) :
    ‖schurBilinear a R b‖≤A*D*C := by
  let X:Matrix Unit I ℂ:=fun _ i=>a i
  let Y:Matrix I Unit ℂ:=fun i _=>b i
  have hX : ∀u:Unit,∑i,‖X u i‖≤A := fun _=>ha
  have hY : ∀i,∑u:Unit,‖Y i u‖≤C := by intro i;simpa only [Fintype.sum_unique] using hb i
  have hXR:=rectangular_product_row_sum_bound X R A D hD hX hR
  have hh:=rectangular_product_row_sum_bound (X*R) Y (A*D) C hC hXR hY ()
  have he : ((X*R)*Y) () ()=schurBilinear a R b := by
    rw [Matrix.mul_assoc]
    simp only [Matrix.mul_apply,X,Y,schurBilinear,Finset.mul_sum,mul_assoc]
  simpa only [Fintype.sum_unique,he] using hh

namespace DeficientGraph
variable {V L : Type} [Fintype V] [Fintype L] {d : ℕ}

theorem attachLeaves_uniform_core_cap (g : DeficientGraph V d) (hd : 3≤d)
    (mate : L→V) (hr : ∀v,multiLeafMultiplicity mate v≤g.deficit v)
    (q z p : ℂ) (hz : 0<z.im) (hq : 0≤q.im) (hp : p≠0)
    (δ W C : ℝ) (hδ : 0≤δ) (hC : 0≤C)
    (hcap : ∀a b,‖(g.attachLeaves (by omega) mate hr).extensionGreen q z a b‖≤C)
    (hrows : ∀x:V,∑l:L,‖(g.attachLeaves (by omega) mate hr).extensionGreen q z (.inl x) (.inr l)‖≤W)
    (herror : ∀l k:L,‖(g.attachLeaves (by omega) mate hr).extensionGreen q z (.inr l) (.inr k)-
      (if l=k then p else 0)‖≤δ)
    (hsmall : (Fintype.card L:ℝ)*‖p⁻¹‖*δ≤1/2) :
    ∀x y,‖g.extensionGreen q z x y‖≤C+2*W*‖p⁻¹‖*C := by
  have hs:=g.attachLeaves_Green_leaf_schur hd mate hr q z hz hq
  have hRi:=scalar_diagonal_inverse_row_col_bound
    (((g.attachLeaves (by omega) mate hr).extensionGreen q z).submatrix Sum.inr Sum.inr)
    p hp hs.1 δ hδ herror hsmall
  intro x y
  have hcorr:=schurBilinear_norm_of_row_cap
    (fun l:L=>(g.attachLeaves (by omega) mate hr).extensionGreen q z (.inl x) (.inr l))
    (fun l:L=>(g.attachLeaves (by omega) mate hr).extensionGreen q z (.inr l) (.inl y))
    (((g.attachLeaves (by omega) mate hr).extensionGreen q z).submatrix Sum.inr Sum.inr)⁻¹
    W (2*‖p⁻¹‖) C (by positivity) hC (hrows x) hRi.1 (fun l=>hcap (.inr l) (.inl y))
  rw [hs.2 x y]
  exact (norm_sub_le _ _).trans ((add_le_add (hcap (.inl x) (.inl y)) hcorr).trans_eq (by ring))

theorem attachLeaves_lift_uniform_core_cap (g : DeficientGraph V d) (hd : 3≤d)
    (mate : L→V) (hr : ∀v,multiLeafMultiplicity mate v≤g.deficit v) (S : Set V)
    (q z p : ℂ) (hz : 0<z.im) (hq : 0≤q.im) (hp : p≠0)
    (δ W C : ℝ) (hδ : 0≤δ) (hC : 0≤C)
    (hcap : ∀a b,‖((g.attachLeaves (by omega) mate hr).restrict (multiLeafLift mate S)).extensionGreen q z a b‖≤C)
    (hrows : ∀x:S,∑l:{l:L //mate l∈S},
      ‖((g.attachLeaves (by omega) mate hr).restrict (multiLeafLift mate S)).extensionGreen q z
        (multiLeafLiftCore mate S x) (multiLeafLiftLeaf mate S l)‖≤W)
    (herror : ∀l k:{l:L //mate l∈S},
      ‖((g.attachLeaves (by omega) mate hr).restrict (multiLeafLift mate S)).extensionGreen q z
        (multiLeafLiftLeaf mate S l) (multiLeafLiftLeaf mate S k)-(if l=k then p else 0)‖≤δ)
    (hsmall : (Fintype.card {l:L //mate l∈S}:ℝ)*‖p⁻¹‖*δ≤1/2) :
    ∀x y:S,‖(g.restrict S).extensionGreen q z x y‖≤C+2*W*‖p⁻¹‖*C := by
  let Q:=((g.attachLeaves (by omega) mate hr).restrict (multiLeafLift mate S)).extensionGreen q z
  let leaf:=multiLeafLiftLeaf mate S
  let core:=multiLeafLiftCore mate S
  have hs:=g.attachLeaves_lift_Green_leaf_schur hd mate hr S q z hz hq
  have hRi:=scalar_diagonal_inverse_row_col_bound (Q.submatrix leaf leaf) p hp hs.1 δ hδ herror hsmall
  intro x y
  have hcorr:=schurBilinear_norm_of_row_cap (fun l:{l:L //mate l∈S}=>Q (core x) (leaf l))
    (fun l:{l:L //mate l∈S}=>Q (leaf l) (core y)) (Q.submatrix leaf leaf)⁻¹
    W (2*‖p⁻¹‖) C (by positivity) hC (hrows x) hRi.1 (fun l=>hcap (leaf l) (core y))
  rw [hs.2 x y]
  exact (norm_sub_le _ _).trans ((add_le_add (hcap (core x) (core y)) hcorr).trans_eq (by ring))

end DeficientGraph
end LocalLaw
