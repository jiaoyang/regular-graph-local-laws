import LocalLaw.LeafSchurModel
import LocalLaw.ScalarLeafPaddingStability

/-! # Actual global and restricted leaf-Schur comparison

The two core Green functions are compared through their genuine completed
models.  Local leaf slots are padded onto the global slot index; the actual
leaf block units follow from the model identities, rather than being assumed.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance leafSchurComparisonDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Matrix
variable {I : Type} [Fintype I] [DecidableEq I]

theorem one_padded_leaf_schur_target_bound (F : Set I) (x y p : ℂ)
    (a b : I→ℂ) (a' b' : F→ℂ) (R : Matrix I I ℂ) (S : Matrix F F ℂ)
    (hp : p≠0) (hRunit : IsUnit R) (hSunit : IsUnit S)
    (δtarget δleaf A B A' B' : ℝ) (hδleaf : 0≤δleaf)
    (hA : 0≤A) (hB : 0≤B) (hA' : 0≤A') (hB' : 0≤B') (hxy : ‖x-y‖≤δtarget)
    (ha : (∑i,‖a i‖)≤A) (hb : (∑i,‖b i‖)≤B)
    (ha' : (∑i,‖a' i‖)≤A') (hb' : (∑i,‖b' i‖)≤B')
    (hR : ∀i j,‖R i j-(if i=j then p else 0)‖≤δleaf)
    (hS : ∀i j:F,‖S i j-(if i=j then p else 0)‖≤δleaf)
    (hsmall : (Fintype.card I:ℝ)*‖p⁻¹‖*δleaf≤1/2)
    (hsmallF : (Fintype.card F:ℝ)*‖p⁻¹‖*δleaf≤1/2) :
    ‖(x-schurBilinear a R⁻¹ b)-(y-schurBilinear a' S⁻¹ b')‖≤
      δtarget+‖p⁻¹‖*(∑i:I,‖a i*b i-
        scalarLeafPaddedVector F a' i*scalarLeafPaddedVector F b' i‖)+
        (2*‖p⁻¹‖^2*δleaf)*(A*B+A'*B') := by
  have ha'p : (∑i:I,‖scalarLeafPaddedVector F a' i‖)≤A' := by
    rw [scalarLeafPaddedVector_sum_norm]
    exact ha'
  have hb'p : (∑i:I,‖scalarLeafPaddedVector F b' i‖)≤B' := by
    rw [scalarLeafPaddedVector_sum_norm]
    exact hb'
  have hRi := scalar_diagonal_inverse_stability R p hp hRunit δleaf hδleaf hR hsmall
  have hSi := scalarLeafPadding_inverse_stability F S p hSunit hp δleaf hδleaf hS hsmallF
  have hh := two_diagonal_schur_target_bound x y p a b
    (scalarLeafPaddedVector F a') (scalarLeafPaddedVector F b') R (scalarLeafPadding F S p)
    δtarget (2*‖p⁻¹‖^2*δleaf) A B A' B' (by positivity) hA hB hA' hB' hxy
    ha hb ha'p hb'p hRi hSi
  rw [scalarLeafPadding_inverse_bilinear F S p hSunit hp a' b'] at hh
  exact hh

end Matrix

namespace DeficientGraph
variable {V I : Type} [Fintype V] [Fintype I] {d : ℕ}

theorem attachLeaves_restriction_schur_bound (g : DeficientGraph V d) (hd : 3≤d)
    (mate : I→V) (hrestore : ∀v,multiLeafMultiplicity mate v≤g.deficit v)
    (S : Set V) (q z p : ℂ) (hz : 0<z.im) (hq : 0≤q.im) (hp : p≠0)
    (i j : S) (δtarget δleaf W : ℝ) (hδleaf : 0≤δleaf) (hW : 0≤W)
    (hxy : let P:=(g.attachLeaves (by omega) mate hrestore).extensionGreen q z
      let Q:=((g.attachLeaves (by omega) mate hrestore).restrict (multiLeafLift mate S)).extensionGreen q z
      ‖P (.inl i.val) (.inl j.val)-Q (multiLeafLiftCore mate S i) (multiLeafLiftCore mate S j)‖≤δtarget)
    (ha : ∑l:I,‖(g.attachLeaves (by omega) mate hrestore).extensionGreen q z (.inl i.val) (.inr l)‖≤W)
    (hb : ∑l:I,‖(g.attachLeaves (by omega) mate hrestore).extensionGreen q z (.inr l) (.inl j.val)‖≤W)
    (ha' : ∑l:{l:I //mate l∈S},
      ‖((g.attachLeaves (by omega) mate hrestore).restrict (multiLeafLift mate S)).extensionGreen q z
        (multiLeafLiftCore mate S i) (multiLeafLiftLeaf mate S l)‖≤W)
    (hb' : ∑l:{l:I //mate l∈S},
      ‖((g.attachLeaves (by omega) mate hrestore).restrict (multiLeafLift mate S)).extensionGreen q z
        (multiLeafLiftLeaf mate S l) (multiLeafLiftCore mate S j)‖≤W)
    (hR : ∀l k:I,‖(g.attachLeaves (by omega) mate hrestore).extensionGreen q z
      (.inr l) (.inr k)-(if l=k then p else 0)‖≤δleaf)
    (hQ : ∀l k:{l:I //mate l∈S},
      ‖((g.attachLeaves (by omega) mate hrestore).restrict (multiLeafLift mate S)).extensionGreen q z
        (multiLeafLiftLeaf mate S l) (multiLeafLiftLeaf mate S k)-(if l=k then p else 0)‖≤δleaf)
    (hsmall : (Fintype.card I:ℝ)*‖p⁻¹‖*δleaf≤1/2)
    (hsmallF : (Fintype.card {l:I //mate l∈S}:ℝ)*‖p⁻¹‖*δleaf≤1/2) :
    let P:=(g.attachLeaves (by omega) mate hrestore).extensionGreen q z
    let Q:=((g.attachLeaves (by omega) mate hrestore).restrict (multiLeafLift mate S)).extensionGreen q z
    let E : Set I:={l |mate l∈S}
    let a':=scalarLeafPaddedVector E (fun l=>Q (multiLeafLiftCore mate S i) (multiLeafLiftLeaf mate S l))
    let b':=scalarLeafPaddedVector E (fun l=>Q (multiLeafLiftLeaf mate S l) (multiLeafLiftCore mate S j))
    ‖g.extensionGreen q z i.val j.val-(g.restrict S).extensionGreen q z i j‖≤
      δtarget+‖p⁻¹‖*(∑l:I,‖P (.inl i.val) (.inr l)*P (.inr l) (.inl j.val)-a' l*b' l‖)+
        4*‖p⁻¹‖^2*δleaf*W^2 := by
  dsimp only
  let P:=(g.attachLeaves (by omega) mate hrestore).extensionGreen q z
  let Q:=((g.attachLeaves (by omega) mate hrestore).restrict (multiLeafLift mate S)).extensionGreen q z
  let E : Set I:={l |mate l∈S}
  have hglobal:=g.attachLeaves_Green_leaf_schur hd mate hrestore q z hz hq
  have hlocal:=g.attachLeaves_lift_Green_leaf_schur hd mate hrestore S q z hz hq
  have hh:=one_padded_leaf_schur_target_bound E
    (P (.inl i.val) (.inl j.val)) (Q (multiLeafLiftCore mate S i) (multiLeafLiftCore mate S j)) p
    (fun l=>P (.inl i.val) (.inr l)) (fun l=>P (.inr l) (.inl j.val))
    (fun l=>Q (multiLeafLiftCore mate S i) (multiLeafLiftLeaf mate S l))
    (fun l=>Q (multiLeafLiftLeaf mate S l) (multiLeafLiftCore mate S j))
    (P.submatrix Sum.inr Sum.inr)
    (Q.submatrix (multiLeafLiftLeaf mate S) (multiLeafLiftLeaf mate S))
    hp hglobal.1 hlocal.1 δtarget δleaf W W W W hδleaf hW hW hW hW hxy
    ha hb ha' hb' hR hQ hsmall hsmallF
  have hlocal' : (g.restrict S).extensionGreen q z i j =
      Q (multiLeafLiftCore mate S i) (multiLeafLiftCore mate S j) -
        schurBilinear (fun l:E=>Q (multiLeafLiftCore mate S i) (multiLeafLiftLeaf mate S l))
          (Q.submatrix (multiLeafLiftLeaf mate S) (multiLeafLiftLeaf mate S))⁻¹
          (fun l:E=>Q (multiLeafLiftLeaf mate S l) (multiLeafLiftCore mate S j)) := by
    convert hlocal.2 i j using 1
  rw [←hglobal.2 i.val j.val,←hlocal'] at hh
  convert hh using 1
  ring

end DeficientGraph
end LocalLaw
