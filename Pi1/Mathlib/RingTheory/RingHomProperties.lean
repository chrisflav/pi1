import Mathlib.RingTheory.RingHomProperties
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.Algebra.MvPolynomial.CommRing
import Pi1.Mathlib.Algebra.Category.Ring.Colimits

set_option linter.unusedTactic false

open TensorProduct

universe u

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
variable (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

namespace RingHom

variable (R S T : Type u) [CommRing R] [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

def CodescendsAlong : Prop :=
  ∀ (R S R' S' : Type u) [CommRing R] [CommRing S] [CommRing R'] [CommRing S'],
  ∀ [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S'],
    ∀ [IsScalarTower R S S'] [IsScalarTower R R' S'],
      ∀ [Algebra.IsPushout R S R' S'],
        Q (algebraMap R R') → P (algebraMap R' S') → P (algebraMap R S)

lemma CodescendsAlong.mk (h₁ : RespectsIso P)
    (h₂ : ∀ ⦃R S T⦄ [CommRing R] [CommRing S] [CommRing T],
      ∀ [Algebra R S] [Algebra R T],
        Q (algebraMap R S) → P (algebraMap S (S ⊗[R] T)) → P (algebraMap R T)) :
    CodescendsAlong P Q := by
  introv R h hQ H
  let e := h.symm.equiv
  have : (e.symm : _ →+* _).comp (algebraMap R' S') = algebraMap R' (R' ⊗[R] S) := by
    ext r
    simp [e]
  apply h₂ hQ
  rw [← this]
  exact h₁.1 _ _ H

lemma CodescendsAlong.algebraMap_tensorProduct (hPQ : CodescendsAlong P Q)
    (h : Q (algebraMap R S)) (H : P (algebraMap S (S ⊗[R] T))) :
    P (algebraMap R T) :=
  let _ : Algebra T (S ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  hPQ R T S (S ⊗[R] T) h H

lemma CodescendsAlong.includeRight (hPQ : CodescendsAlong P Q) (h : Q (algebraMap R T))
    (H : P ((Algebra.TensorProduct.includeRight.toRingHom : T →+* S ⊗[R] T))) :
    P (algebraMap R S) := by
  let _ : Algebra T (S ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  apply hPQ R S T (S ⊗[R] T) h H

lemma isStableUnderCobaseChange_toMorphismProperty_iff :
    (toMorphismProperty P).IsStableUnderCobaseChange ↔ IsStableUnderBaseChange P := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · intro R S R' S' _ _ _ _ _ _ _ _ _ _ _ hsq hRS
    rw [← CommRingCat.isPushout_iff_isPushout] at hsq
    exact h.1 (f := CommRingCat.ofHom (algebraMap R S)) hsq.flip hRS
  · constructor
    intro R S R' S' f g f' g' hsq hf
    algebraize [f.hom, g.hom, f'.hom, g'.hom, f'.hom.comp g.hom]
    have : IsScalarTower R S S' := .of_algebraMap_eq fun x ↦ congr($(hsq.1.1).hom x)
    have : Algebra.IsPushout R S R' S' :=
      (CommRingCat.isPushout_iff_isPushout.mp hsq).symm
    apply h (R := R) (S := S) _ _ hf

end RingHom
