import Mathlib.RingTheory.RingHomProperties
import Mathlib.Algebra.MvPolynomial.CommRing

open TensorProduct

universe u

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
variable (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

namespace RingHom

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

def DescendsAlong : Prop :=
  ∀ (R S R' S' : Type u) [CommRing R] [CommRing S] [CommRing R'] [CommRing S'],
  ∀ [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S'],
    ∀ [IsScalarTower R S S'] [IsScalarTower R R' S'],
      ∀ [Algebra.IsPushout R S R' S'],
        Q (algebraMap R R') → P (algebraMap R' S') → P (algebraMap R S)

lemma DescendsAlong.mk (h₁ : RespectsIso P)
    (h₂ : ∀ ⦃R S T⦄ [CommRing R] [CommRing S] [CommRing T],
      ∀ [Algebra R S] [Algebra R T],
        Q (algebraMap R S) → P (algebraMap S (S ⊗[R] T)) → P (algebraMap R T)) :
    DescendsAlong P Q := by
  introv R h hQ H
  let e := h.symm.equiv
  have : (e.symm : _ →+* _).comp (algebraMap R' S') = algebraMap R' (R' ⊗[R] S) := by
    ext r
    simp [e]
  apply h₂ hQ
  rw [← this]
  exact h₁.1 _ _ H

end RingHom
