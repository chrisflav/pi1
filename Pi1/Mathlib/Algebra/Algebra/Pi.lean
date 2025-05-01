import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.Pi

/--
Transport dependent functions through an equivalence of the base space.

This is `Equiv.piCongrLeft'` as an `AlgEquiv`.
-/
def AlgEquiv.piCongrLeft' {ι ι' : Type*} (R : Type*) (S : ι → Type*) (e : ι ≃ ι')
    [CommSemiring R] [∀ i, Semiring (S i)] [∀ i, Algebra R (S i)] :
    (Π i, S i) ≃ₐ[R] Π i, S (e.symm i) :=
  .ofLinearEquiv (.piCongrLeft' R S e) (by ext; simp) (by intro x y; ext; simp)

/--
Transport dependent functions through an equivalence of the base space, expressed as
"simplification".

This is `Equiv.piCongrLeft` as an `AlgEquiv`.
-/
def AlgEquiv.piCongrLeft {ι ι' : Type*} (R : Type*) (S : ι → Type*) (e : ι' ≃ ι)
    [CommSemiring R] [∀ i, Semiring (S i)] [∀ i, Algebra R (S i)] :
    (Π i, S (e i)) ≃ₐ[R] Π i, S i :=
  (AlgEquiv.piCongrLeft' R S e.symm).symm

/-- Product of algebra isomorphisms. -/
def AlgEquiv.prodCongr {R S T A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Semiring S] [Semiring T] [Algebra R S] [Algebra R T] [Algebra R A] [Algebra R B]
    (l : S ≃ₐ[R] A) (r : T ≃ₐ[R] B) :
    (S × T) ≃ₐ[R] A × B :=
  .ofRingEquiv (f := RingEquiv.prodCongr l r) <| by simp

/-- If `ι` as a unique element, then `ι → S` is isomorphic to `S` as an `R`-algebra. -/
def AlgEquiv.funUnique (ι : Type*) (R S : Type*) [Unique ι] [CommSemiring R] [Semiring S]
    [Algebra R S] : (ι → S) ≃ₐ[R] S :=
  .ofLinearEquiv (.funUnique ι R S) (by simp) (by simp)

/-- `Equiv.sumArrowEquivProdArrow` as an algebra equivalence. -/
def AlgEquiv.sumArrowEquivProdArrow (R A α β : Type*) [CommSemiring R] [Semiring A] [Algebra R A] :
    (α ⊕ β → A) ≃ₐ[R] (α → A) × (β → A) :=
  .ofLinearEquiv (.sumArrowLequivProdArrow α β R A) rfl <| fun x y ↦ by ext <;> simp
