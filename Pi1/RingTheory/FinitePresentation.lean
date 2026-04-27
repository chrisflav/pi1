import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.RingHom.FinitePresentation
import Pi1.Mathlib.RingTheory.Ideal.Quotient.Operations

universe u

lemma Pi.ker_algHom {I : Type*} (R : Type*) (f : I → Type*) [CommSemiring R] [∀ i, Semiring (f i)]
    [∀ i, Algebra R (f i)] {A : Type*} [Semiring A] [Algebra R A]
    (g : ∀ i, A →ₐ[R] f i) : RingHom.ker (Pi.algHom R f g) = ⨅ i, RingHom.ker (g i) :=
  Pi.ker_ringHom _

open TensorProduct

instance (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FinitePresentation R A] [Algebra.FinitePresentation R B] :
    Algebra.FinitePresentation R (A ⊗[R] B) :=
  Algebra.FinitePresentation.trans R A (A ⊗[R] B)

instance (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FormallyEtale R A] [Algebra.FormallyEtale R B] :
    Algebra.FormallyEtale R (A ⊗[R] B) :=
  Algebra.FormallyEtale.comp R A (A ⊗[R] B)

open Polynomial

@[simp]
lemma MvPolynomial.aeval_polynomialEval₂_C {R S : Type*} [CommSemiring R]
      [CommSemiring S] [Algebra R S] (f : PUnit → S) (p : R[X]) :
    MvPolynomial.aeval f (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X ()) p) =
      Polynomial.eval₂ (algebraMap R S) (f ()) p := by
  induction p using Polynomial.induction_on with
  | C => simp
  | monomial => simp
  | add p q hp hq => simp [hp, hq]

instance (priority := 900) {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S] : Module.FinitePresentation R S :=
  (Module.FinitePresentation.iff_finitePresentation_of_finite R S).mpr ‹_›
