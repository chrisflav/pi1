import Pi1.RingTheory.SmoothDescent
import Pi1.RingTheory.FiniteEtale.Basic

universe u v w

open TensorProduct

lemma Algebra.FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (T : Type u) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [Algebra.FormallyUnramified T (T ⊗[R] S)] :
    Algebra.FormallyUnramified R S := by
  constructor
  let _ : Algebra S (T ⊗[R] S) := TensorProduct.rightAlgebra
  have : Subsingleton (T ⊗[R] Ω[S⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquivBase R T S (T ⊗[R] S)).subsingleton
  exact Module.FaithfullyFlat.lTensor_reflects_triviality R T _

lemma Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S]
    (T : Type u) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [Algebra.Etale T (T ⊗[R] S)] :
    Algebra.Etale R S := by
  have : Algebra.FinitePresentation R S := .of_finitePresentation_tensorProduct_of_faithfullyFlat T
  refine ⟨?_, .of_finitePresentation_tensorProduct_of_faithfullyFlat T⟩
  rw [FormallyEtale.iff_formallyUnramified_and_formallySmooth]
  exact ⟨.of_formallyUnramified_tensorProduct_of_faithfullyFlat T,
    .of_formallySmooth_tensorProduct T⟩

lemma Algebra.FiniteEtale.of_finiteEtale_tensorProduct_of_faithfullyFlat {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S]
    (T : Type u) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [Algebra.FiniteEtale T (T ⊗[R] S)] :
    Algebra.FiniteEtale R S := by
  have : Algebra.Etale R S :=
    .of_etale_tensorProduct_of_faithfullyFlat T
  have : Module.Finite R S :=
    .of_finite_tensorProduct_of_faithfullyFlat T
  constructor
