module

public import Mathlib.RingTheory.Etale.Descent
public import Pi1.RingTheory.FiniteEtale.Basic

@[expose] public section

universe u v w

open TensorProduct

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
