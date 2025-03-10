import Pi1.RingTheory.FiniteEtale.Basic

universe u

open TensorProduct

lemma Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S]
    (T : Type u) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [Algebra.Etale T (T ⊗[R] S)] :
    Algebra.Etale R S :=
  sorry

lemma Algebra.FiniteEtale.of_finiteEtale_tensorProduct_of_faithfullyFlat {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S]
    (T : Type u) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [Algebra.FiniteEtale T (T ⊗[R] S)] :
    Algebra.FiniteEtale R S :=
  sorry
