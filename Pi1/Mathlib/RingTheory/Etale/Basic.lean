import Mathlib.RingTheory.Etale.Basic

universe u

instance (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S] :
    Algebra.Smooth R S where

instance (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S] :
    Algebra.Unramified R S where

instance (R S : Type u) [CommRing R] [CommRing S] :
    letI : Algebra (R × S) S := (RingHom.snd R S).toAlgebra
    Algebra.Etale (R × S) S := by
  algebraize [RingHom.snd R S]
  exact Algebra.Etale.of_isLocalization_Away (0, 1)

instance (R S : Type u) [CommRing R] [CommRing S] :
    letI : Algebra (R × S) R := (RingHom.fst R S).toAlgebra
    Algebra.Etale (R × S) R := by
  algebraize [RingHom.fst R S]
  exact Algebra.Etale.of_isLocalization_Away (1, 0)
