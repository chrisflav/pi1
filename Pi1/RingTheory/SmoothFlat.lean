import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Smooth.Basic
import Pi1.RingTheory.Smooth.Flat

universe u

instance (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S] :
    Module.Flat R S :=
  inferInstance
