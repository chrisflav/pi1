import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Smooth.Basic

universe u

instance (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S] :
    Module.Flat R S :=
  -- done, but needs to be PRed
  sorry
