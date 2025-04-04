import Mathlib

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

noncomputable
def finrank {X S : Scheme.{u}} (f : X ⟶ S) : S → ℕ :=
  sorry

lemma rank_SpecMap_algebraMap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (x : PrimeSpectrum R) :
    finrank (Spec.map (CommRingCat.ofHom <| algebraMap R S)) x =
      Module.rankAtStalk S x := sorry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsFinite f]
    [LocallyOfFinitePresentation f]

lemma continuous_finrank [Flat f] [IsFinite f]
    [LocallyOfFinitePresentation f] : Continuous (finrank f) := sorry

lemma isIso_iff_rank_eq [Flat f] [IsFinite f] [LocallyOfFinitePresentation f] :
    CategoryTheory.IsIso f ↔ finrank f = 1 :=
  sorry

lemma finrank_eq_one_of_isIso [IsIso f] : finrank f = 1 := by
  rwa [← isIso_iff_rank_eq]

lemma one_le_finrank_iff_surjective [Flat f] [IsFinite f] [LocallyOfFinitePresentation f] :
    1 ≤ finrank f ↔ Surjective f := by
  sorry

lemma one_le_finrank_map [Flat f] [IsFinite f] [LocallyOfFinitePresentation f] (x : X) :
    1 ≤ finrank f (f.base x) :=
  sorry

lemma finrank_eq_const_of_preconnectedSpace
    [PreconnectedSpace Y] (y y' : Y) :
    finrank f y = finrank f y' := by
  apply IsLocallyConstant.apply_eq_of_preconnectedSpace
  rw [IsLocallyConstant.iff_continuous]
  exact continuous_finrank f

lemma finrank_pullback_snd {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Flat f] [IsFinite f] [LocallyOfFinitePresentation f] (y : Y) :
    finrank (pullback.snd f g) y = finrank f (g.base y) :=
  sorry

end AlgebraicGeometry
