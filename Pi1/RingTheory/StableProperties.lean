import Pi1.Mathlib.CategoryTheory.MorphismProperty.UnderAdjunction
import Pi1.FundamentalGroup.AffineAnd
import Mathlib

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

universe u

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

namespace RingHom

/--
A property `P` of ring homomorphisms is said to have stable equalizers, if the equalizer
of algebra maps between algebras with structure morphisms satisfying `P`, is preserved by
arbitrary base change.
-/
def HasStableEqualizers : Prop :=
  ∀ {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R S] [Algebra R B]
    (f g : A →ₐ[R] B), P (algebraMap R A) → P (algebraMap R B) →
    Function.Bijective (f.tensorEqualizer R S g)

end RingHom

open CategoryTheory Limits RingHom MorphismProperty

namespace CommRingCat

variable {P}

lemma preservesFiniteProducts_pushout (hPi : RingHom.RespectsIso P)
    (hPp : RingHom.HasFiniteProducts P)
    [(toMorphismProperty P).IsStableUnderCobaseChange]
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    PreservesFiniteProducts (Under.pushout (toMorphismProperty P) ⊤ f) := by
  have := CommRingCat.Under.createsFiniteProductsForget hPi hPp R
  constructor
  intro n
  constructor
  intro K
  have : PreservesLimit K (Under.pushout (toMorphismProperty P) ⊤ f ⋙
        Under.forget (toMorphismProperty P) ⊤ S) :=
    inferInstanceAs <| PreservesLimit K (Under.forget (toMorphismProperty P) ⊤ R ⋙ Under.pushout f)
  apply CategoryTheory.Limits.preservesLimit_of_reflects_of_preserves _
    (MorphismProperty.Under.forget _ ⊤ S)

lemma preservesLimit_parallelPair_tensorProd_of_tensorEqualizer_bijective
    {R S : CommRingCat.{u}} [Algebra R S] {A B : Under R} {f g : A ⟶ B}
    (H : Function.Bijective <| (toAlgHom f).tensorEqualizer R S (toAlgHom g)) :
    PreservesLimit (parallelPair f g) (tensorProd R S) := by
  let e0 := AlgEquiv.ofBijective ((toAlgHom f).tensorEqualizer S S (toAlgHom g)) H |>.toUnder
  let e : Under.tensorProdEqualizer f g ≅ Under.equalizerFork'
      (Algebra.TensorProduct.map (AlgHom.id S S) (toAlgHom f))
      (Algebra.TensorProduct.map (AlgHom.id S S) (toAlgHom g)) :=
    Fork.ext e0 <| by
      ext
      apply AlgHom.coe_tensorEqualizer
  let c : Fork f g := Under.equalizerFork f g
  let hc : IsLimit c := Under.equalizerForkIsLimit f g
  apply preservesLimit_of_preserves_limit_cone hc
  apply (isLimitMapConeForkEquiv (tensorProd R S) _).symm <|
    (IsLimit.equivIsoLimit e.symm) <|
    Under.equalizerFork'IsLimit _ _

lemma preservesLimit_parallelPair_tensorProd_of_hasStableEqualizers
    (hPse : HasStableEqualizers P) {R S : CommRingCat.{u}}
    [Algebra R S] {A B : Under R} (f g : A ⟶ B)
    (hA : P A.hom.hom) (hB : P B.hom.hom) :
    PreservesLimit (parallelPair f g) (tensorProd R S) :=
  preservesLimit_parallelPair_tensorProd_of_tensorEqualizer_bijective
    (hPse _ _ hA hB)

lemma preservesEqualizers_pushout_of_hasStableEqualizers (hPi : RespectsIso P)
    (hPe : HasEqualizers P) (hPse : HasStableEqualizers P)
    [(toMorphismProperty P).IsStableUnderCobaseChange]
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    PreservesLimitsOfShape WalkingParallelPair (Under.pushout (toMorphismProperty P) ⊤ f) := by
  constructor
  intro K
  have := CommRingCat.Under.createsEqualizersForget hPi hPe R
  algebraize [f.hom]
  have : PreservesLimit (K ⋙ Under.forget (toMorphismProperty P) ⊤ R)
      (CategoryTheory.Under.pushout f) := by
    convert preservesLimit_of_natIso _ (tensorProdIsoPushout R S)
    convert preservesLimit_of_iso_diagram _ (diagramIsoParallelPair _).symm
    apply preservesLimit_parallelPair_tensorProd_of_hasStableEqualizers hPse
    exact (K.obj _).prop
    exact (K.obj _).prop
  have : PreservesLimit K (Under.pushout (toMorphismProperty P) ⊤ f ⋙
        Under.forget (toMorphismProperty P) ⊤ S) := by
    show PreservesLimit K (Under.forget (toMorphismProperty P) ⊤ R ⋙ Under.pushout f)
    infer_instance
  apply CategoryTheory.Limits.preservesLimit_of_reflects_of_preserves _
    (MorphismProperty.Under.forget _ ⊤ S)

/-- If `P` is a property of ring homs that is stable under finite products and
equalizers, and the latter are preserved by arbitrary base change,
pushout along any ring homomorphism preserves finite limits. -/
lemma preservesFiniteLimits_pushout_of_hasStableEqualizers (hPi : RingHom.RespectsIso P)
    (hPp : HasFiniteProducts P) (hPe : HasEqualizers P) (hPse : HasStableEqualizers P)
    [(toMorphismProperty P).IsStableUnderCobaseChange] {R S : CommRingCat.{u}} (f : R ⟶ S) :
    PreservesFiniteLimits (Under.pushout (toMorphismProperty P) ⊤ f) :=
  have := preservesFiniteProducts_pushout hPi hPp f
  have := preservesEqualizers_pushout_of_hasStableEqualizers hPi hPe hPse f
  have := Under.hasFiniteLimits hPi hPp hPe
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts _

end CommRingCat
