/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Pi1.Mathlib.RingTheory.RingHom.Etale
import Pi1.FundamentalGroup.AffineAnd
import Pi1.RingTheory.StableProperties
import Pi1.RingTheory.FiniteEtale.Equalizer
import Pi1.RingTheory.KerTensor

/-!
# Finite étale morphisms

We say a morphism is finite étale if it is finite and étale. The category `FiniteEtale X` is
the category of finite etale schemes over `X`.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace Algebra

end Algebra

namespace RingHom

/-- A ring homomorphism is finite étale if the induced algebra is finite étale. -/
def FiniteEtale {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.FiniteEtale R S

lemma finiteEtale_algebraMap_iff {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap R S).FiniteEtale ↔ Algebra.FiniteEtale R S := by
  simp only [RingHom.FiniteEtale]
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

namespace FiniteEtale

lemma iff_finite_and_etale
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    f.FiniteEtale ↔ f.Etale ∧ f.Finite := by
  rw [FiniteEtale, Finite, Etale]
  rw [Algebra.finiteEtale_iff]

lemma eq_and :
    @FiniteEtale = (fun R S (_ : CommRing R) (_ : CommRing S) f ↦ f.Etale ∧ f.Finite) := by
  ext
  rw [iff_finite_and_etale]

lemma isStableUnderBaseChange : IsStableUnderBaseChange FiniteEtale := by
  rw [eq_and]
  exact Etale.isStableUnderBaseChange.and finite_isStableUnderBaseChange

lemma respectsIso : RespectsIso FiniteEtale := by
  rw [eq_and]
  apply Etale.respectsIso.and finite_respectsIso

lemma hasFiniteProducts : HasFiniteProducts FiniteEtale := by
  introv R _ hf
  simp_rw [finiteEtale_algebraMap_iff] at hf ⊢
  constructor

lemma hasEqualizers : HasEqualizers FiniteEtale := by
  introv R hS hT
  rw [finiteEtale_algebraMap_iff] at hS hT ⊢
  apply Algebra.Etale.equalizer

lemma hasStableEqualizers : HasStableEqualizers FiniteEtale := by
  introv R hA hB
  rw [finiteEtale_algebraMap_iff] at hA hB
  exact Algebra.tensorEqualizer_bijective_of_finite_of_etale f g

instance : (toMorphismProperty RingHom.FiniteEtale).IsStableUnderCobaseChange := by
  rw [isStableUnderCobaseChange_toMorphismProperty_iff]
  exact isStableUnderBaseChange

end FiniteEtale

end RingHom

namespace AlgebraicGeometry

/-- A morphism is finite étale if it is finite and étale. -/
@[mk_iff]
class IsFiniteEtale {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop
  extends IsFinite f, IsEtale f

namespace IsFiniteEtale

open MorphismProperty

lemma eq_inf : @IsFiniteEtale = (@IsFinite ⊓ @IsEtale : MorphismProperty Scheme.{u}) := by
  ext f
  rw [isFiniteEtale_iff]
  rfl

instance : IsMultiplicative @IsFiniteEtale := by
  rw [eq_inf]
  infer_instance

instance : IsStableUnderBaseChange @IsFiniteEtale := by
  rw [eq_inf]
  infer_instance

instance : HasOfPostcompProperty @IsFiniteEtale @IsFiniteEtale := by
  have : HasOfPostcompProperty @IsEtale (@IsFinite ⊓ @IsEtale) := by
    apply HasOfPostcompProperty.of_le (Q := @IsEtale) (W := @IsEtale)
    exact inf_le_right
  have : HasOfPostcompProperty @IsFinite (@IsFinite ⊓ @IsEtale) := by
    apply HasOfPostcompProperty.of_le (Q := @IsFinite) (W := @IsFinite)
    exact inf_le_left
  rw [eq_inf]
  infer_instance

instance : HasAffineProperty @IsFiniteEtale (affineAnd RingHom.FiniteEtale) := by
  rw [HasAffineProperty.iff, eq_inf]
  constructor
  · infer_instance
  · ext X Y f _
    simp only [affineAnd_apply, RingHom.FiniteEtale.iff_finite_and_etale]
    show _ ↔ IsFinite f ∧ IsEtale f
    simp only [HasAffineProperty.iff_of_isAffine (P := @IsFinite), and_assoc, and_congr_right_iff]
    intro h
    rw [HasRingHomProperty.iff_of_isAffine (P := @IsEtale)]
    rw [RingHom.Etale.iff_locally_isStandardSmoothOfRelativeDimension, and_comm]

instance {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsFiniteEtale f] [IsFiniteEtale g] :
    IsFiniteEtale (f ≫ g) where

lemma mono_iff {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFiniteEtale f] :
    Mono f ↔ IsOpenImmersion f ∧ IsClosedImmersion f := by
  refine ⟨fun hf ↦ ⟨inferInstance, ?_⟩, fun ⟨hfo, _⟩ ↦ inferInstance⟩
  · rw [IsClosedImmersion.iff_isFinite_and_mono]
    exact ⟨inferInstance, inferInstance⟩

end IsFiniteEtale

/-- The category of schemes finite étale over `X`. -/
def FiniteEtale (X : Scheme.{u}) : Type _ :=
  MorphismProperty.Over @IsFiniteEtale ⊤ X

namespace FiniteEtale

variable (X : Scheme.{u})

instance : Category (FiniteEtale X) :=
  inferInstanceAs <| Category (MorphismProperty.Over @IsFiniteEtale ⊤ X)

/-- The forgetful functor from schemes finite étale over `X` to schemes over `X`. -/
def forget : FiniteEtale X ⥤ Over X :=
  MorphismProperty.Over.forget @IsFiniteEtale ⊤ X

/-- The forgetful functor from schemes finite étale over `X` to schemes over `X` is fully
faithful. -/
def forgetFullyFaithful : (FiniteEtale.forget X).FullyFaithful :=
  MorphismProperty.Comma.forgetFullyFaithful _ _ _

instance : (FiniteEtale.forget X).Full :=
  inferInstanceAs <| (MorphismProperty.Comma.forget _ _ _ _ _).Full
instance : (FiniteEtale.forget X).Faithful :=
  inferInstanceAs <| (MorphismProperty.Comma.forget _ _ _ _ _).Faithful

instance : HasTerminal (FiniteEtale X) := by
  unfold FiniteEtale
  infer_instance

instance : HasPullbacks (FiniteEtale X) := by
  unfold FiniteEtale
  infer_instance

instance (f : FiniteEtale X) : IsFiniteEtale f.hom := f.2

/-- The forgetful functor to the category of schemes affine over `X`. -/
def toAffine : FiniteEtale X ⥤ Affine X where
  obj f := ⟨f.toComma, inferInstance⟩
  map {X Y} f := ⟨f.toCommaMorphism, trivial, trivial⟩

def toAffineFullyFaithful : (toAffine X).FullyFaithful where
  preimage f := ⟨f.toCommaMorphism, trivial, trivial⟩

instance : (toAffine X).Faithful := (toAffineFullyFaithful X).faithful
instance : (toAffine X).Full := (toAffineFullyFaithful X).full

instance : HasFiniteColimits (FiniteEtale X) :=
  AffineAnd.hasFiniteColimits _
    RingHom.FiniteEtale.respectsIso
    RingHom.FiniteEtale.hasFiniteProducts
    RingHom.FiniteEtale.hasEqualizers

instance (f g : FiniteEtale X) (i : f ⟶ g) : IsFiniteEtale i.hom.left := by
  apply MorphismProperty.of_postcomp @IsFiniteEtale (W' := @IsFiniteEtale) _ g.hom
  · infer_instance
  · simp only [Functor.const_obj_obj, Functor.id_obj, Over.w]
    infer_instance

lemma mono_iff (f g : FiniteEtale X) (i : f ⟶ g) :
    Mono i ↔ IsOpenImmersion i.hom.left ∧ IsClosedImmersion i.hom.left := by
  rw [← IsFiniteEtale.mono_iff]
  refine ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
  · exact (MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).map_mono _
  · exact (MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).mono_of_mono_map hi

variable {X}

abbrev pullback {Y : Scheme.{u}} (f : X ⟶ Y) : FiniteEtale Y ⥤ FiniteEtale X :=
  MorphismProperty.Over.pullback _ _ f

def mk {T : Scheme.{u}} (f : T ⟶ X) [IsFiniteEtale f] : FiniteEtale X :=
  MorphismProperty.Over.mk ⊤ f inferInstance

@[simp]
lemma mk_hom {T : Scheme.{u}} (f : T ⟶ X) [IsFiniteEtale f] : (mk f).hom = f := rfl

@[simp]
lemma mk_left {T : Scheme.{u}} (f : T ⟶ X) [IsFiniteEtale f] : (mk f).left = T := rfl

open RingHom in
instance {Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (pullback f) := by
  have (R S : CommRingCat.{u}) (f : R ⟶ S) :
      PreservesFiniteLimits (MorphismProperty.Under.pushout
        (RingHom.toMorphismProperty RingHom.FiniteEtale) ⊤ f) := by
    apply CommRingCat.preservesFiniteLimits_pushout_of_hasStableEqualizers
    · exact FiniteEtale.respectsIso
    · exact FiniteEtale.hasFiniteProducts
    · exact FiniteEtale.hasEqualizers
    · exact FiniteEtale.hasStableEqualizers
  apply AffineAnd.preservesFiniteColimits_pullback
  · exact FiniteEtale.respectsIso
  · exact FiniteEtale.hasFiniteProducts
  · exact FiniteEtale.hasEqualizers

end FiniteEtale

