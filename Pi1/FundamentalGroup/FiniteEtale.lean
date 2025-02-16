/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Pi1.Mathlib.CategoryTheory.MorphismProperty.Composition
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.Etale
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.Finite
import Pi1.FundamentalGroup.AffineColimits

/-!
# Finite étale morphisms

We say a morphism is finite étale if it is finite and étale. The category `FiniteEtale X` is
the category of finite etale schemes over `X`.
-/

universe u

open CategoryTheory Limits

namespace RingHom

variable (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

-- TODO: reformulate these with ringhoms?

/-- A property of ring homomorphisms `Q` is said to have equalizers, if the equalizer of algebra maps
between algebras satisfiying `Q` also satisfies `Q`. -/
def HasEqualizers (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop) : Prop :=
  ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f g : S →ₐ[R] T), Q (algebraMap R S) → Q (algebraMap R T) →
      Q (algebraMap R (AlgHom.equalizer f g))

def HasProducts (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop) : Prop :=
  ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T],
    Q (algebraMap R S) → Q (algebraMap R T) → Q (algebraMap R (S × T))

end RingHom

namespace AlgebraicGeometry

/-- A morphism is finite étale if it is finite and étale. -/
@[mk_iff]
class IsFiniteEtale {X Y : Scheme.{u}} (f : X ⟶ Y) extends IsFinite f, IsEtale f : Prop

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

/-- The forgetful functor from schemes finite étale over `X` to schemes over `X` is fully faithful. -/
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

instance : HasFiniteColimits (Affine X) := sorry

instance : HasFiniteColimits (FiniteEtale X) :=
  sorry

lemma mono_iff (f g : FiniteEtale X) (i : f ⟶ g) :
    Mono i ↔ IsOpenImmersion i.hom.left ∧ IsClosedImmersion i.hom.left :=
  sorry

end FiniteEtale

variable {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
variable (P : MorphismProperty Scheme.{u}) [HasAffineProperty P (affineAnd Q)]

namespace AffineAnd

open MorphismProperty

variable {X : Scheme.{u}}

instance (f : P.Over ⊤ X) : IsAffineHom f.hom :=
  HasAffineProperty.affineAnd_le_isAffineHom P inferInstance _ f.2

def toAffine (X : Scheme.{u}) : P.Over ⊤ X ⥤ Affine X where
  obj f := ⟨f.toComma, inferInstance⟩
  map f := ⟨f.toCommaMorphism, trivial, trivial⟩

def toAffineFullyFaithful (X : Scheme.{u}) : (toAffine P X).FullyFaithful where
  preimage f := ⟨f.toCommaMorphism, trivial, trivial⟩

instance : (toAffine P X).Faithful := (toAffineFullyFaithful P X).faithful
instance : (toAffine P X).Full := (toAffineFullyFaithful P X).full

variable [P.IsStableUnderBaseChange]

theorem hasFiniteColimits (hQp : RingHom.HasProducts Q) (hQe : RingHom.HasEqualizers Q) :
    HasFiniteColimits (P.Over ⊤ X) :=
  sorry

theorem preservesFiniteColimits_pullback (hQp : RingHom.HasProducts Q)
    (hQe : RingHom.HasEqualizers Q) {Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    PreservesFiniteColimits (MorphismProperty.Over.pullback P ⊤ f) :=
  sorry

end AffineAnd

end AlgebraicGeometry
