/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Constructors
import Mathlib.Topology.LocalAtTarget

/-!
# Universally open morphism

A morphism of schemes `f : X ⟶ Y` is universally open if `X ×[Y] Y' ⟶ Y'` is an open map
for all base change `Y' ⟶ Y`.

We show that being universally open is local at the target, and is stable under compositions and
base changes.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open CategoryTheory.MorphismProperty

/-- A morphism of schemes `f : X ⟶ Y` is universally open if the base change `X ×[Y] Y' ⟶ Y'`
along any morphism `Y' ⟶ Y` is (topologically) a open map.
-/
@[mk_iff]
class UniversallyOpen (f : X ⟶ Y) : Prop where
  out : universally (topologically @IsOpenMap) f

lemma Scheme.Hom.isOpenMap {X Y : Scheme} (f : X.Hom Y) [UniversallyOpen f] :
    IsOpenMap f.base := UniversallyOpen.out _ _ _ IsPullback.of_id_snd

theorem universallyOpen_eq : @UniversallyOpen = universally (topologically @IsOpenMap) := by
  ext X Y f; rw [universallyOpen_iff]

instance (priority := 900) [IsOpenImmersion f] : UniversallyOpen f := by
  rw [universallyOpen_eq]
  intro X' Y' i₁ i₂ f' hf
  have hf' : IsOpenImmersion f' := MorphismProperty.of_isPullback hf.flip inferInstance
  exact f'.isOpenEmbedding.isOpenMap

theorem universallyOpen_respectsIso : RespectsIso @UniversallyOpen :=
  universallyOpen_eq.symm ▸ universally_respectsIso (topologically @IsOpenMap)

instance universallyOpen_isStableUnderBaseChange : IsStableUnderBaseChange @UniversallyOpen :=
  universallyOpen_eq.symm ▸ universally_isStableUnderBaseChange (topologically @IsOpenMap)

instance : IsStableUnderComposition (topologically @IsOpenMap) where
  comp_mem f g hf hg := IsOpenMap.comp (f := f.base) (g := g.base) hg hf

instance universallyOpen_isStableUnderComposition :
    IsStableUnderComposition @UniversallyOpen := by
  rw [universallyOpen_eq]
  infer_instance

instance {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : UniversallyOpen f] [hg : UniversallyOpen g] : UniversallyOpen (f ≫ g) :=
  comp_mem _ _ _ hf hg

instance : MorphismProperty.IsMultiplicative @UniversallyOpen where
  id_mem _ := inferInstance

instance universallyOpen_fst {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hg : UniversallyOpen g] :
    UniversallyOpen (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g hg

instance universallyOpen_snd {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hf : UniversallyOpen f] :
    UniversallyOpen (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g hf

instance universallyOpen_isLocalAtTarget : IsLocalAtTarget @UniversallyOpen := by
  rw [universallyOpen_eq]
  apply universally_isLocalAtTarget
  intro X Y f ι U hU H
  simp_rw [topologically, morphismRestrict_base] at H
  exact hU.isOpenMap_iff_restrictPreimage.mpr H

end AlgebraicGeometry
