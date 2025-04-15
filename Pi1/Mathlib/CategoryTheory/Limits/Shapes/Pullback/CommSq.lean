import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

namespace CategoryTheory

open Limits

lemma Limits.isPullback_map_snd_snd {C : Type*} [Category C] [HasPullbacks C]
    {X Y Z S : C} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) :
    IsPullback (pullback.map _ _ _ _ (pullback.snd f g) (pullback.snd f h) f
        pullback.condition pullback.condition)
      (pullback.fst (pullback.fst f g) (pullback.fst f h))
      (pullback.fst g h) (pullback.snd f g) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro c
    refine pullback.lift c.snd
        (pullback.lift (c.snd ≫ pullback.fst _ _) (c.fst ≫ pullback.snd _ _) ?_) ?_
    · simp [pullback.condition, ← c.condition_assoc]
    · simp
  · intro c
    apply pullback.hom_ext <;> simp [c.condition]
  · intro c
    apply pullback.hom_ext <;> simp [c.condition]
  · intro c m hfst hsnd
    apply pullback.hom_ext
    · simpa
    · apply pullback.hom_ext <;> simp [← hsnd, pullback.condition, ← hfst]

/-
pullback g.left
    (pullback.map (pullback.snd (colimit D).hom (Y.affineCover.map i)) (pullback.snd f (Y.affineCover.map i))
      (colimit D).hom f (pullback.fst (colimit D).hom (Y.affineCover.map i)) (pullback.fst f (Y.affineCover.map i))
      (Y.affineCover.map i) ⋯ ⋯)
-/
--def Limits.isPullback_map_snd_snd' {C : Type*} [Category C] [HasPullbacks C]
--    {X Y Z S T : C} (f : X ⟶ Y) (u : T ⟶ Y) (h : S ⟶ Y) (g : Z ⟶ pullback h f) :
--    IsPullback _ _ g (pullback.map (pullback.snd h u) (pullback.snd f u)
--      h f (pullback.fst h u) (pullback.fst f u)
--      u pullback.condition.symm pullback.condition.symm) :=
--  sorry

lemma Limits.isPullback_map_fst_fst {C : Type*} [Category C] [HasPullbacks C]
    {X Y Z U S : C} (f : X ⟶ S) (g : Y ⟶ S) (i : Z ⟶ S) (h : U ⟶ pullback i g) :
    IsPullback
      (pullback.map (pullback.snd f g) (h ≫ pullback.snd i g) f i
        (pullback.fst f g) (h ≫ pullback.fst i g) g
        pullback.condition.symm (by simp [pullback.condition]))
      (pullback.snd (pullback.snd f g) (h ≫ pullback.snd i g))
      (pullback.snd f i)
      (h ≫ pullback.fst i g) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro c
    exact pullback.lift (pullback.lift (c.fst ≫ pullback.fst _ _) (c.snd ≫ h ≫ pullback.snd _ _)
          (by simp [pullback.condition, c.condition_assoc])) c.snd (by simp)
  · intro c
    apply pullback.hom_ext <;> simp [c.condition]
  · intro c
    simp
  · intro c m hfst hsnd
    apply pullback.hom_ext
    · apply pullback.hom_ext
      simp [← hfst]
      simp [← hsnd, pullback.condition]
    · simpa

end CategoryTheory
