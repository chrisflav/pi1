import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.LocalProperties.Exactness

lemma RingHom.Bijective.stableUnderComposition :
    RingHom.StableUnderComposition (fun f ↦ Function.Bijective f) :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hg.comp hf

lemma RingHom.Bijective.respectsIso :
    RingHom.RespectsIso (fun f ↦ Function.Bijective f) :=
  RingHom.Bijective.stableUnderComposition.respectsIso fun e ↦ e.bijective

lemma RingHom.Bijective.ofLocalizationSpan :
    RingHom.OfLocalizationSpan (fun f ↦ Function.Bijective f) := by
  introv R hs hf
  algebraize [f]
  let f' (r : s) :=
    (IsScalarTower.toAlgHom R S (Localization.Away (Algebra.ofId R S <| r.val))).toLinearMap
  have (r : s) : IsLocalizedModule (Submonoid.powers r.val) (f' r) := by
    rw [isLocalizedModule_iff_isLocalization]
    have : Algebra.algebraMapSubmonoid S (.powers r.val) = .powers (Algebra.ofId R S <| r.val) :=
      Submonoid.map_powers _ r.val
    rw [this]
    infer_instance
  apply bijective_of_isLocalized_span s hs (F := Algebra.linearMap R S)
    (fun x : s ↦ Localization.Away x.val) (fun x : s ↦ Algebra.linearMap _ _) _ f'
  intro r
  let fr := (Localization.awayMapₐ (Algebra.ofId R S) r.val).toLinearMap
  have heq :
      (IsLocalizedModule.map (.powers r.val) (Algebra.linearMap R (Localization.Away r.val))
      (f' r))
        (Algebra.linearMap R S) =
        (Localization.awayMapₐ (Algebra.ofId R S) r.val).toLinearMap := by
    apply IsLocalizedModule.linearMap_ext (.powers r.val)
      (f := (Algebra.linearMap R (Localization.Away r.val)))
      (f' := f' r)
    rw [IsLocalizedModule.map_comp]
    ext
    simp [f']
  rw [heq]
  exact hf r
