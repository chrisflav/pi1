/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Properties of ring homomorphisms formed by conjunction

-/

universe u

namespace RingHom

variable {P Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

lemma OfLocalizationSpanTarget.and (hP : OfLocalizationSpanTarget P)
    (hQ : OfLocalizationSpanTarget Q) :
    OfLocalizationSpanTarget (fun f ↦ P f ∧ Q f) := by
  introv R hs hf
  exact ⟨hP f s hs fun r ↦ (hf r).1, hQ f s hs fun r ↦ (hf r).2⟩

lemma OfLocalizationSpan.and (hP : OfLocalizationSpan P) (hQ : OfLocalizationSpan Q) :
    OfLocalizationSpan (fun f ↦ P f ∧ Q f) := by
  introv R hs hf
  exact ⟨hP f s hs fun r ↦ (hf r).1, hQ f s hs fun r ↦ (hf r).2⟩

lemma LocalizationAwayPreserves.and (hP : LocalizationAwayPreserves P)
    (hQ : LocalizationAwayPreserves Q) :
    LocalizationAwayPreserves (fun f ↦ P f ∧ Q f) := by
  introv R h
  exact ⟨hP f r R' S' h.1, hQ f r R' S' h.2⟩

lemma StableUnderCompositionWithLocalizationAwayTarget.and
    (hP : StableUnderCompositionWithLocalizationAwayTarget P)
    (hQ : StableUnderCompositionWithLocalizationAwayTarget Q) :
    StableUnderCompositionWithLocalizationAwayTarget (fun f ↦ P f ∧ Q f) := by
  introv R h hf
  exact ⟨hP T s f hf.1, hQ T s f hf.2⟩

lemma StableUnderComposition.and (hP : StableUnderComposition P) (hQ : StableUnderComposition Q) :
    StableUnderComposition (fun f ↦ P f ∧ Q f) := by
  introv R hf hg
  exact ⟨hP f g hf.1 hg.1, hQ f g hf.2 hg.2⟩

lemma RespectsIso.and (hP : RespectsIso P) (hQ : RespectsIso Q) :
    RespectsIso (fun f ↦ P f ∧ Q f) := by
  refine ⟨?_, ?_⟩
  · introv hf
    exact ⟨hP.1 f e hf.1, hQ.1 f e hf.2⟩
  · introv hf
    exact ⟨hP.2 f e hf.1, hQ.2 f e hf.2⟩

lemma PropertyIsLocal.and (hP : PropertyIsLocal P) (hQ : PropertyIsLocal Q) :
    PropertyIsLocal (fun f ↦ P f ∧ Q f) where
  localizationAwayPreserves := hP.localizationAwayPreserves.and hQ.localizationAwayPreserves
  ofLocalizationSpanTarget := hP.ofLocalizationSpanTarget.and hQ.ofLocalizationSpanTarget
  ofLocalizationSpan := hP.ofLocalizationSpan.and hQ.ofLocalizationSpan
  StableUnderCompositionWithLocalizationAwayTarget :=
    hP.StableUnderCompositionWithLocalizationAwayTarget.and
    hQ.StableUnderCompositionWithLocalizationAwayTarget

lemma IsStableUnderBaseChange.and (hP : IsStableUnderBaseChange P)
    (hQ : IsStableUnderBaseChange Q) :
    IsStableUnderBaseChange (fun f ↦ P f ∧ Q f) := by
  introv R _ h
  exact ⟨hP R S R' S' h.1, hQ R S R' S' h.2⟩

end RingHom
