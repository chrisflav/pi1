import Mathlib
import Pi1.Mathlib.CategoryTheory.MorphismProperty.Limits
import Pi1.Mathlib.RingTheory.RingHomProperties

universe u

open TensorProduct CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable (P P' : MorphismProperty Scheme.{u})

lemma foobar [P.IsStableUnderBaseChange]
    [(MorphismProperty.isomorphisms Scheme.{u}).DescendsAlong P]
    {R S : CommRingCat.{u}} (φ : R ⟶ S) {X : Scheme.{u}}
    (f : X ⟶ Spec R) [IsAffine (pullback f (Spec.map φ))] (hφ : P (Spec.map φ)) :
    IsAffine X := by
  let sX := X.toSpecΓ
  let sX' := (pullback f (Spec.map φ)).isoSpec
  let u : Spec Γ(X, ⊤) ⟶ Spec R :=
    Spec.map <| ((ΓSpec.adjunction.homEquiv _ _).symm f).unop
  let u' : Spec Γ(pullback f (Spec.map φ), ⊤) ⟶ Spec S :=
    Spec.map <| ((ΓSpec.adjunction.homEquiv _ _).symm <| pullback.snd _ _).unop
  have h1 : f = sX ≫ u := sorry
  have h2 : pullback.snd _ _ = sX'.hom ≫ u' := sorry
  let h' : Spec Γ(pullback f (Spec.map φ), ⊤) ⟶ Spec Γ(X, ⊤) :=
    Spec.map (pullback.fst f (Spec.map φ)).appTop
  have H₁ : IsPullback u' h' (Spec.map φ) u := by
    -- there is a proof in http://math.stanford.edu/~conrad/216APage/handouts/fpqc.pdf, Lemma 15
    -- but need `φ` flat and `f` qc-qs
    sorry
  have hh : P h' := by
    apply P.of_isPullback
    exact H₁
    exact hφ
  have H₂ : IsPullback sX'.hom (pullback.fst _ _) h' sX := by
    apply IsPullback.of_right (h₁₂ := u') (h₂₂ := u) (v₁₃ := Spec.map φ)
    · rw [← h2, ← h1]
      exact IsPullback.flip (IsPullback.of_hasPullback f (Spec.map φ))
    · sorry
    · exact H₁
  constructor
  apply (MorphismProperty.isomorphisms Scheme.{u}).of_isPullback_of_descendsAlong (Q := P)
  exact H₂
  exact hh
  exact inferInstanceAs <| IsIso sX'.hom

end AlgebraicGeometry
