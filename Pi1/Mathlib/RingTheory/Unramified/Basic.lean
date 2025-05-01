import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Unramified.Basic
import Pi1.Mathlib.Algebra.Algebra.Pi
import Pi1.Mathlib.RingTheory.Idempotents

universe u

open TensorProduct

/-- If `S` is an unramified `R`-algebra, `S ⊗[R] S` splits as `S × T` for some `R`-algebra `T`.
In particular, the diagonal is an open and closed immersion. -/
lemma Algebra.FormallyUnramified.exists_algEquiv_prod (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra S T), Nonempty (S ⊗[R] S ≃ₐ[S] S × T) := by
  obtain ⟨e, he, hsp⟩ := (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg R S)).mp
    ((Ideal.cotangent_subsingleton_iff _).mp (inferInstanceAs <| Subsingleton (Ω[S⁄R])))
  let e₁ := AlgEquiv.prodQuotientOfIsIdempotentElem (R := S) he he.one_sub
    (by simp [he]) (by simp [he])
  let e₂ : (S ⊗[R] S ⧸ Ideal.span {e}) ≃ₐ[S] S :=
    ((Ideal.span {e}).quotientEquivAlgOfEq S hsp.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective <|
      fun x ↦ by use x ⊗ₜ 1; simp [Algebra.TensorProduct.lmul''])
  exact ⟨(S ⊗[R] S) ⧸ Ideal.span {1 - e}, inferInstance, inferInstance,
    ⟨e₁.trans (.prodCongr e₂ .refl)⟩⟩
