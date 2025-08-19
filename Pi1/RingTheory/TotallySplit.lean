/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Pi1.RingTheory.FinitePresentation
import Pi1.RingTheory.RankAtStalk
import Pi1.RingTheory.SmoothFlat
import Pi1.Mathlib.RingTheory.TensorProduct.Basic
import Pi1.Mathlib.RingTheory.Etale.Basic
import Pi1.Mathlib.RingTheory.Unramified.Basic

/-!
# Totally split algebras

An `R`-algebra `S` is totally split of rank `n` if it is isomorphic to `Fin n → R`. Geometrically,
this corresponds to a trivial covering.

Every totally split algebra is finite étale and conversely, every finite étale covering is étale
locally totally split.
-/

open TensorProduct

universe u v

open IsLocalRing

/-- `S` is an `R`-algebra split of rank `n` if `S` is isomorphic to `Fin n → R`.
Geometrically, this is a trivial cover of degree `n`. -/
class Algebra.IsSplitOfRank (n : outParam ℕ) (R S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] : Prop where
  nonempty_algEquiv_fun' : Nonempty (S ≃ₐ[R] Fin n → R)

namespace Algebra.IsSplitOfRank

section

variable {n : ℕ}
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

variable (n R S) in
lemma nonempty_algEquiv_fun [IsSplitOfRank n R S] : Nonempty (S ≃ₐ[R] Fin n → R) :=
  nonempty_algEquiv_fun'

instance {T : Type*} [CommRing T] [Algebra R T] [IsSplitOfRank n R S] :
    IsSplitOfRank n T (T ⊗[R] S) := by
  obtain ⟨e⟩ := Algebra.IsSplitOfRank.nonempty_algEquiv_fun n R S
  refine ⟨⟨?_⟩⟩
  exact (Algebra.TensorProduct.congr AlgEquiv.refl e).trans
    ((Algebra.TensorProduct.piRight R T T (fun _ : Fin n ↦ R)).trans <|
      AlgEquiv.piCongrRight fun i ↦ TensorProduct.rid R T T)

lemma of_equiv {S' : Type*} [CommRing S'] [Algebra R S'] (e : S ≃ₐ[R] S') [IsSplitOfRank n R S] :
    IsSplitOfRank n R S' := by
  obtain ⟨f⟩ := nonempty_algEquiv_fun n R S
  exact ⟨⟨e.symm.trans f⟩⟩

lemma iff_subsingleton_of_isEmpty (hn : n = 0) :
    IsSplitOfRank n R S ↔ Subsingleton S := by
  subst hn
  exact ⟨fun ⟨⟨e⟩⟩ ↦ e.subsingleton, fun hs ↦ ⟨⟨default⟩⟩⟩

lemma of_card_eq {ι : Type*} [Finite ι] (h : Nat.card ι = n) (e : S ≃ₐ[R] ι → R) :
    IsSplitOfRank n R S := by
  cases nonempty_fintype ι
  let f : (ι → R) ≃ₐ[R] (Fin n → R) := AlgEquiv.piCongrLeft' _ _
    (Fintype.equivOfCardEq (by simpa using h))
  refine ⟨⟨e.trans f⟩⟩

lemma of_subsingleton [Subsingleton R] : IsSplitOfRank n R S := by
  have : Subsingleton S := RingHom.codomain_trivial (algebraMap R S)
  exact ⟨⟨default⟩⟩

instance [Algebra.IsSplitOfRank n R S] : Module.Free R S := by
  obtain ⟨e⟩ := nonempty_algEquiv_fun n R S
  exact Module.Free.of_equiv e.symm.toLinearEquiv

lemma finrank_eq [Nontrivial R] [Algebra.IsSplitOfRank n R S] : Module.finrank R S = n := by
  obtain ⟨e⟩ := nonempty_algEquiv_fun n R S
  simp [e.toLinearEquiv.finrank_eq]

lemma rankAtStalk_eq [Nontrivial R] [Algebra.IsSplitOfRank n R S] :
    Module.rankAtStalk (R := R) S = n := by
  rw [Module.rankAtStalk_eq_finrank_of_free, finrank_eq]

instance [Algebra.IsSplitOfRank n R S] : Module.FinitePresentation R S := by
  obtain ⟨e⟩ := nonempty_algEquiv_fun n R S
  apply Module.FinitePresentation.of_equiv e.symm.toLinearEquiv

end

section

variable {n : ℕ} {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

instance [IsSplitOfRank n R S] : Etale R S := by
  obtain ⟨e⟩ := Algebra.IsSplitOfRank.nonempty_algEquiv_fun n R S
  exact Algebra.Etale.of_equiv e.symm

/-- If `S` is finite étale over `R` of (constant) rank `n`, there exists
a faithfully flat, étale `R`-algebra `T` such that `T ⊗[R] S` is split of rank `n`
over `T`. -/
lemma exists_isSplitOfRank_tensorProduct [Etale R S] [Module.Finite R S] {n : ℕ}
    (hn : Module.rankAtStalk (R := R) S = n) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Module.FaithfullyFlat R T)
      (_ : Algebra.Etale R T),
      IsSplitOfRank n T (T ⊗[R] S) := by
  induction n generalizing R S with
  | zero =>
      use R, inferInstance, inferInstance, inferInstance, inferInstance
      let e : R ⊗[R] S ≃ₐ[R] S := TensorProduct.lid R S
      have : IsSplitOfRank 0 R S := by
        rw [iff_subsingleton_of_isEmpty]
        simp only [Nat.cast_zero] at hn
        rwa [Module.rankAtStalk_eq_zero_iff_subsingleton] at hn
        rfl
      apply IsSplitOfRank.of_equiv e.symm
  | succ n ih =>
      cases subsingleton_or_nontrivial R
      · use R, inferInstance, inferInstance, inferInstance, inferInstance
        have : IsSplitOfRank (n + 1) R S := .of_subsingleton
        apply IsSplitOfRank.of_equiv (TensorProduct.lid R S).symm
      have : Nontrivial S := by
        apply Module.nontrivial_of_rankAtStalk_pos (R := R)
        simp [hn]
      obtain ⟨U, _, _, ⟨e⟩⟩ := Algebra.FormallyUnramified.exists_algEquiv_prod R S
      algebraize [RingHom.snd S U]
      have : IsScalarTower S (S × U) U := IsScalarTower.of_algebraMap_eq' rfl
      have : Etale S U := by
        have : Etale S (S × U) := Etale.of_equiv e
        apply Etale.comp S (S × U) U
      have : Module.Finite S U := by
        have : Module.Finite S (S × U) := Module.Finite.equiv e.toLinearEquiv
        have : Module.Finite (S × U) U :=
          Module.Finite.of_surjective (Algebra.linearMap (S × U) U) (RingHom.snd S U).surjective
        apply Module.Finite.trans (S × U)
      have (p : PrimeSpectrum S) : Module.rankAtStalk (R := S) (S × U) p = n + 1 := by
        rw [Module.rankAtStalk_eq_of_equiv e.symm.toLinearEquiv]
        simp [Module.rankAtStalk_baseChange, hn]
      simp_rw [Module.rankAtStalk_prod , Module.rankAtStalk_self, Pi.add_apply,
        Pi.one_apply] at this
      have : Module.rankAtStalk (R := S) U = n := by
        ext p
        simp only [Pi.natCast_def, Nat.cast_id]
        have := this p
        omega
      obtain ⟨V, _, _, _, _, hV⟩ := ih this
      obtain ⟨f⟩ := hV.nonempty_algEquiv_fun
      algebraize [(algebraMap S V).comp (algebraMap R S)]
      let e₁ : V ⊗[R] S ≃ₐ[V] V ⊗[S] (S ⊗[R] S) :=
        (Algebra.TensorProduct.cancelBaseChange R S V V S).symm
      let e₂ : V ⊗[S] (S ⊗[R] S) ≃ₐ[V] V ⊗[S] (S × U) :=
        TensorProduct.congr AlgEquiv.refl e
      let e₃ : V ⊗[S] (S × U) ≃ₐ[V] V ⊗[S] S × V ⊗[S] U :=
        TensorProduct.prodRight S V V S U
      let e₄ : (V ⊗[S] S × V ⊗[S] U) ≃ₐ[V] V × (Fin n → V) :=
        AlgEquiv.prodCongr (TensorProduct.rid S V V) f
      let e₅ : (V × (Fin n → V)) ≃ₐ[V] (Unit ⊕ Fin n) → V :=
        AlgEquiv.trans (AlgEquiv.prodCongr (AlgEquiv.funUnique _ _ _).symm AlgEquiv.refl)
          (AlgEquiv.sumArrowEquivProdArrow Unit (Fin n) V V).symm
      let e := e₁.trans <| e₂.trans <| e₃.trans <| e₄.trans e₅
      refine ⟨V, inferInstance, inferInstance, ?_, ?_, ?_⟩
      · have : Module.FaithfullyFlat R S := by
          apply Module.FaithfullyFlat.of_specComap_surjective
          rw [← Algebra.rankAtStalk_pos_iff_specComap_surjective]
          intro p
          simp [hn]
        exact Module.FaithfullyFlat.trans R S V
      · exact Algebra.Etale.comp R S V
      · exact IsSplitOfRank.of_card_eq (ι := Unit ⊕ Fin n) (by simp [add_comm]) e

end

end Algebra.IsSplitOfRank
