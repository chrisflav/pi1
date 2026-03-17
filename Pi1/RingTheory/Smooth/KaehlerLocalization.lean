/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Extension.Presentation.Basic
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Extension.Cotangent.LocalizationAway
import Mathlib.RingTheory.Kaehler.JacobiZariski

/-!
# Cotangent and localization away

In this file we use the Jacobi-Zariski sequence to show some results
where `R → S → T` is such that `T` is the localization of `S` away from one
element, where `S` is generated over `R` by `P` with kernel `I` and `Q` is the
canonical `S`-presentation of `T`.

## Main results

- `Algebra.Generators.liftBaseChange_injective`: The map `T ⊗[S] (I⧸I²)` is injective.

-/

open TensorProduct MvPolynomial

namespace Algebra.Generators

variable {R S T : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable {ι σ : Type*}
variable (g : S) [IsLocalization.Away g T] (P : Generators R S ι)

lemma MvPolynomial.coeff_def {σ R : Type*} [CommSemiring R] (m : σ →₀ ℕ) (p : MvPolynomial σ R) :
    MvPolynomial.coeff m p = @DFunLike.coe ((σ →₀ ℕ) →₀ R) _ _ _ p m :=
  rfl

lemma foo (σ A B) [AddMonoid A] [AddCommMonoid B] (f₁ f₂ : σ) (g₁ g₂ : A) (F : σ → A → B)
    (H : f₁ ≠ f₂) (HF : ∀ f, F f 0 = 0) :
    Finsupp.sum (Finsupp.single f₁ g₁ + Finsupp.single f₂ g₂) F = F f₁ g₁ + F f₂ g₂ := by
  classical
  by_cases hg₁ : g₁ = 0
  · simp [hg₁, HF]
  by_cases hg₂ : g₂ = 0
  · simp [hg₂, HF]
  have : (Finsupp.single f₁ g₁ + Finsupp.single f₂ g₂).support = {f₁, f₂} := by
    ext a
    simp only [Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply, ne_eq, Finset.mem_insert,
      Finset.mem_singleton, Finsupp.single_apply]
    split_ifs <;> aesop
  simp [Finsupp.sum, this, H, H.symm]

lemma relation_comp_localizationAway_inl (P : Presentation R S ι σ)
    (h1 : P.σ (-1) = -1) (h0 : P.σ 0 = 0) (r) :
    ((Presentation.localizationAway T g).comp P).relation (Sum.inl r) =
      rename Sum.inr (P.σ g) * X (Sum.inl ()) - 1 := by
  classical
  simp only [Presentation.comp, Sum.elim_inl]
  show Finsupp.sum _ _ = _
  simp only [Presentation.localizationAway_relation]
  rw [sub_eq_add_neg, C_mul_X_eq_monomial, ← map_one C, ← map_neg C]
  refine (foo _ _ _ (Finsupp.single () 1) 0 g (-1 : S) _ ?_ ?_).trans ?_
  · simp
  · simp [h0]
  · simp only [Finsupp.mapDomain_single, h1, map_neg, map_one, Finsupp.mapDomain_zero,
      monomial_zero', mul_one, sub_eq_add_neg, add_left_inj]
    rfl

end Algebra.Generators
