/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.RingTheory.Ideal.Maps


universe u v w t

open TensorProduct

namespace Algebra

variable {R : Type u} [CommRing R] {ι : Type v}

def MvPolynomial.coefficients (p : MvPolynomial ι R) : Set R := (p.coeff '' p.support)

lemma MvPolynomial.coefficients_mem {p : MvPolynomial ι R} (m : ι →₀ ℕ)
    (h : m ∈ MvPolynomial.support p) : p.coeff m ∈ MvPolynomial.coefficients p :=
  Set.mem_image_of_mem p.coeff h

def MvPolynomial.Set.coefficients (S : Set (MvPolynomial ι R)) : Set R :=
  Set.iUnion (ι := S) (fun (p : S) ↦ MvPolynomial.coefficients p.val)

theorem MvPolynomial.coefficients_finite (p : MvPolynomial ι R) :
    Set.Finite (MvPolynomial.coefficients p) := by
  apply Set.Finite.image
  change Set.Finite (Finsupp.support p).toSet
  rw [← Finsupp.fun_support_eq]
  exact Finsupp.finite_support p

theorem MvPolynomial.Set.coefficients_finite_of_finite (S : Set (MvPolynomial ι R))
    (hf : Set.Finite S) : Set.Finite (MvPolynomial.Set.coefficients S) := by
  letI : Finite S := hf
  apply Set.finite_iUnion
  intro p
  exact MvPolynomial.coefficients_finite p.val

lemma MvPolynomial.Set.coefficients_in (S : Set (MvPolynomial ι R))
    (p : MvPolynomial ι R) (hS : p ∈ S) :
    (MvPolynomial.coefficients p) ⊆ MvPolynomial.Set.coefficients S := by
  intro r hr
  obtain ⟨m, hms, hmeq⟩ := hr
  simp only [MvPolynomial.Set.coefficients, Set.mem_iUnion]
  use ⟨p, hS⟩
  use m

variable {S : Type w} [CommRing S]

lemma Ideal.span_preimage_le_comap (f : R →+* S) (T : Set S) :
    Ideal.span (f ⁻¹' T) ≤ Ideal.comap f (Ideal.span T) := by
  intro p hp
  induction hp using Submodule.span_induction with
  | mem x h =>
    apply Ideal.subset_span
    exact h
  | zero => simp
  | add x y _ _ hx hy => exact Ideal.add_mem _ hx hy
  | smul a x _ hx => exact Ideal.mul_mem_left _ a hx

lemma MvPolynomial.isHomogeneous_of_map (f : R →+* S) (hf : Function.Injective f)
    (p : MvPolynomial ι R) {n : ℕ} (hphomog : MvPolynomial.IsHomogeneous (MvPolynomial.map f p) n) :
    MvPolynomial.IsHomogeneous p n := by
  intro u hu
  apply hphomog
  rw [MvPolynomial.coeff_map]
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero] at hf
  intro h
  exact hu (hf _ h)

variable [Algebra R S]
  {T : Type t} [CommRing T] [Algebra R T]
  {T' : Type t} [CommRing T'] [Algebra R T']

lemma AlgHom.cancel_surjective {f g : T →ₐ[R] S} (p : T' →ₐ[R] T) (hf : Function.Surjective p)
    (heq : f.comp p = g.comp p) : f = g := by
  ext x
  obtain ⟨t', rfl⟩ := hf x
  change (f.comp p) t' = (g.comp p) t'
  rw [heq]
