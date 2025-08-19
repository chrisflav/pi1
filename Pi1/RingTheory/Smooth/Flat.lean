/-
Copyright (c) 2022 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Pi1.RingTheory.Smooth.NoetherianDescent
import Mathlib

universe u v

open TensorProduct

namespace AdicCompletion

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A)

variable (R) in
def transitionMap'ₐ {m n : ℕ} (hmn : m ≤ n) :
    A ⧸ (I ^ n) →ₐ[R] A ⧸ (I ^ m) :=
  have h : I ^ n ≤ I ^ m := Ideal.pow_le_pow_right (by omega)
  AlgHom.mk (Ideal.Quotient.factor h) (fun r ↦ by simp; rfl)

@[simp]
theorem transitionMap'ₐ_apply {m n : ℕ} (hmn : m ≤ n) (x : A) :
    transitionMap'ₐ R I hmn x = x :=
  rfl

@[simp]
lemma transitionMap'ₐ_id (n : ℕ) :
    transitionMap'ₐ R I (Nat.le_refl n) = AlgHom.id R (A ⧸ (I ^ n)) := by
  ext x
  refine Quotient.inductionOn' x (fun x ↦ ?_)
  rfl

@[simp]
lemma transitionMap'ₐ_comp {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (transitionMap'ₐ R I hmn).comp (transitionMap'ₐ R I hnk) =
      transitionMap'ₐ R I (hmn.trans hnk) := by
  ext x
  refine Quotient.inductionOn' x (fun x ↦ ?_)
  rfl

variable (R) in
def comparisonMap (n : ℕ) : (A ⧸ I ^ n) ≃ₐ[R] A ⧸ (I ^ n • ⊤ : Ideal A) :=
  Ideal.quotientEquivAlgOfEq R (by ext; simp)

theorem transitionMap_comparisonMap_apply {m n : ℕ} (hmn : m ≤ n) (x : A ⧸ I ^ n) :
    transitionMap I A hmn (comparisonMap R I n x) =
      comparisonMap R I m (transitionMap'ₐ R I hmn x) := by
  refine Quotient.inductionOn' x (fun x ↦ ?_)
  rfl

variable {B : Type*} [CommRing B] [Algebra R B]

noncomputable

def liftₐ (f : ∀ (n : ℕ), B →ₐ[R] A ⧸ (I ^ n))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), (transitionMap'ₐ R I hle).comp (f n) = f m) :
    B →ₐ[R] AdicCompletion I A where
  toFun := fun x ↦ ⟨fun n ↦ comparisonMap R I n (f n x), by
    intro m n hmn
    simp only [← h hmn, AlgHom.coe_comp, Function.comp_apply,
      transitionMap_comparisonMap_apply I hmn]⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' x y := by ext; simp
  map_mul' x y := by ext; simp
  commutes' r := by ext; simp; rfl

@[simp]
theorem evalₐ_liftₐ_apply (f : ∀ (n : ℕ), B →ₐ[R] A ⧸ (I ^ n))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), (transitionMap'ₐ R I hle).comp (f n) = f m)
    (n : ℕ) (b : B) :
    evalₐ I n (liftₐ I f h b) = f n b := by
  simp only [evalₐ, smul_eq_mul, liftₐ, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, AlgHom.coe_comp, AlgHom.coe_coe, Function.comp_apply, AlgHom.ofLinearMap_apply]
  erw [AdicCompletion.eval_apply]
  simp only
  refine Quotient.inductionOn' (f n b) (fun x ↦ ?_)
  rfl

end AdicCompletion

namespace Algebra

namespace Smooth

section

variable {R : Type*} [CommRing R]
variable (I : Ideal R) (J : Ideal R) (h : I ≤ J)

def Ideal.Quotient.factorₐ : R ⧸ I →ₐ[R] R ⧸ J := by
  fapply AlgHom.mk
  · exact Ideal.Quotient.factor h
  · intro r
    simp

end

section

variable (A : Type*) [CommRing A]
variable (B : Type*) [CommRing B] [Algebra A B]
variable (C : Type*) [CommRing C] [Algebra A C]

-- the unique algebra map to the zero algebra
def AlgHom.toTrivialAlgebra [Subsingleton C] : B →ₐ[A] C := default

@[simp]
lemma AlgHom.toTrivialAlgebra_apply_eq_one [Subsingleton C] (b : B) :
    AlgHom.toTrivialAlgebra A B C b = 1 :=
  Subsingleton.elim _ _

end

section

variable {A : Type u} [CommRing A]
variable {B : Type u} [CommRing B] [Algebra A B] [FormallySmooth A B]
variable {k : ℕ}

local notation "R" => MvPolynomial (Fin k) A

variable (f : MvPolynomial (Fin k) A →ₐ[A] B) (hf : Function.Surjective f)

local notation "I" => RingHom.ker f

noncomputable def sectionAuxEquiv (m : ℕ) :
    ((R ⧸ I ^ (m + 1)) ⧸ (I ^ m).map (Ideal.Quotient.mk (I ^ (m + 1)))) ≃ₐ[A] R ⧸ (I ^ m) := by
  apply DoubleQuot.quotQuotEquivQuotOfLEₐ _
  apply Ideal.pow_le_pow_right
  exact Nat.le_succ m

omit [FormallySmooth A B] in
@[simp]
lemma sectionAuxEquiv_mk (m : ℕ) (p : R) :
    sectionAuxEquiv f m p = p := by
  simp only [sectionAuxEquiv]
  change (DoubleQuot.quotQuotEquivQuotOfLEₐ A _) (DoubleQuot.quotQuotMk _ _ p) =
    Ideal.Quotient.mk _ p
  simp

omit [FormallySmooth A B] in
lemma sectionAuxEquiv_comp (m : ℕ) :
    AlgHom.comp (sectionAuxEquiv f m).toAlgHom
      (Ideal.Quotient.mkₐ A <| (I ^ m).map (Ideal.Quotient.mk (I ^ (m + 1)))) =
      AdicCompletion.transitionMap'ₐ A I (Nat.le_succ m) := by
  apply AlgHom.cancel_surjective (Ideal.Quotient.mkₐ A (I ^ (m + 1)))
  · apply Ideal.Quotient.mkₐ_surjective
  · ext; simp

/-- Lift `B →ₐ[A] R ⧸ I` inductively to `B →ₐ[A] R ⧸ (I ^ m)` using formal smoothness.
Note that, since `B ≃ₐ[A] R ⧸ I ≃ₐ[A] R ⧸ (I ^ m) ⧸ (I ⧸ (I ^ m))`, we could also
lift this directly, but then we don't have compatibility with the canonical transition maps.
-/
noncomputable def sectionAux' : (m : ℕ) → B →ₐ[A] R ⧸ (I ^ (m + 1))
  | Nat.zero => by
      letI e : (R ⧸ I) ≃ₐ[A] R ⧸ (I ^ 1) := by
        apply Ideal.quotientEquivAlgOfEq A
        simp
      letI f' : (R ⧸ I) ≃ₐ[A] B := Ideal.quotientKerAlgEquivOfSurjective hf
      exact (AlgEquiv.trans f'.symm e).toAlgHom
  | Nat.succ m => by
      letI T := R ⧸ (I ^ (m + 2))
      letI J : Ideal T := Ideal.map (Ideal.Quotient.mk (I ^ (m + 2))) (I ^ (m + 1))
      letI q : B →ₐ[A] T ⧸ J := AlgHom.comp (sectionAuxEquiv f (m + 1)).symm (sectionAux' m)
      refine FormallySmooth.lift J ⟨m + 2, ?_⟩ q
      rw [← Ideal.map_pow, Submodule.zero_eq_bot, ← pow_mul]
      refine eq_bot_mono (Ideal.map_mono ?_) (Ideal.map_quotient_self _)
      apply Ideal.pow_le_pow_right
      simp

@[simp]
theorem sectionAux'_zero (p : R) : (sectionAux' f hf 0) (f p) = p := by
  simp only [sectionAux']
  simp only [Nat.reduceAdd, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, AlgEquiv.trans_apply]
  change (Ideal.quotientEquivAlgOfEq A _)
    ((Ideal.quotientKerAlgEquivOfSurjective hf).symm
      (Ideal.quotientKerAlgEquivOfSurjective hf p)) = Ideal.Quotient.mk _ p
  erw [RingEquiv.symm_apply_apply]
  rfl

lemma sectionAux'_comp_transitionMap (m : ℕ) :
    AlgHom.comp (AdicCompletion.transitionMap'ₐ A I (Nat.le_succ (m + 1)))
        (sectionAux' f hf (m + 1)) =
      sectionAux' f hf m := by
  cases m <;> (
    simp only [sectionAux', ← sectionAuxEquiv_comp]
    ext
    simp
  )

/-- Extends `sectionAux` with the zero map in degree zero. -/
noncomputable def sectionAux : (m : ℕ) → B →ₐ[A] R ⧸ (I ^ m)
  | Nat.zero => by
      have : Subsingleton (R ⧸ I ^ Nat.zero) := by
        rw [Ideal.Quotient.subsingleton_iff]
        simp
      apply AlgHom.toTrivialAlgebra
  | Nat.succ m => sectionAux' f hf m

@[simp]
lemma sectionAux_comp_transitionMap (m : ℕ) :
    AlgHom.comp (AdicCompletion.transitionMap'ₐ A I (Nat.le_succ m)) (sectionAux f hf (m + 1)) =
      sectionAux f hf m := by
  cases m with
  | zero =>
      ext b
      apply eq_of_zero_eq_one
      rw [subsingleton_iff_zero_eq_one, Ideal.Quotient.subsingleton_iff]
      simp
  | succ m => exact sectionAux'_comp_transitionMap f hf m

@[simp]
lemma sectionAux_comp_transitionMap_of_le {m n : ℕ} (hn : m ≤ n) :
    AlgHom.comp (AdicCompletion.transitionMap'ₐ A I hn) (sectionAux f hf n)
      = sectionAux f hf m := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
      rw [← AdicCompletion.transitionMap'ₐ_comp I hmn (by omega), AlgHom.comp_assoc]
      simpa

/-- The constructed section from `B` to the `I`-adic completion of `R`. -/
noncomputable def section' : B →ₐ[A] AdicCompletion I R :=
  AdicCompletion.liftₐ I (sectionAux f hf) (sectionAux_comp_transitionMap_of_le f hf)

@[simp]
theorem section'_apply (p : R) :
    AdicCompletion.evalₐ I 1 (section' f hf (f p)) = p := by
  simp [section']
  simp only [sectionAux]
  simp

set_option synthInstance.maxHeartbeats 50000

/-- The canonical projection from the `I`-adic completion of `R` to `B`. -/
noncomputable def proj : AdicCompletion I R →ₐ[A] B :=
  let p : AdicCompletion I R →ₐ[A] (R ⧸ (I ^ 1)) :=
    AlgHom.restrictScalars A (AdicCompletion.evalₐ I 1)
  let e : (R ⧸ (I ^ 1)) ≃ₐ[A] R ⧸ I := by
    apply Ideal.quotientEquivAlgOfEq A
    simp
  let f' : (R ⧸ I) ≃ₐ[A] B := Ideal.quotientKerAlgEquivOfSurjective hf
  AlgHom.comp f' (AlgHom.comp e.toAlgHom p)

/-- The constructed section is indeed a section for `proj`. -/
theorem section'_isSection :
    AlgHom.comp (proj f hf) (section' f hf) = AlgHom.id A B := by
  --simp only [proj]
  apply AlgHom.cancel_surjective (Ideal.quotientKerAlgEquivOfSurjective hf).toAlgHom
    (EquivLike.surjective (Ideal.quotientKerAlgEquivOfSurjective hf))
  apply AlgHom.cancel_surjective (Ideal.Quotient.mkₐ A I) (Ideal.Quotient.mkₐ_surjective _ _)
  ext i
  simp
  change (proj f hf) ((section' f hf) (f (MvPolynomial.X i))) = f (MvPolynomial.X i)
  simp [proj]
  rfl

variable [IsNoetherianRing A]

--instance : Module.Flat R (AdicCompletion I R) := AdicCompletion.flat I

/-- The polynomial ring is flat -/
instance : Module.Flat A R := inferInstance

instance : Module.Flat A (AdicCompletion I R) :=
  Module.Flat.trans A R (AdicCompletion I R)

instance flat_of_map : Module.Flat A B := by
  apply Module.Flat.of_retract (section' f hf).toLinearMap (proj f hf).toLinearMap
  ext b
  simp only [LinearMap.coe_comp, Function.comp_apply]
  change (AlgHom.comp (proj f hf) (section' f hf)) b = (AlgHom.id A B) b
  rw [section'_isSection f hf]

end

section

variable (A : Type u) [CommRing A] [IsNoetherianRing A]
variable (B : Type u) [CommRing B] [Algebra A B]

variable [Algebra.FiniteType A B] [Algebra.FormallySmooth A B]

instance flat_of_noetherian : Module.Flat A B := by
  obtain ⟨k, f, hf⟩ :=
    (FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B)).mp inferInstance
  exact flat_of_map f hf

end

section

variable (A : Type u) [CommRing A]
variable (B : Type u) [CommRing B] [Algebra A B]

variable [Algebra.FinitePresentation A B] [Algebra.FormallySmooth A B]

/-- If `B` is a smooth `A`-algebra, `B` is `A`-flat. -/
instance flat : Module.Flat A B := by
  obtain ⟨A₀, B₀, _, _, f, hfin, hfp, hfs⟩ := descent (R := A) B inferInstance
  have : IsNoetherianRing A₀ := FiniteType.isNoetherianRing ℤ A₀
  have : Module.Flat A₀ B₀ := inferInstance
  have : Module.Flat A (A ⊗[A₀] B₀) := inferInstance
  exact Module.Flat.of_linearEquiv f.toLinearEquiv

end
