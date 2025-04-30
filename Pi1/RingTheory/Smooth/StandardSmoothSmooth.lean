/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Pi1.RingTheory.Smooth.FreeKaehler
import Pi1.Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.Smooth.Kaehler
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.RingHom.Locally
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.RingHom.FinitePresentation

/-!
# Smooth and locally standard smooth
-/

suppress_compilation

universe w t u v

section Upstream

instance Localization.Away.finitePresentation {R : Type*} [CommRing R] (r : R) :
    Algebra.FinitePresentation R (Localization.Away r) :=
  IsLocalization.Away.finitePresentation r

instance Localization.essFiniteType {R : Type*} [CommRing R] (S : Submonoid R) :
    Algebra.EssFiniteType R (Localization S) :=
  Algebra.EssFiniteType.of_isLocalization _ S

section

variable {R M M' : Type*} [CommRing R]
    (S : Submonoid R) [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M')

lemma IsLocalizedModule.subsingleton [IsLocalizedModule S f] (h : 0 ∈ S) :
    Subsingleton M' := by
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨⟨a, s⟩, (rfl : mk' f a s = _)⟩ := IsLocalizedModule.mk'_surjective S f a
  obtain ⟨⟨b, t⟩, (rfl : mk' f b t = _)⟩ := IsLocalizedModule.mk'_surjective S f b
  exact (IsLocalizedModule.mk'_eq_mk'_iff f a b s t).mpr ⟨⟨0, h⟩, by simp⟩

lemma IsLocalizedModule.subsingleton_of_subsingleton [IsLocalizedModule S f] [Subsingleton M] :
    Subsingleton M' := by
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨⟨a, s⟩, (rfl : mk' f a s = _)⟩ := IsLocalizedModule.mk'_surjective S f a
  obtain ⟨⟨b, t⟩, (rfl : mk' f b t = _)⟩ := IsLocalizedModule.mk'_surjective S f b
  rw [IsLocalizedModule.mk'_eq_mk'_iff f a b s t]
  use 1
  apply Subsingleton.elim

lemma IsLocalizedModule.exists_subsingleton_away {R M M' : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [AddCommGroup M'] [Module R M'] (l : M →ₗ[R] M')
    (p : Ideal R) [p.IsPrime] [IsLocalizedModule p.primeCompl l] [Subsingleton M'] :
    ∃ f ∉ p, Subsingleton (LocalizedModule (Submonoid.powers f) M) := by
  let e := IsLocalizedModule.iso p.primeCompl l
  have : Subsingleton (LocalizedModule p.primeCompl M) := e.subsingleton
  apply LocalizedModule.exists_subsingleton_away

section

variable {R M N M' N' : Type*} [CommSemiring R] (S : Submonoid R)
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
  (g₁ : M →ₗ[R] M') (g₂ : N →ₗ[R] N')

lemma IsLocalizedModule.map_injective_iff_localizedModule_map_injective
    [IsLocalizedModule S g₁] [IsLocalizedModule S g₂] (l : M →ₗ[R] N) :
    Function.Injective (IsLocalizedModule.map S g₁ g₂ l) ↔
      Function.Injective (LocalizedModule.map S l) := by
  have : ⇑(LocalizedModule.map S l) =
      ⇑((IsLocalizedModule.iso S g₂).symm ∘ₗ
      IsLocalizedModule.map S g₁ g₂ l ∘ₗ IsLocalizedModule.iso S g₁) := by
    rw [← LocalizedModule.restrictScalars_map_eq S g₁ g₂ l]
    simp only [LinearMap.coe_restrictScalars]
  rw [this]
  simp

lemma IsLocalizedModule.map_surjective_iff_localizedModule_map_surjective
    [IsLocalizedModule S g₁] [IsLocalizedModule S g₂] (l : M →ₗ[R] N) :
    Function.Surjective (IsLocalizedModule.map S g₁ g₂ l) ↔
      Function.Surjective (LocalizedModule.map S l) := by
  have : ⇑(LocalizedModule.map S l) =
      ⇑((IsLocalizedModule.iso S g₂).symm ∘ₗ
      IsLocalizedModule.map S g₁ g₂ l ∘ₗ IsLocalizedModule.iso S g₁) := by
    rw [← LocalizedModule.restrictScalars_map_eq S g₁ g₂ l]
    simp only [LinearMap.coe_restrictScalars]
  rw [this]
  simp

lemma IsLocalizedModule.map_bijective_iff_localizedModule_map_bijective
    [IsLocalizedModule S g₁] [IsLocalizedModule S g₂] (l : M →ₗ[R] N) :
    Function.Bijective (IsLocalizedModule.map S g₁ g₂ l) ↔
      Function.Bijective (LocalizedModule.map S l) := by
  have : ⇑(LocalizedModule.map S l) =
      ⇑((IsLocalizedModule.iso S g₂).symm ∘ₗ
      IsLocalizedModule.map S g₁ g₂ l ∘ₗ IsLocalizedModule.iso S g₁) := by
    rw [← LocalizedModule.restrictScalars_map_eq S g₁ g₂ l]
    simp only [LinearMap.coe_restrictScalars]
  rw [this]
  simp

end

section

variable {R : Type*} [CommSemiring R] (S : Submonoid R) {M M' M'' : Type*}
  [AddCommMonoid M] [AddCommMonoid M']
  [AddCommMonoid M''] [Module R M] [Module R M'] [Module R M'']
  (f : M →ₗ[R] M') (g : M →ₗ[R] M'') [IsLocalizedModule S f]

@[simp]
lemma IsLocalizedModule.iso_symm_apply'' (x) : (iso S f).symm (f x) = LocalizedModule.mk x 1 := by
  show ((iso S f).symm.toLinearMap.comp f) x = _
  --have := iso_symm_comp S f
  rw [iso_symm_comp]
  simp

end

end

end Upstream

namespace LinearMap

variable {R M N : Type*} [CommRing R]

end LinearMap

namespace Module

section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submonoid R)
    {M' : Type*} [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M')
    [IsLocalizedModule S f]
    (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ]
    [Module Rₛ M'] [IsScalarTower R Rₛ M']
    [IsLocalization S Rₛ]
    (Mₜ : R → Type*) [∀ t, AddCommGroup (Mₜ t)] [∀ t, Module R (Mₜ t)]
    (fₜ : ∀ t, M →ₗ[R] Mₜ t)
    [∀ t, IsLocalizedModule (.powers t) (fₜ t)]
    (Rₜ : R → Type*) [∀ t, CommRing (Rₜ t)] [∀ t, Algebra R (Rₜ t)]
    [∀ t, IsLocalization.Away t (Rₜ t)]
    [∀ t, Module (Rₜ t) (Mₜ t)]
    [∀ t, IsScalarTower R (Rₜ t) (Mₜ t)]
    [FinitePresentation R M] {I : Type*} [Finite I]
    (b : Basis I Rₛ M')

include b

lemma FinitePresentation.exists_basis_of_isLocalizedModule_powers :
    ∃ (t : R) (ht : t ∈ S) (b' : Basis I (Rₜ t) (Mₜ t)),
      ∀ (i : I), (IsLocalizedModule.lift (.powers t) (fₜ t) f
        (fun x ↦ IsLocalizedModule.map_units f
          ⟨x.1, SetLike.le_def.mp (Submonoid.powers_le.mpr ht) x.2⟩) (b' i) = b i) := by
  obtain ⟨t, ht, b', hb'⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers S f Rₛ b
  use t, ht
  let eM : LocalizedModule (.powers t) M ≃ₗ[R] Mₜ t := IsLocalizedModule.iso (.powers t) (fₜ t)
  let eb'' : Mₜ t ≃ₗ[R] I →₀ Rₜ t :=
    eM.symm ≪≫ₗ b'.repr.restrictScalars R ≪≫ₗ
      IsLocalizedModule.linearEquiv (.powers t)
        (Finsupp.mapRange.linearMap (Algebra.linearMap R _))
        (Finsupp.mapRange.linearMap (Algebra.linearMap R _))
  let eb : Mₜ t ≃ₗ[Rₜ t] I →₀ Rₜ t :=
    .ofLinear (.extendScalarsOfIsLocalizationEquiv (.powers t) (Rₜ t) eb'')
      (.extendScalarsOfIsLocalizationEquiv (.powers t) (Rₜ t) eb''.symm)
      (by ext; simp) (by ext; simp)
  refine ⟨Basis.ofRepr eb, fun i ↦ ?_⟩
  simp only [LinearMap.extendScalarsOfIsLocalizationEquiv_apply, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, Basis.coe_ofRepr, LinearEquiv.ofLinear_symm_apply,
    LinearMap.extendScalarsOfIsLocalization_apply', LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_symm_apply, Basis.repr_symm_apply, eb, eb'']
  have : Finsupp.single i 1 =
    (Finsupp.mapRange.linearMap (Algebra.linearMap R (Rₜ t))) (Finsupp.basisSingleOne i) := by simp
  rw [this]
  rw [IsLocalizedModule.linearEquiv_symm_apply]
  simp only [Finsupp.coe_basisSingleOne, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    Algebra.linearMap_apply, map_one, Finsupp.linearCombination_single, one_smul,
    eM, eb'', eb]
  rw [IsLocalizedModule.lift_iso, hb']

end

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]

open LinearMap in
lemma exists_of_surjective [Module.Finite R N] (f : M →ₗ[R] N)
    (p : Ideal R) [p.IsPrime] (hf : Function.Surjective (LocalizedModule.map p.primeCompl f)) :
    ∃ g ∉ p, Function.Surjective (LocalizedModule.map (Submonoid.powers g) f) := by
  have : Submodule.localized p.primeCompl (range f) = range (LocalizedModule.map p.primeCompl f) :=
    localized'_range_eq_range_localizedMap _ _ _ _ _
  let fₚ : N ⧸ LinearMap.range f →ₗ[R]
      LocalizedModule p.primeCompl N ⧸ LinearMap.range (LocalizedModule.map p.primeCompl f) :=
    (LinearEquiv.toLinearMap <| (Submodule.quotEquivOfEq _ _ this).restrictScalars R) ∘ₗ
      (range f).toLocalizedQuotient p.primeCompl
  have : IsLocalizedModule p.primeCompl fₚ := by
    apply IsLocalizedModule.of_linearEquiv
  have : Subsingleton
      (LocalizedModule p.primeCompl N ⧸ LinearMap.range (LocalizedModule.map p.primeCompl f)) := by
    rwa [Submodule.subsingleton_quotient_iff_eq_top, LinearMap.range_eq_top]
  obtain ⟨g, hg, _⟩ := IsLocalizedModule.exists_subsingleton_away fₚ p
  use g, hg
  let p : Submodule (Localization (Submonoid.powers g)) (LocalizedModule (Submonoid.powers g) N) :=
    LinearMap.range ((LocalizedModule.map (Submonoid.powers g)) f)
  let q : Submodule (Localization (Submonoid.powers g)) (LocalizedModule (Submonoid.powers g) N) :=
      Submodule.localized (Submonoid.powers g) (LinearMap.range f)
  have : p = q := by
    symm
    apply LinearMap.localized'_range_eq_range_localizedMap
  let eq : (LocalizedModule (Submonoid.powers g) N ⧸
      range ((LocalizedModule.map (Submonoid.powers g)) f)) ≃ₗ[R]
        (LocalizedModule (Submonoid.powers g) (N ⧸ range f)) :=
    (p.quotEquivOfEq q this).restrictScalars R ≪≫ₗ (IsLocalizedModule.iso (Submonoid.powers g)
      ((range f).toLocalizedQuotient (Submonoid.powers g))).symm
  rw [← LinearMap.range_eq_top, ← Submodule.subsingleton_quotient_iff_eq_top]
  apply eq.subsingleton

lemma exists_of_surjective' [Module.Finite R N] (f : M →ₗ[R] N)
    (p : Ideal R) [p.IsPrime] {Mₚ Nₚ : Type*}
    [AddCommGroup Mₚ] [AddCommGroup Nₚ] [Module R Mₚ] [Module R Nₚ]
    (fM : M →ₗ[R] Mₚ) (fN : N →ₗ[R] Nₚ)
    [IsLocalizedModule p.primeCompl fM]
    [IsLocalizedModule p.primeCompl fN]
    (hf : Function.Surjective (IsLocalizedModule.map p.primeCompl fM fN f)) :
    ∃ g ∉ p, Function.Surjective (LocalizedModule.map (Submonoid.powers g) f) := by
  simp_rw [IsLocalizedModule.map_surjective_iff_localizedModule_map_surjective] at hf ⊢
  exact exists_of_surjective f p hf

lemma exists_of_bijective' [Module.Finite R M] [Module.FinitePresentation R N] (f : M →ₗ[R] N)
    (p : Ideal R) [p.IsPrime] {Rₚ Mₚ Nₚ : Type*}
    [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
    [AddCommGroup Mₚ] [AddCommGroup Nₚ] [Module R Mₚ] [Module R Nₚ]
    (fM : M →ₗ[R] Mₚ) (fN : N →ₗ[R] Nₚ)
    [IsLocalizedModule p.primeCompl fM]
    [IsLocalizedModule p.primeCompl fN]
    {Mₜ Nₜ : R → Type*}
    [∀ r, AddCommGroup (Mₜ r)] [∀ r, Module R (Mₜ r)]
    [∀ r, AddCommGroup (Nₜ r)] [∀ r, Module R (Nₜ r)]
    (fₜ : ∀ r, M →ₗ[R] Mₜ r) [∀ r, IsLocalizedModule (Submonoid.powers r) (fₜ r)]
    (gₜ : ∀ r, N →ₗ[R] Nₜ r) [∀ r, IsLocalizedModule (Submonoid.powers r) (gₜ r)]
    (hf : Function.Bijective (IsLocalizedModule.map p.primeCompl fM fN f)) :
    ∃ (g : R), g ∉ p ∧
      Function.Bijective (IsLocalizedModule.map (Submonoid.powers g) (fₜ g) (gₜ g) f) := by
  simp_rw [IsLocalizedModule.map_bijective_iff_localizedModule_map_bijective]
  obtain ⟨g, hg, h⟩ := exists_bijective_map_powers p.primeCompl fM fN f hf
  exact ⟨g, hg, h g (by rfl)⟩

lemma exists_of_bijective [Module.Finite R M] [Module.FinitePresentation R N] (f : M →ₗ[R] N)
    (p : Ideal R) [p.IsPrime] {Rₚ Mₚ Nₚ : Type*}
    [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
    [AddCommGroup Mₚ] [AddCommGroup Nₚ] [Module R Mₚ] [Module R Nₚ]
    (fM : M →ₗ[R] Mₚ) (fN : N →ₗ[R] Nₚ)
    [IsLocalizedModule p.primeCompl fM]
    [IsLocalizedModule p.primeCompl fN]
    (hf : Function.Bijective (IsLocalizedModule.map p.primeCompl fM fN f)) :
    ∃ (g : R), g ∉ p ∧ Function.Bijective (LocalizedModule.map (Submonoid.powers g) f) := by
  obtain ⟨g, hg, h⟩ := exists_bijective_map_powers p.primeCompl fM fN f hf
  exact ⟨g, hg, h g (by rfl)⟩

end Module

namespace Algebra

variable {R S : Type u} [CommRing R] [CommRing S]

section

variable [Algebra R S]

variable (R) in
lemma isSmoothAt_of_smooth [Smooth R S] (p : Ideal S) [p.IsPrime] :
    IsSmoothAt R p := by
  have : smoothLocus R S = Set.univ := by
    rw [smoothLocus_eq_univ_iff]
    infer_instance
  show ⟨p, inferInstance⟩ ∈ smoothLocus R S
  rw [this]
  trivial

open KaehlerDifferential

lemma _root_.KaehlerDifferential.span_range_map_derivation_of_isLocalization
    (R : Type u) {S : Type u} (T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] (M : Submonoid S) [IsLocalization M T] :
    Submodule.span T (Set.range <| fun s ↦ map R R S T (D R S s)) = ⊤ := by
  convert span_eq_top_of_isLocalizedModule T M (map R R S T) (v := Set.range <| D R S)
    (span_range_derivation R S)
  rw [← Set.range_comp, Function.comp_def]

theorem exists_isStandardSmooth [Smooth R S] (p : Ideal S) [p.IsPrime] :
    ∃ (f : S), f ∉ p ∧ IsStandardSmooth.{u, u} R (Localization.Away f) := by
  have : FormallySmooth R (Localization.AtPrime p) := isSmoothAt_of_smooth R p
  let v (s : S) : (Ω[Localization.AtPrime p⁄R]) :=
    map R R S (Localization.AtPrime p) (D R S s)
  have hv : Submodule.span (Localization.AtPrime p) (Set.range v) = ⊤ :=
    span_range_map_derivation_of_isLocalization R (Localization.AtPrime p) p.primeCompl
  have : Algebra.EssFiniteType R (Localization.AtPrime p) :=
    Algebra.EssFiniteType.comp R S (Localization.AtPrime p)
  have : Module.FinitePresentation (Localization.AtPrime p) (Ω[Localization.AtPrime p⁄R]) :=
    Module.finitePresentation_of_projective (Localization.AtPrime p) (Ω[Localization.AtPrime p⁄R])
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat v hv
  let e : (κ →₀ S) →ₗ[S] (Ω[S ⁄R]) :=
    Finsupp.basisSingleOne.constr S (fun i : κ ↦ D R S (a i))
  let l₁ : (κ →₀ S) →ₗ[S] (κ →₀ Localization.AtPrime p) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S (Localization.AtPrime p))
  have : IsLocalizedModule p.primeCompl l₁ := inferInstance
  let l₂ : (Ω[S⁄R]) →ₗ[S] (Ω[Localization.AtPrime p⁄R]) := map R R S (Localization.AtPrime p)
  have : IsLocalizedModule p.primeCompl l₂ := inferInstance
  let eₚ : (κ →₀ Localization.AtPrime p) →ₗ[Localization.AtPrime p] (Ω[Localization.AtPrime p⁄R]) :=
    IsLocalizedModule.mapExtendScalars p.primeCompl l₁ l₂ (Localization.AtPrime p) e
  have : eₚ = b.repr.symm := by
    apply Finsupp.basisSingleOne.ext
    intro i
    have : Finsupp.basisSingleOne i = l₁ (Finsupp.basisSingleOne i) := by simp [l₁]
    simp only [this, IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply,
      Basis.constr_basis, map_D, Basis.coe_repr_symm, eₚ, l₂, e]
    simp [l₁, hb, v]
  have heₚ : Function.Bijective eₚ := by
    rw [this]
    exact b.repr.symm.bijective
  have : Finite κ := Module.Finite.finite_basis b
  let l₁ₜ (s : S) : (κ →₀ S) →ₗ[S] (κ →₀ Localization.Away s) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S _)
  let l₂ₜ (s : S) : (Ω[S⁄R]) →ₗ[S] (Ω[Localization.Away s⁄R]) :=
    map R R S (Localization.Away s)
  obtain ⟨g, hg, h⟩ := Module.exists_of_bijective' e p l₁ l₂ (Rₚ := Localization.AtPrime p)
    l₁ₜ l₂ₜ heₚ
  let eₜ' : (κ →₀ Localization.Away g) →ₗ[Localization.Away g] (Ω[Localization.Away g⁄R]) :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers g) (l₁ₜ g) (l₂ₜ g) (Localization.Away g) e
  use g, hg
  have : Subsingleton (H1Cotangent R (Localization.Away g)) :=
    IsLocalizedModule.subsingleton_of_subsingleton (Submonoid.powers g)
      (Algebra.H1Cotangent.map R R S (Localization.Away g))
  have : FinitePresentation R (Localization.Away g) :=
    FinitePresentation.trans R S (Localization.Away g)
  refine isStandardSmooth_of (I := κ) (Basis.ofRepr (LinearEquiv.ofBijective eₜ' h).symm) ?_
  rintro - ⟨i, rfl⟩
  simp only [Basis.coe_ofRepr, LinearEquiv.symm_symm, LinearEquiv.ofBijective_apply,
    IsLocalizedModule.mapExtendScalars_apply_apply, Set.mem_range, eₜ']
  use algebraMap S (Localization.Away g) (a i)
  have : Finsupp.single i 1 = (l₁ₜ g) (Finsupp.basisSingleOne i) := by simp [l₁ₜ]
  rw [this]
  simp [-Finsupp.coe_basisSingleOne, l₂ₜ, e]

theorem exists_cover [Smooth R S] : ∃ (s : Set S),
    Ideal.span s = ⊤ ∧ ∀ x ∈ s, IsStandardSmooth R (Localization.Away x) := by
  have (p : Ideal S) [p.IsPrime] :
      ∃ (f : S), f ∉ p ∧ IsStandardSmooth R (Localization.Away f) := by
    obtain ⟨g, hg, h⟩ := exists_isStandardSmooth (R := R) p
    use g, hg
  choose f hf₁ hf₂ using this
  refine ⟨Set.range (fun p : PrimeSpectrum S ↦ f p.asIdeal), ?_, ?_⟩
  · rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    rw [_root_.eq_top_iff]
    rintro p -
    simp only [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.carrier_eq_coe,
      PrimeSpectrum.basicOpen_eq_zeroLocus_compl, TopologicalSpace.Opens.coe_mk, Set.mem_iUnion,
      Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
    use p
    apply hf₁
  · simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    intro p
    apply hf₂

end

end Algebra

namespace RingHom

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

lemma smooth_of_isStandardSmooth (f : R →+* S) (hf : IsStandardSmooth f) :
    Smooth f := by
  algebraize [f]
  rw [RingHom.Smooth]
  infer_instance

theorem locally_isStandardSmooth_of_smooth (f : R →+* S)
    (hf : f.Smooth) : Locally IsStandardSmooth f := by
  algebraize [f]
  have : Algebra.Smooth R S := hf
  obtain ⟨s, hs, h⟩ := Algebra.exists_cover (R := R) (S := S)
  use s, hs
  intro t ht
  suffices h : Algebra.IsStandardSmooth R (Localization.Away t) by
    rw [RingHom.IsStandardSmooth]
    convert h
    ext
    rw [Algebra.smul_def]
    rfl
  convert h t ht

theorem smooth_iff_locally_isStandardSmooth {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    Smooth f ↔ Locally IsStandardSmooth f := by
  constructor
  · intro hf
    exact locally_isStandardSmooth_of_smooth f hf
  · intro hf
    have : Locally Smooth f := by
      refine RingHom.locally_of_locally ?_ hf
      introv
      apply smooth_of_isStandardSmooth
    rwa [RingHom.locally_iff_of_localizationSpanTarget Smooth.respectsIso
      Smooth.ofLocalizationSpanTarget] at this

end RingHom
