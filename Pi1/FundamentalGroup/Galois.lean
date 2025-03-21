/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.Etale
import Pi1.Mathlib.AlgebraicGeometry.Limits
import Pi1.FundamentalGroup.FiniteEtale
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-!
# The category of finite étale morphisms over a connected base is a Galois category

Let `S` be a scheme and denote by `FEt S` the category of finite étale schemes over `S`. Then
`FEt S` is a `PreGaloisCategory`.
-/

universe u w

noncomputable section

open CategoryTheory Limits

instance {C : Type*} [Category C] {G : Type*} [Group G] [Finite G] [HasFiniteColimits C] :
    HasColimitsOfShape (SingleObj G) C := by
  obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm

instance {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {G : Type*} [Group G] [Finite G]
    [PreservesFiniteColimits F] :
    PreservesColimitsOfShape (SingleObj G) F := by
  obtain ⟨(G' : Type), hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.preservesColimitsOfShape_of_equiv e.toSingleObjEquiv.symm F

namespace AlgebraicGeometry

section General

end General

namespace FiniteEtale

variable (X : Scheme.{u})

/-- The category of finite étale morphisms is a pre-galois category. -/
instance (X : Scheme.{u}) : PreGaloisCategory (FiniteEtale X) where
  hasQuotientsByFiniteGroups G := inferInstance
  monoInducesIsoOnDirectSummand {f g} i hi := by
    rw [FiniteEtale.mono_iff] at hi
    obtain ⟨ho, hc⟩ := hi
    let A : Set g.left := Set.range i.hom.left.base
    have hA : IsClosed A := i.hom.left.isClosedEmbedding.isClosed_range
    let U : g.left.Opens := ⟨Aᶜ, hA.isOpen_compl⟩
    have : IsClosedImmersion U.ι := by
      apply isClosedImmersion_of_isPreimmersion_of_isClosed
      simp only [Scheme.Opens.range_ι, TopologicalSpace.Opens.coe_mk, isClosed_compl_iff, U, A]
      apply IsOpenImmersion.isOpen_range
    let u : FiniteEtale X := ⟨Over.mk (U.ι ≫ g.hom), by simpa using ⟨⟩⟩
    refine ⟨u, MorphismProperty.Over.homMk U.ι, ⟨?_⟩⟩
    apply isColimitOfReflects (MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _)
    apply (isColimitMapCoconeBinaryCofanEquiv _ _ _).invFun
    simp only [Functor.comp_obj, MorphismProperty.Comma.forget_obj, Over.forget_obj,
      Functor.comp_map, MorphismProperty.Comma.forget_map, Over.forget_map,
      MorphismProperty.Over.homMk_hom, Over.homMk_left]
    apply Nonempty.some
    apply nonempty_isColimit_binaryCofanMk_of_isCompl
    constructor
    · rw [disjoint_iff]
      ext : 1
      simp [U, A]
    · rw [codisjoint_iff]
      ext : 1
      simp [U, A]

instance : HasRingHomProperty @IsEtale RingHom.Etale :=
  sorry

lemma finite_of_isFinite_of_etale (X : Scheme.{u}) {Ω : Type u} [Field Ω]
    (f : X ⟶ Spec (.of Ω)) [IsEtale f] [IsAffineHom f] :
    Finite X := by
  have : IsAffine X := isAffine_of_isAffineHom f
  have : IsEtale f := inferInstance
  rw [HasRingHomProperty.iff_of_isAffine (P := @IsEtale)] at this
  let e : Γ(Spec (CommRingCat.of Ω), ⊤) ≃+* Ω :=
    (Scheme.ΓSpecIso (.of Ω)).commRingCatIsoToRingEquiv
  algebraize [(f.appTop.hom.comp e.symm.toRingHom)]
  have : Algebra.Etale Ω Γ(X, ⊤) := by
    show (f.appTop.hom.comp e.symm.toRingHom).Etale
    apply RingHom.Etale.respectsIso.2
    assumption
  rw [Algebra.Etale.iff_exists_algEquiv_prod Ω Γ(X, ⊤)] at this
  obtain ⟨I, hI, Ai, _, _, eq, h⟩ := this
  let eq2 : X ≅ ∐ fun i ↦ Spec (.of (Ai i)) :=
    X.isoSpec ≪≫ Scheme.Spec.mapIso eq.toRingEquiv.symm.toCommRingCatIso.op ≪≫
      (asIso (sigmaSpec (fun i ↦ .of (Ai i)))).symm
  let eq3 : X ≃ Σ i, Spec (.of <| Ai i) :=
    eq2.schemeIsoToHomeo.trans (sigmaMk _).symm
  apply Finite.of_equiv _ eq3.symm

instance {Ω : Type u} [Field Ω] (X : FiniteEtale (Spec (.of Ω))) : Fintype X.left :=
  have : Finite X.left := finite_of_isFinite_of_etale X.left X.hom
  Fintype.ofFinite X.left

/-- -/
@[simps]
def forgetScheme (Ω : Type u) [Field Ω] : FiniteEtale (Spec (.of Ω)) ⥤ FintypeCat.{u} where
  obj X := FintypeCat.of X.left
  map {X Y} f := f.left.base

variable (Ω : Type u) [Field Ω]

instance {ι : Type u} [Finite ι] (R : Type u) [CommRing R] :
    IsFiniteEtale (Spec.map <| CommRingCat.ofHom <| algebraMap R (ι → R)) :=
  sorry

@[simps]
def inventScheme (Ω : Type u) [Field Ω] : FintypeCat.{u} ⥤ FiniteEtale (Spec (.of Ω)) where
  obj S :=
    mk (Spec.map <| CommRingCat.ofHom <| algebraMap Ω (S → Ω))
  map {S T} f :=
    MorphismProperty.Over.homMk
      (Spec.map <| CommRingCat.ofHom <| Pi.ringHom (fun s ↦ Pi.evalRingHom _ (f s))) <| by
      dsimp
      rw [← Spec.map_comp]
      rfl
  map_id S := by
    apply MorphismProperty.Over.Hom.ext
    simp [FiniteEtale]
    rfl
  map_comp {S T W} f g := by
    dsimp
    apply MorphismProperty.Over.Hom.ext
    simp [FiniteEtale]
    rw [← Spec.map_comp]
    rfl

instance (S : FintypeCat) :
    Fintype (Spec (CommRingCat.of (S.carrier → Ω))).toPresheafedSpace :=
  have : Finite (Spec (CommRingCat.of (S.carrier → Ω))).toPresheafedSpace := sorry
  Fintype.ofFinite _

def specPiEquiv (ι : Type u) [Finite ι] (K : Type u) [Field K] :
    Spec (.of (ι → K)) ≃ ι :=
  ((asIso (sigmaSpec (fun _ : ι ↦ .of K))).schemeIsoToHomeo.toEquiv.symm.trans
      (sigmaMk (fun _ : ι ↦ Spec (.of K))).toEquiv.symm).trans
    (Equiv.sigmaUnique ι (fun _ : ι ↦ Spec (.of K)))

@[simp]
lemma specPiEquiv_symm_apply (ι : Type u) [Finite ι] (K : Type u) [Field K]
    (i : ι) : (specPiEquiv ι K).symm i =
      (Spec.map <| CommRingCat.ofHom <| Pi.evalRingHom _ i).base default := by
  simp [specPiEquiv, Iso.schemeIsoToHomeo, ← Scheme.comp_base_apply]

def inventForgetIso : inventScheme Ω ⋙ forgetScheme Ω ≅ 𝟭 FintypeCat :=
  Iso.symm <| NatIso.ofComponents
    (fun S ↦ FintypeCat.equivEquivIso (specPiEquiv S Ω).symm)
    (fun {S T} f ↦ by
      simp only [Functor.id_obj, Functor.comp_obj, inventScheme_obj, Functor.id_map,
        forgetScheme_obj_carrier, mk_left, Functor.comp_map, inventScheme_map]
      ext x
      simp only [forgetScheme_obj_carrier, mk_left, FintypeCat.equivEquivIso, Equiv.coe_fn_mk,
        Equiv.symm_symm, FintypeCat.comp_apply, specPiEquiv_symm_apply, forgetScheme_map,
        MorphismProperty.Over.homMk_hom, Over.homMk_left]
      have : (Pi.evalRingHom (fun i ↦ Ω) x).comp
          (Pi.ringHom fun s ↦ Pi.evalRingHom (fun a ↦ Ω) (f s)) = Pi.evalRingHom _ (f x) := rfl
      rw [← Scheme.comp_base_apply, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [this])

def _root_.AlgebraicGeometry.IsFiniteEtale.isoSpecPi {X : Scheme.{u}} (f : X ⟶ Spec (.of Ω))
    [IsFiniteEtale f] :
    X ≅ Spec (.of <| Π (m : MaximalSpectrum Γ(X, ⊤)), Γ(X, ⊤) ⧸ m.asIdeal) :=
  have : IsAffine X := isAffine_of_isAffineHom f
  have : IsArtinianRing Γ(X, ⊤) := sorry
  have : _root_.IsReduced Γ(X, ⊤) := sorry
  X.isoSpec ≪≫ Scheme.Spec.mapIso ((IsArtinianRing.equivPi _).symm.toCommRingCatIso).op

--lemma isoSpecPi_naturality {X Y : FiniteEtale (Spec (.of Ω))} (f : X ⟶ Y) :
--    f.left ≫ (IsFiniteEtale.isoSpecPi Ω Y.hom).hom =
--      (IsFiniteEtale.isoSpecPi Ω X.hom).hom ≫
--        Spec.map (CommRingCat.ofHom <|
--          Pi.ringHom (fun i ↦ RingHom.comp _ (Pi.evalRingHom _ _))) := sorry

--lemma _root_.AlgebraicGeometry.IsFiniteEtale.isoSpecPi {X : Scheme.{u}} (f : X ⟶ Spec (.of Ω))
--    [IsFiniteEtale f] :

instance (X : FiniteEtale (Spec <| .of Ω)) : Algebra Ω Γ(X.left, ⊤) :=
  X.hom.appTop.hom.comp
    (Scheme.ΓSpecIso (.of Ω)).commRingCatIsoToRingEquiv.symm.toRingHom |>.toAlgebra

@[simp]
lemma appTop_left_comp_algebraMap {X Y : FiniteEtale (Spec <| .of Ω)} (f : X ⟶ Y) :
    f.left.appTop.hom.comp (algebraMap Ω Γ(Y.left, ⊤)) = algebraMap Ω Γ(X.left, ⊤) :=
  sorry

@[simp]
lemma appTop_left_algebraMap {X Y : FiniteEtale (Spec <| .of Ω)} (f : X ⟶ Y) (x : Ω) :
    f.left.appTop.hom (algebraMap Ω Γ(Y.left, ⊤) x) = algebraMap Ω Γ(X.left, ⊤) x :=
  sorry

def _root_.AlgebraicGeometry.IsFiniteEtale.isoSpecFun [IsSepClosed Ω] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of Ω)) [IsFiniteEtale f] :
    X ≅ Spec (.of <| X → Ω) :=
  have : IsAffine X := isAffine_of_isAffineHom f
  let i1 := IsFiniteEtale.isoSpecPi Ω f
  have : IsArtinianRing Γ(X, ⊤) := sorry
  let e : X ≃ MaximalSpectrum Γ(X, ⊤) :=
    X.isoSpec.schemeIsoToHomeo.toEquiv.trans IsArtinianRing.primeSpectrumEquivMaximalSpectrum
  let _ : Algebra Ω Γ(X, ⊤) :=
    f.appTop.hom.comp
      (Scheme.ΓSpecIso (.of Ω)).commRingCatIsoToRingEquiv.symm.toRingHom |>.toAlgebra
  have (m : MaximalSpectrum Γ(X, ⊤)) : Algebra.IsSeparable Ω (Γ(X, ⊤) ⧸ m.asIdeal) :=
    sorry
  let _ (m : MaximalSpectrum Γ(X, ⊤)) : Field (Γ(X, ⊤) ⧸ m.asIdeal) :=
    Ideal.Quotient.field m.asIdeal
  have hb (m : MaximalSpectrum Γ(X, ⊤)) :
      Function.Bijective (algebraMap Ω (Γ(X, ⊤) ⧸ m.asIdeal)) :=
    ⟨FaithfulSMul.algebraMap_injective _ _,
      IsSepClosed.algebraMap_surjective Ω (Γ(X, ⊤) ⧸ m.asIdeal)⟩
  let a (m : MaximalSpectrum Γ(X, ⊤)) : Γ(X, ⊤) ⧸ m.asIdeal ≃+* Ω :=
    (RingEquiv.ofBijective _ (hb m)).symm
  let o : (Π (m : MaximalSpectrum Γ(X, ⊤)), Γ(X, ⊤) ⧸ m.asIdeal) ≃+* (X → Ω) :=
    (RingEquiv.piCongrRight a).trans (RingEquiv.piCongrLeft (fun _ ↦ Ω) e.symm)
  i1 ≪≫ Scheme.Spec.mapIso o.toCommRingCatIso.symm.op

@[reassoc (attr := simp)]
lemma _root_.AlgebraicGeometry.IsFiniteEtale.isoSpecFun_hom_SpecMap [IsSepClosed Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of Ω)) [IsFiniteEtale f] :
    (IsFiniteEtale.isoSpecFun Ω f).hom ≫
      Spec.map (CommRingCat.ofHom <| algebraMap Ω (X → Ω)) = f := sorry

--@[simp]
lemma IsArtinianRing.equivPi_apply (R : Type*) [CommRing R] [IsArtinianRing R] [_root_.IsReduced R]
    (x : R) (m : MaximalSpectrum R) :
    (IsArtinianRing.equivPi R x) m = Ideal.Quotient.mk m.asIdeal x := rfl

--@[simp]set_option maxHeartbeats <num>
set_option maxHeartbeats 0 in
lemma IsArtinianRing.equivPi_naturality_apply (R S : Type*) [CommRing R] [CommRing S]
    [IsArtinianRing R] [IsArtinianRing S] [_root_.IsReduced R] [_root_.IsReduced S]
    (f : R →+* S) (x : R) :
    IsArtinianRing.equivPi S (f x) =
      Pi.ringHom
        (fun m ↦ RingHom.comp
          (by exact Ideal.quotientMap m.asIdeal f (by simp))
          (Pi.evalRingHom _ ⟨Ideal.comap f m.asIdeal, IsArtinianRing.isMaximal_of_isPrime _⟩))
        (IsArtinianRing.equivPi R x) :=
  sorry

set_option maxHeartbeats 0 in
def forgetInventIso [IsSepClosed Ω] : 𝟭 (FiniteEtale _) ≅ forgetScheme Ω ⋙ inventScheme Ω :=
  NatIso.ofComponents (fun X ↦
    (MorphismProperty.Over.isoMk (IsFiniteEtale.isoSpecFun Ω X.hom))) <| fun {X Y} f ↦ by
      apply MorphismProperty.Over.Hom.ext
      simp [FiniteEtale, IsFiniteEtale.isoSpecFun]
      simp [IsFiniteEtale.isoSpecPi]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [← Spec.map_comp, ← Spec.map_comp]
      have : IsAffine X.left := sorry
      have : IsAffine Y.left := sorry
      rw [← Scheme.isoSpec_hom_naturality_assoc, ← Spec.map_comp]
      congr 2
      ext x
      simp
      have : IsArtinianRing ↑Γ(X.left, ⊤) := sorry
      have : _root_.IsReduced ↑Γ(X.left, ⊤) := sorry
      have : _root_.IsReduced ↑Γ(Y.left, ⊤) := sorry
      have : IsArtinianRing ↑Γ(Y.left, ⊤) := sorry
      apply (IsArtinianRing.equivPi Γ(X.left, ⊤)).injective
      ext j
      simp
      --rw [IsArtinianRing.equivPi_apply]
      rw [IsArtinianRing.equivPi_naturality_apply]
      simp
      congr 1
      sorry

def equivFintypeCat [IsSepClosed Ω] : FiniteEtale (Spec <| .of Ω) ≌ FintypeCat.{u} :=
  CategoryTheory.Equivalence.mk (forgetScheme Ω) (inventScheme Ω)
    (forgetInventIso Ω) (inventForgetIso Ω)

instance [IsSepClosed Ω] : (forgetScheme Ω).IsEquivalence :=
  (equivFintypeCat Ω).isEquivalence_functor

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
variable {X}

def fiber : FiniteEtale X ⥤ FintypeCat :=
  pullback ξ ⋙ forgetScheme Ω

instance [IsSepClosed Ω] : PreservesLimitsOfShape (Discrete PEmpty.{1}) (pullback ξ) :=
  sorry

instance [IsSepClosed Ω] : PreservesLimitsOfShape WalkingCospan (pullback ξ) :=
  sorry

instance [IsSepClosed Ω] : PreservesFiniteColimits (pullback ξ) :=
  sorry

instance [ConnectedSpace X] [IsSepClosed Ω] : (pullback ξ).ReflectsIsomorphisms :=
  sorry

instance [IsSepClosed Ω] : PreservesFiniteColimits (fiber ξ) := by
  dsimp [fiber]
  infer_instance

open PreGaloisCategory

instance [ConnectedSpace X] [IsSepClosed Ω] : FiberFunctor (fiber ξ) where
  preservesTerminalObjects := by dsimp [fiber]; infer_instance
  preservesPullbacks := by dsimp [fiber]; infer_instance
  reflectsIsos := by dsimp [fiber]; infer_instance
  preservesQuotientsByFiniteGroups _ _ := inferInstance

instance [ConnectedSpace X] : GaloisCategory (FiniteEtale X) where
  hasFiberFunctor := by
    have : Nonempty X := inferInstance
    let x : X := ‹Nonempty X›.some
    let k : Type u := X.residueField x
    let Ω : Type u := AlgebraicClosure k
    let ξ : Spec (.of Ω) ⟶ X :=
      Spec.map (CommRingCat.ofHom <| algebraMap k Ω) ≫ X.fromSpecResidueField x
    exact ⟨fiber ξ, ⟨inferInstance⟩⟩

end AlgebraicGeometry.FiniteEtale
