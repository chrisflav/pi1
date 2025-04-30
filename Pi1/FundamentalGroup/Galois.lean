/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.Etale
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.Flat
import Pi1.Mathlib.AlgebraicGeometry.Limits
import Pi1.Mathlib.CategoryTheory.Limits.MorphismProperty
import Pi1.Mathlib.RingTheory.Ideal.Quotient.Operations
import Pi1.Mathlib.Topology.Connected.Clopen
import Pi1.FundamentalGroup.FiniteEtale
import Pi1.FundamentalGroup.Rank
import Pi1.RingTheory.FinitePresentation
import Pi1.RingTheory.SmoothFlat
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

lemma finite_of_isEtale_of_isAffineHom (X : Scheme.{u}) {Ω : Type u} [Field Ω]
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
  have : Finite X.left := finite_of_isEtale_of_isAffineHom X.left X.hom
  Fintype.ofFinite X.left

/-- -/
@[simps]
def forgetScheme (Ω : Type u) [Field Ω] : FiniteEtale (Spec (.of Ω)) ⥤ FintypeCat.{u} where
  obj X := FintypeCat.of X.left
  map {X Y} f := f.left.base

variable (Ω : Type u) [Field Ω]

lemma _root_.AlgebraicGeometry.IsFiniteEtale.SpecMap_iff {R S : CommRingCat.{u}}
    {f : R ⟶ S} :
    IsFiniteEtale (Spec.map f) ↔ f.hom.FiniteEtale := by
  have := RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.FiniteEtale.respectsIso
  simp only [HasAffineProperty.iff_of_isAffine (P := @IsFiniteEtale), affineAnd, and_iff_right]
  exact MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty RingHom.FiniteEtale)
    (arrowIsoΓSpecOfIsAffine f).symm

instance {ι : Type u} [Finite ι] (R : Type u) [CommRing R] :
    IsFiniteEtale (Spec.map <| CommRingCat.ofHom <| algebraMap R (ι → R)) := by
  rw [IsFiniteEtale.SpecMap_iff]
  simp
  rw [RingHom.finiteEtale_algebraMap_iff]
  constructor

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

instance (S : FintypeCat.{u}) :
    Fintype (Spec (CommRingCat.of (S.carrier → Ω))).toPresheafedSpace :=
  let f : Spec (CommRingCat.of (S.carrier → Ω)) ⟶ Spec (.of Ω) :=
    Spec.map (CommRingCat.ofHom <| algebraMap Ω _)
  have : IsEtale f := by
    rw [HasRingHomProperty.Spec_iff (P := @IsEtale)]
    simp only [CommRingCat.hom_ofHom, RingHom.etale_algebraMap_iff]
    infer_instance
  have : Finite (Spec (CommRingCat.of (S.carrier → Ω))).toPresheafedSpace :=
    finite_of_isEtale_of_isAffineHom _ f
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

instance (X : Scheme.{u}) (R : CommRingCat.{u}) [X.Over (Spec R)] (U : X.Opens) :
    Algebra R Γ(X, U) :=
  ((((X ↘ Spec R)).appLE ⊤ U (by simp)).hom.comp
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm.toRingHom).toAlgebra

instance (X : Scheme.{u}) (R : Type u) [CommRing R] [X.Over (Spec (.of R))] (U : X.Opens) :
    Algebra R Γ(X, U) :=
  ((((X ↘ Spec (.of R))).appLE ⊤ U (by simp)).hom.comp
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.toRingHom).toAlgebra

@[simp]
lemma _root_.CategoryTheory.Iso.commRingCatIsoToRingEquiv_symm_apply {R S : CommRingCat.{u}}
    (e : R ≅ S) (x : S) :
    e.commRingCatIsoToRingEquiv.symm x = e.symm.hom x := rfl

@[simp]
lemma _root_.CategoryTheory.Iso.commRingCatIsoToRingEquiv_symm_toRingHom {R S : CommRingCat.{u}}
    (e : R ≅ S) :
    e.commRingCatIsoToRingEquiv.symm = e.symm.hom.hom := rfl

lemma appLE_comp_algebraMap {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Type u) [CommRing R]
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [f.IsOver (Spec (.of R))]
    (U : Y.Opens) (V : X.Opens) (hUV : V ≤ f ⁻¹ᵁ U) :
    (f.appLE U V hUV).hom.comp (algebraMap R Γ(Y, U)) = algebraMap R Γ(X, V) := by
  ext r
  simp only [RingHom.algebraMap_toAlgebra, Iso.commRingCatIsoToRingEquiv,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    RingEquiv.ofHomInv_symm_apply]
  rw [← CommRingCat.comp_apply]
  rw [Scheme.appLE_comp_appLE]
  simp

set_option pp.proofs true
instance (X : Scheme.{u}) (R : Type u) [CommRing R] [X.Over (Spec (.of R))]
    [IsEtale (X ↘ Spec (.of R))] [IsAffineHom (X ↘ Spec (.of R))] :
    Algebra.Etale R Γ(X, ⊤) := by
  rw [← RingHom.etale_algebraMap_iff, RingHom.algebraMap_toAlgebra]
  apply RingHom.Etale.respectsIso.2
  simp [Scheme.Hom.appLE]
  have : IsAffine X := isAffine_of_isAffineHom (X ↘ Spec (.of R))
  apply HasRingHomProperty.appTop @IsEtale
  infer_instance

instance (X : Scheme.{u}) (R : Type u) [Field R] [X.Over (Spec (.of R))]
    [IsEtale (X ↘ Spec (.of R))] [IsAffineHom (X ↘ Spec (.of R))] :
    Module.Finite R Γ(X, ⊤) :=
  Algebra.FormallyUnramified.finite_of_free R Γ(X, ⊤)

def _root_.AlgebraicGeometry.IsFiniteEtale.isoSpecPi (X : Scheme.{u}) [X.Over (Spec (.of Ω))]
    [IsFiniteEtale (X ↘ Spec (.of Ω))] :
    X ≅ Spec (.of <| Π (m : MaximalSpectrum Γ(X, ⊤)), Γ(X, ⊤) ⧸ m.asIdeal) :=
  have : IsAffine X := isAffine_of_isAffineHom (X ↘ Spec (.of Ω))
  have := Algebra.FormallyUnramified.finite_of_free Ω Γ(X, ⊤)
  have := Algebra.FormallyUnramified.isReduced_of_field Ω Γ(X, ⊤)
  have : IsArtinianRing Γ(X, ⊤) := isArtinian_of_tower Ω inferInstance
  X.isoSpec ≪≫ Scheme.Spec.mapIso ((IsArtinianRing.equivPi _).symm.toCommRingCatIso).op

@[simp]
lemma appTop_left_comp_algebraMap {X Y : FiniteEtale (Spec <| .of Ω)} (f : X ⟶ Y) :
    f.left.appTop.hom.comp (algebraMap Ω Γ(Y.left, ⊤)) = algebraMap Ω Γ(X.left, ⊤) := by
  simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, appLE_comp_algebraMap]

@[simp]
lemma appTop_left_algebraMap {X Y : FiniteEtale (Spec <| .of Ω)} (f : X ⟶ Y) (x : Ω) :
    f.left.appTop.hom (algebraMap Ω Γ(Y.left, ⊤) x) = algebraMap Ω Γ(X.left, ⊤) x :=
  DFunLike.congr_fun (appTop_left_comp_algebraMap Ω f) x

instance {S : Scheme.{u}} (X : FiniteEtale S) : IsFiniteEtale (X.left ↘ S) :=
  X.prop

instance (X : FiniteEtale (Spec (.of Ω))) : IsArtinianRing Γ(X.left, ⊤) :=
  isArtinian_of_tower Ω inferInstance

instance (X : FiniteEtale (Spec (.of Ω))) : _root_.IsReduced Γ(X.left, ⊤) :=
  Algebra.FormallyUnramified.isReduced_of_field Ω Γ(X.left, ⊤)

def _root_.AlgebraicGeometry.IsFiniteEtale.isoSpecFun [IsSepClosed Ω] (X : Scheme.{u})
    [X.Over (Spec (.of Ω))] [IsFiniteEtale (X ↘ Spec (.of Ω))] :
    X ≅ Spec (.of <| X → Ω) :=
  have : IsAffine X := isAffine_of_isAffineHom (X ↘ Spec (.of Ω))
  let i1 := IsFiniteEtale.isoSpecPi Ω X
  have : IsArtinianRing Γ(X, ⊤) := isArtinian_of_tower Ω inferInstance
  let e : X ≃ MaximalSpectrum Γ(X, ⊤) :=
    X.isoSpec.schemeIsoToHomeo.toEquiv.trans IsArtinianRing.primeSpectrumEquivMaximalSpectrum
  have : _root_.IsReduced ↑Γ(X, ⊤) :=
    Algebra.FormallyUnramified.isReduced_of_field Ω Γ(X, ⊤)
  let eo : Γ(X, ⊤) ≃ₐ[Ω] _ := { __ := IsArtinianRing.equivPi Γ(X, ⊤), commutes' := fun r ↦ rfl }
  have : Algebra.FormallyEtale Ω (Π (m : MaximalSpectrum Γ(X, ⊤)), (Γ(X, ⊤) ⧸ m.asIdeal)) :=
    Algebra.FormallyEtale.of_equiv eo
  have (m : MaximalSpectrum Γ(X, ⊤)) : Algebra.FormallyEtale Ω (Γ(X, ⊤) ⧸ m.asIdeal) := by
    rw [Algebra.FormallyEtale.pi_iff] at this
    exact this m
  let _ (m : MaximalSpectrum Γ(X, ⊤)) : Field (Γ(X, ⊤) ⧸ m.asIdeal) :=
    Ideal.Quotient.field m.asIdeal
  have (m : MaximalSpectrum Γ(X, ⊤)) : Algebra.IsSeparable Ω (Γ(X, ⊤) ⧸ m.asIdeal) := by
    rw [← Algebra.FormallyEtale.iff_isSeparable]
    infer_instance
  have hb (m : MaximalSpectrum Γ(X, ⊤)) :
      Function.Bijective (algebraMap Ω (Γ(X, ⊤) ⧸ m.asIdeal)) :=
    ⟨FaithfulSMul.algebraMap_injective _ _,
      IsSepClosed.algebraMap_surjective Ω (Γ(X, ⊤) ⧸ m.asIdeal)⟩
  let a (m : MaximalSpectrum Γ(X, ⊤)) : Γ(X, ⊤) ⧸ m.asIdeal ≃+* Ω :=
    (RingEquiv.ofBijective _ (hb m)).symm
  let o : (Π (m : MaximalSpectrum Γ(X, ⊤)), Γ(X, ⊤) ⧸ m.asIdeal) ≃+* (X → Ω) :=
    (RingEquiv.piCongrRight a).trans (RingEquiv.piCongrLeft (fun _ ↦ Ω) e.symm)
  i1 ≪≫ Scheme.Spec.mapIso o.toCommRingCatIso.symm.op

lemma IsArtinianRing.equivPi_apply (R : Type*) [CommRing R] [IsArtinianRing R] [_root_.IsReduced R]
    (x : R) (m : MaximalSpectrum R) :
    (IsArtinianRing.equivPi R x) m = Ideal.Quotient.mk m.asIdeal x := rfl

@[reassoc (attr := simp)]
lemma _root_.AlgebraicGeometry.IsFiniteEtale.isoSpecFun_hom_SpecMap [IsSepClosed Ω]
    (X : Scheme.{u}) [X.Over (Spec (.of Ω))] [IsFiniteEtale (X ↘ Spec (.of Ω))] :
    (IsFiniteEtale.isoSpecFun Ω X).hom ≫
      Spec.map (CommRingCat.ofHom <| algebraMap Ω (X → Ω)) = X ↘ Spec (.of Ω) := by
  have : IsAffine X := isAffine_of_isAffineHom (X ↘ Spec (.of Ω))
  rw [← cancel_epi X.isoSpec.inv]
  conv_rhs => rw [← Scheme.isoSpec_inv_naturality]
  simp only [IsFiniteEtale.isoSpecFun, IsFiniteEtale.isoSpecPi, RingEquiv.toRingHom_eq_coe,
    Iso.trans_assoc, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, RingEquiv.toCommRingCatIso_hom,
    Scheme.Spec_map, Quiver.Hom.unop_op, Iso.symm_hom, RingEquiv.toCommRingCatIso_inv,
    Category.assoc, Iso.inv_hom_id_assoc, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  congr 1
  have : IsArtinianRing Γ(X, ⊤) := isArtinian_of_tower Ω inferInstance
  have : _root_.IsReduced ↑Γ(X, ⊤) := Algebra.FormallyUnramified.isReduced_of_field Ω Γ(X, ⊤)
  ext x
  apply (IsArtinianRing.equivPi Γ(X, ⊤)).injective
  ext j
  simp [RingHom.algebraMap_toAlgebra]
  rw [IsArtinianRing.equivPi_apply]
  simp [Scheme.Hom.appTop, Scheme.Hom.appLE, Iso.commRingCatIsoToRingEquiv]

--@[simp]
lemma IsArtinianRing.equivPi_naturality_apply (R S : Type*) [CommRing R] [CommRing S]
    [IsArtinianRing R] [IsArtinianRing S] [_root_.IsReduced R] [_root_.IsReduced S]
    (f : R →+* S) (x : R) :
    IsArtinianRing.equivPi S (f x) =
      Pi.ringHom
        (fun m ↦ RingHom.comp
          (by exact Ideal.quotientMap m.asIdeal f (by simp))
          (Pi.evalRingHom _ ⟨Ideal.comap f m.asIdeal, IsArtinianRing.isMaximal_of_isPrime _⟩))
        (IsArtinianRing.equivPi R x) := by
  ext m
  simp [IsArtinianRing.equivPi, IsArtinianRing.quotNilradicalEquivPi]

instance (priority := 900) [IsAffine X] (Y : FiniteEtale X) : IsAffine Y.left :=
  let f : Y.left ⟶ X := Y.hom
  isAffine_of_isAffineHom f

set_option maxHeartbeats 0 in
def forgetInventIso [IsSepClosed Ω] : 𝟭 (FiniteEtale _) ≅ forgetScheme Ω ⋙ inventScheme Ω :=
  NatIso.ofComponents (fun X ↦
    (MorphismProperty.Over.isoMk (IsFiniteEtale.isoSpecFun Ω X.left))) <| fun {X Y} f ↦ by
      apply MorphismProperty.Over.Hom.ext
      simp only [FiniteEtale, Functor.id_obj, Functor.comp_obj, inventScheme_obj,
        forgetScheme_obj_carrier, mk_left, Functor.id_map, IsFiniteEtale.isoSpecFun,
        RingEquiv.toRingHom_eq_coe, MorphismProperty.Comma.comp_hom, Comma.comp_left,
        MorphismProperty.Over.isoMk_hom_left, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
        Iso.symm_hom, RingEquiv.toCommRingCatIso_inv, Scheme.Spec_map, Quiver.Hom.unop_op,
        Functor.comp_map, inventScheme_map, forgetScheme_map, MorphismProperty.Over.homMk_hom,
        Over.homMk_left, Category.assoc]
      simp only [IsFiniteEtale.isoSpecPi, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
        RingEquiv.toCommRingCatIso_hom, Scheme.Spec_map, Quiver.Hom.unop_op, Category.assoc]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [← Spec.map_comp, ← Spec.map_comp]
      rw [← Scheme.isoSpec_hom_naturality_assoc, ← Spec.map_comp]
      congr 2
      ext x
      simp only [CommRingCat.ofHom_comp, Category.assoc, CommRingCat.hom_comp,
        CommRingCat.hom_ofHom, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
        RingEquiv.symm_trans_apply, RingEquiv.piCongrRight_symm, RingEquiv.symm_symm]
      apply (IsArtinianRing.equivPi Γ(X.left, ⊤)).injective
      ext j
      simp only [RingEquiv.apply_symm_apply, RingEquiv.piCongrRight_apply,
        RingEquiv.piCongrLeft_symm_apply, Equiv.symm_symm, RingEquiv.piCongrLeft'_apply,
        Equiv.symm_trans_apply, Homeomorph.coe_symm_toEquiv, Pi.ringHom_apply, Pi.evalRingHom_apply,
        RingEquiv.coe_ofBijective]
      rw [IsArtinianRing.equivPi_naturality_apply]
      simp only [RingEquiv.apply_symm_apply, Pi.ringHom_apply, RingHom.coe_comp,
        Function.comp_apply, Pi.evalRingHom_apply, RingEquiv.piCongrRight_apply,
        RingEquiv.piCongrLeft_symm_apply, Equiv.symm_symm, RingEquiv.piCongrLeft'_apply,
        Equiv.symm_trans_apply, Homeomorph.coe_symm_toEquiv, RingEquiv.coe_ofBijective,
        Ideal.quotientMap_algebraMap, appTop_left_algebraMap, Ideal.Quotient.mk_algebraMap,
        algebraMap.coe_inj]
      congr 1
      simp only [Iso.schemeIsoToHomeo, Scheme.homeoOfIso_symm, Scheme.homeoOfIso_apply,
        Iso.symm_hom]
      rw [← Scheme.comp_base_apply, ← Scheme.isoSpec_inv_naturality]
      simp only [Scheme.comp_coeBase, TopCat.hom_comp, ContinuousMap.comp_apply]
      rfl

def equivFintypeCat [IsSepClosed Ω] : FiniteEtale (Spec <| .of Ω) ≌ FintypeCat.{u} :=
  CategoryTheory.Equivalence.mk (forgetScheme Ω) (inventScheme Ω)
    (forgetInventIso Ω) (inventForgetIso Ω)

instance [IsSepClosed Ω] : (forgetScheme Ω).IsEquivalence :=
  (equivFintypeCat Ω).isEquivalence_functor

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
variable {X}

def fiber : FiniteEtale X ⥤ FintypeCat :=
  pullback ξ ⋙ forgetScheme Ω

variable {ξ} in
def fiberPt {A : FiniteEtale X} (x : (fiber ξ).obj A) : A.left :=
  (pullback.fst A.hom ξ).base x

instance [IsSepClosed Ω] : PreservesFiniteLimits (pullback ξ) := by
  dsimp [pullback]
  apply AffineAnd.preservesFiniteLimits_pullback

instance (X : Type*) [TopologicalSpace X] [LocallyConnectedSpace X] :
    DiscreteTopology (ConnectedComponents X) := by
  rw [← singletons_open_iff_discrete]
  intro i
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
  rw [← ConnectedComponents.isQuotientMap_coe.isOpen_preimage,
    connectedComponents_preimage_singleton]
  exact isOpen_connectedComponent

def _root_.AlgebraicGeometry.Scheme.connCompOpen {X : Scheme.{u}} [Finite (ConnectedComponents X)]
    (i : ConnectedComponents X) : X.Opens :=
  ⟨ConnectedComponents.mk ⁻¹' {i}, by
    rw [ConnectedComponents.isQuotientMap_coe.isOpen_preimage]
    exact isOpen_discrete {i}⟩

-- TODO: find the correct assumptions
def _root_.AlgebraicGeometry.Scheme.connectedComponents (X : Scheme.{u})
      [Finite (ConnectedComponents X)] :
    X.OpenCover where
  J := ConnectedComponents X
  obj c := X.connCompOpen c
  map c := (X.connCompOpen c).ι
  f x := ConnectedComponents.mk x
  covers x := by simp [Scheme.connCompOpen]

instance {X : Scheme.{u}} [Finite (ConnectedComponents X)] (i : ConnectedComponents X) :
    ConnectedSpace (X.connectedComponents.obj i) := by
  apply isConnected_iff_connectedSpace.mp
  simp only [Scheme.connCompOpen, TopologicalSpace.Opens.coe_mk]
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
  rw [connectedComponents_preimage_singleton]
  exact isConnected_connectedComponent

instance {X : Scheme.{u}} [Finite (ConnectedComponents X)] (i : ConnectedComponents X) :
    IsClosedImmersion (X.connectedComponents.map i) where
  base_closed := ⟨(X.connectedComponents.map i).isOpenEmbedding.isEmbedding, by
    simp [Scheme.connectedComponents, Scheme.connCompOpen,
      ConnectedComponents.isQuotientMap_coe.isClosed_preimage]⟩

lemma _root_.AlgebraicGeometry.IsFiniteEtale.isIso_of_isIso_snd {X Y Z : Scheme.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) [IsFiniteEtale f] [PreconnectedSpace Z] [Nonempty Y]
    [IsIso (pullback.snd f g)] : IsIso f := by
  rw [isIso_iff_rank_eq]
  obtain ⟨y⟩ := ‹Nonempty Y›
  ext z
  rw [finrank_eq_const_of_preconnectedSpace f z (g.base y), ← finrank_pullback_snd,
    finrank_eq_one_of_isIso, Pi.one_apply, Pi.one_apply]

instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsFiniteEtale g] :
    IsFiniteEtale (pullback.fst f g) :=
  MorphismProperty.pullback_fst _ _ ‹_›

instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsFiniteEtale f] :
    IsFiniteEtale (pullback.snd f g) :=
  MorphismProperty.pullback_snd _ _ ‹_›

instance _root_.AlgebraicGeometry.IsFiniteEtale.surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [PreconnectedSpace Y] [Nonempty X] [IsFiniteEtale f] :
    Surjective f := by
  rw [← one_le_finrank_iff_surjective]
  obtain ⟨x⟩ := ‹Nonempty X›
  intro y
  rw [finrank_eq_const_of_preconnectedSpace _ _ (f.base x)]
  apply one_le_finrank_map

lemma _root_.AlgebraicGeometry.IsFiniteEtale.isIso_of_isIso_snd' {X Y Z : Scheme.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) [IsFiniteEtale f] [Finite (ConnectedComponents Z)]
    [∀ i : ConnectedComponents Z, Nonempty ↑(Limits.pullback g (Z.connectedComponents.map i))]
    [IsIso (pullback.snd f g)] : IsIso f := by
  show MorphismProperty.isomorphisms _ _
  rw [IsLocalAtTarget.iff_of_openCover (P := MorphismProperty.isomorphisms Scheme.{u})
    Z.connectedComponents]
  intro i
  simp
  dsimp [Scheme.Cover.pullbackHom]
  let g' := pullback.snd g (Z.connectedComponents.map i)
  have : pullback.snd (pullback.snd f (Z.connectedComponents.map i)) g' =
      (pullbackLeftPullbackSndIso f (Z.connectedComponents.map i) g').hom ≫
      (pullback.congrHom rfl pullback.condition.symm).hom ≫
      (pullbackAssoc f g g (Z.connectedComponents.map i)).inv ≫
      (pullback.map _ _ _ _ (pullback.snd _ _) (𝟙 _) (𝟙 _) rfl rfl) := by
    apply pullback.hom_ext <;> simp [g']
  have : IsIso (pullback.snd (pullback.snd f (Z.connectedComponents.map i)) g') := by
    rw [this]
    infer_instance
  apply IsFiniteEtale.isIso_of_isIso_snd _ g'

lemma isIso_of_isIso_left {A B : FiniteEtale X} (f : A ⟶ B) [IsIso f.left] : IsIso f := by
  have : IsIso ((forget X ⋙ Over.forget X).map f) := ‹_›
  exact isIso_of_reflects_iso f (forget X ⋙ Over.forget X)

instance [ConnectedSpace X] (Y : FiniteEtale X) : Finite (ConnectedComponents Y.left) := by
  have : ConnectedSpace ↑↑((Functor.fromPUnit X).obj Y.right).toPresheafedSpace := by
    dsimp
    infer_instance
  exact Y.hom.isOpenMap.finite_connectedComponents_of_finite_preimage_singleton Y.hom.continuous
    Y.hom.isClosedMap (fun y ↦ IsFinite.finite_preimage_singleton _ y)

open MorphismProperty

instance {Y : Scheme.{u}} [Nonempty Y] (g : Y ⟶ X) [ConnectedSpace X] :
    (pullback g).ReflectsIsomorphisms := by
  constructor
  intro A B f hf
  have : IsIso f.left := by
    have : (pullbackRightPullbackFstIso B.hom g f.left).inv ≫
        pullback.snd f.left (pullback.fst B.hom g) =
          (pullback.congrHom (by simp) rfl).hom ≫ ((pullback g).map f).left := by
      apply pullback.hom_ext <;> simp
    have : IsIso (pullback.snd f.left (pullback.fst B.hom g)) := by
      rw [← isomorphisms.iff, ← cancel_left_of_respectsIso (.isomorphisms _)
        (pullbackRightPullbackFstIso B.hom g f.left).inv, isomorphisms.iff, this]
      infer_instance
    have (i : _root_.ConnectedComponents B.left) :
        Nonempty ↑(Limits.pullback (pullback.fst B.hom g) (B.left.connectedComponents.map i)) := by
      let e := pullbackRightPullbackFstIso B.hom g (B.left.connectedComponents.map i)
      have : Nonempty ↑(Limits.pullback (B.left.connectedComponents.map i ≫ B.hom) g) := by
        obtain ⟨y⟩ := ‹Nonempty Y›
        have : IsFiniteEtale (B.left.connectedComponents.map i ≫ B.hom) := by
          apply MorphismProperty.comp_mem
          constructor
          infer_instance
        have : Nonempty (B.left.connectedComponents.obj i) := inferInstance
        have : Surjective (B.left.connectedComponents.map i ≫ B.hom) := by
          convert IsFiniteEtale.surjective _
          simp
          infer_instance
          infer_instance
          infer_instance
        obtain ⟨z, hz⟩ := (B.left.connectedComponents.map i ≫ B.hom).surjective (g.base y)
        obtain ⟨o, _⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hz
        use o
      exact ((pullbackSymmetry _ _).hom ≫ (pullbackRightPullbackFstIso B.hom g
        (B.left.connectedComponents.map i)).hom).homeomorph.nonempty
    apply IsFiniteEtale.isIso_of_isIso_snd' f.left (pullback.fst B.hom g)
  apply isIso_of_isIso_left

instance [ConnectedSpace X] [IsSepClosed Ω] : (fiber ξ).ReflectsIsomorphisms := by
  dsimp [fiber]
  infer_instance

instance [IsSepClosed Ω] : PreservesFiniteColimits (fiber ξ) := by
  dsimp [fiber]
  infer_instance

open PreGaloisCategory

/-- If `X` is a connected scheme and `ξ : Spec Ω ⟶ X` is a geometric point,
taking fibers over `ξ` is a fiber functor. -/
instance [ConnectedSpace X] [IsSepClosed Ω] : FiberFunctor (fiber ξ) where
  preservesTerminalObjects := by dsimp [fiber]; infer_instance
  preservesPullbacks := by dsimp [fiber]; infer_instance
  preservesQuotientsByFiniteGroups _ _ := inferInstance

/-- If `X` is a connected scheme, the category of finite étale schemes over `X`
is a Galois category. -/
instance [ConnectedSpace X] : GaloisCategory (FiniteEtale X) where
  hasFiberFunctor := by
    have : Nonempty X := inferInstance
    let x : X := ‹Nonempty X›.some
    let k : Type u := X.residueField x
    let Ω : Type u := AlgebraicClosure k
    let ξ : Spec (.of Ω) ⟶ X :=
      Spec.map (CommRingCat.ofHom <| algebraMap k Ω) ≫ X.fromSpecResidueField x
    exact ⟨fiber ξ, ⟨inferInstance⟩⟩

/-- The étale fundamental group of a connected scheme `X` at the geometric point `ξ` is
the automorphism group of the fiber functor at `ξ`. -/
notation:arg "π₁ᵉᵗ" "(" x ")" => Aut (fiber x)

example : IsTopologicalGroup π₁ᵉᵗ(ξ) := inferInstance
example : T2Space π₁ᵉᵗ(ξ) := inferInstance
example : TotallyDisconnectedSpace π₁ᵉᵗ(ξ) := inferInstance
example : CompactSpace π₁ᵉᵗ(ξ) := inferInstance

end AlgebraicGeometry.FiniteEtale
