/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Pi1.FundamentalGroup.Galois
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

universe u

open CategoryTheory PreGaloisCategory

section

@[simp]
lemma CategoryTheory.Iso.commRingCatIsoToRingEquiv_symm {R S : CommRingCat}
    (e : R ≅ S) :
    e.symm.commRingCatIsoToRingEquiv = e.commRingCatIsoToRingEquiv.symm :=
  rfl

@[simp]
lemma CategoryTheory.Iso.ofHom_commRingCatIsoToRingEquiv {R S : CommRingCat}
    (e : R ≅ S) :
    CommRingCat.ofHom e.commRingCatIsoToRingEquiv = e.hom :=
  rfl

@[simp]
lemma CategoryTheory.Iso.ofHom_commRingCatIsoToRingEquiv_symm {R S : CommRingCat}
    (e : R ≅ S) :
    CommRingCat.ofHom e.commRingCatIsoToRingEquiv.symm = e.inv :=
  rfl

end

-- from mathlib, remove after bumping
lemma IntermediateField.finite_of_fg_of_isAlgebraic {F E : Type*}
    [Field F] [Field E] [Algebra F E]
    (h : IntermediateField.FG (⊤ : IntermediateField F E)) [Algebra.IsAlgebraic F E] :
    Module.Finite F E := by
  obtain ⟨s, hs⟩ := h
  have : Algebra.FiniteType F E := by
    use s
    rw [← IntermediateField.adjoin_algebraic_toSubalgebra
      (fun x hx ↦ Algebra.IsAlgebraic.isAlgebraic x)]
    simpa [← IntermediateField.toSubalgebra_inj] using hs
  exact Algebra.IsIntegral.finite

@[simp]
lemma IntermediateField.map_top {F E E' : Type*} [Field F] [Field E] [Field E'] [Algebra F E]
    [Algebra F E'] (f : E →ₐ[F] E') :
    map f (⊤ : IntermediateField F E) = f.fieldRange := by
  ext : 1
  simp only [map, top_toSubalgebra, Algebra.map_top, AlgHom.mem_fieldRange]
  rfl

lemma IntermediateField.FG.finite_of_isAlgebraic {F E : Type*}
    [Field F] [Field E] [Algebra F E]
    {L : IntermediateField F E} (hL : L.FG)
    [Algebra.IsAlgebraic F E] :
    Module.Finite F L := by
  apply IntermediateField.finite_of_fg_of_isAlgebraic
  obtain ⟨s, hs⟩ := hL
  use s.preimage L.subtype L.subtype_injective.injOn
  apply IntermediateField.map_injective (IsScalarTower.toAlgHom F L E)
  simp only [Subalgebra.toSubsemiring_subtype, coe_type_toSubalgebra, RingHom.coe_coe,
    Finset.coe_preimage, IntermediateField.adjoin_map]
  convert hs
  · show L.val '' (L.val ⁻¹' _) = _
    rw [Set.image_preimage_eq_of_subset]
    simp [← hs, subset_adjoin]
  · ext
    simp

section

variable {R A B C : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
  [Algebra R A] [Algebra R B] [Algebra R C]

@[simp]
lemma AlgEquiv.toRingHom_trans (f : A ≃ₐ[R] B) (g : B ≃ₐ[R] C) :
    (f.trans g : A →+* C) = (g : B →+* C).comp f :=
  rfl

@[simp]
lemma AlgEquiv.toRingHom_refl :
    (AlgEquiv.refl (R := R) (A₁ := A) : A →+* A) = RingHom.id _ :=
  rfl

end

section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

instance (L : Type*) [Field L] [Algebra k L] : MulAction (K ≃ₐ[k] K) (L →ₐ[k] K) where
  smul g x := (g : _ →ₐ[k] _).comp x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

--instance (L : Type*) [Field L] [Algebra k L] :
--    letI : TopologicalSpace (L →ₐ[k] K) := ⊥
--    ContinuousSMul (K ≃ₐ[k] K) (L →ₐ[k] K) := by
--  letI : TopologicalSpace (L →ₐ[k] K) := ⊥
--  constructor
--  sorry

lemma AlgEquiv.smul_algHom_def (L : Type*) [Field L] [Algebra k L]
    (g : K ≃ₐ[k] K) (x : L →ₐ[k] K) :
    g • x = (g : _ →ₐ[k] _).comp x :=
  rfl

instance (L : Type*) [Field L] [Algebra k L] [Algebra L K] [IsScalarTower k L K] [Normal k L]
    [Normal k K] :
    MulAction.IsPretransitive (K ≃ₐ[k] K) (L →ₐ[k] K) := by
  constructor
  intro x y
  obtain ⟨σx, (hx : σx.restrictNormal _ = _)⟩ :=
    AlgEquiv.restrictNormalHom_surjective K (x.restrictNormal' L)
  obtain ⟨σy, (hy : σy.restrictNormal _ = _)⟩ :=
    AlgEquiv.restrictNormalHom_surjective K (y.restrictNormal' L)
  use σx.symm.trans σy
  rw [AlgEquiv.smul_algHom_def]
  ext a
  have hy : y a = σy (algebraMap _ _ a) := by
    simp [← AlgEquiv.restrictNormal_commutes, hy, AlgHom.restrictNormal']
  have hx : x a = σx (algebraMap _ _ a) := by
    simp [← AlgEquiv.restrictNormal_commutes, hx, AlgHom.restrictNormal']
  simp [hx, hy]

end

namespace AlgebraicGeometry

namespace FiniteEtale

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ S)

def fiberObjEquivHom (X : FiniteEtale S) : (fiber ξ).obj X ≃ (Over.mk ξ ⟶ X.toComma) where
  toFun x := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

@[simp]
lemma fiberObjEquivHom_symm_naturality {X Y : FiniteEtale S} (f : X ⟶ Y) (x) :
    (fiber ξ).map f ((fiberObjEquivHom ξ X).symm x) = (fiberObjEquivHom ξ Y).symm (x ≫ f.hom) :=
  sorry

@[reassoc]
lemma fiberObjEquivHom_naturality {X Y : FiniteEtale S} (f : X ⟶ Y) (x) :
    (fiberObjEquivHom ξ X x) ≫ f.hom = fiberObjEquivHom ξ Y ((fiber ξ).map f x) :=
  sorry

noncomputable
def fiberIsoCoyoneda :
    fiber ξ ⋙ CategoryTheory.forget FintypeCat ≅ forget _ ⋙ coyoneda.obj ⟨Over.mk ξ⟩ :=
  NatIso.ofComponents (fun X ↦ (equivEquivIso (fiberObjEquivHom ξ X)))
  sorry

unif_hint (X : FiniteEtale S) where
  ⊢ (forget S ⋙ coyoneda.obj ⟨Over.mk ξ⟩).obj X ≟ (Over.mk ξ ⟶ X.toComma)

variable (k K Ω : Type u) [Field k] [Field K] [Algebra k K] [Field Ω] [Algebra k Ω]
  [Algebra K Ω] [IsScalarTower k K Ω]

scoped notation3:arg "fib " k:arg K:arg =>
  FiniteEtale.fiber (Spec.map (CommRingCat.ofHom <| algebraMap k K))

scoped notation3:arg "ξ " k:arg K:arg => Spec.map (CommRingCat.ofHom <| algebraMap k K)

noncomputable
instance (X : FiniteEtale (Spec (.of k))) :
    SMul (K ≃ₐ[k] K) (Over.mk (ξ k K) ⟶ X.toComma) where
  smul g x := Over.homMk (Spec.map (CommRingCat.ofHom g))
    (by
      dsimp only [Over.mk_left, Functor.const_obj_obj, Over.mk_hom]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← AlgEquiv.toAlgHom_toRingHom,
      AlgHom.comp_algebraMap]) ≫ x

@[simp]
lemma algEquiv_smul_hom {X : FiniteEtale (Spec (.of k))} (g : K ≃ₐ[k] K)
    (x : Over.mk (ξ k K) ⟶ X.toComma) :
    (g • x).left = Spec.map (CommRingCat.ofHom g) ≫ x.left :=
  rfl

variable (X : FiniteEtale (Spec (.of k)))

noncomputable
instance : MulAction (K ≃ₐ[k] K) (Over.mk (ξ k K) ⟶ X.toComma) where
  smul g x := Over.homMk (Spec.map (CommRingCat.ofHom g))
    (by
      dsimp only [Over.mk_left, Functor.const_obj_obj, Over.mk_hom]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← AlgEquiv.toAlgHom_toRingHom,
      AlgHom.comp_algebraMap]) ≫ x
  one_smul x := by ext1; simp [AlgEquiv.aut_one]
  mul_smul g h x := by ext1; simp [AlgEquiv.aut_mul]

scoped instance : TopologicalSpace (Over.mk (ξ k K) ⟶ X.toComma) := ⊥

instance : ContinuousSMul (K ≃ₐ[k] K) (Over.mk (ξ k K) ⟶ X.toComma) where
  continuous_smul :=
    sorry

noncomputable
instance : MulAction (K ≃ₐ[k] K) ((forget _ ⋙ coyoneda.obj ⟨Over.mk (ξ k K)⟩).obj X) :=
  fast_instance% inferInstanceAs <| MulAction (K ≃ₐ[k] K) (Over.mk (ξ k K) ⟶ X.toComma)

noncomputable
instance (X : FiniteEtale (Spec (.of k))) : SMul (K ≃ₐ[k] K) ((fib k K).obj X) where
  smul g x := (fiberIsoCoyoneda (ξ k K)).inv.app X <| g • (((fiberIsoCoyoneda (ξ k K)).hom.app X) x)

lemma algEquiv_smul_fiber_def (g : K ≃ₐ[k] K) (x : (fib k K).obj X) :
    g • x = (fiberObjEquivHom (ξ k K) X).symm (g • ((fiberObjEquivHom (ξ k K) X) x)) :=
  rfl

noncomputable
instance (X : FiniteEtale (Spec (.of k))) : MulAction (K ≃ₐ[k] K) ((fib k K).obj X) where
  one_smul x := by simp [algEquiv_smul_fiber_def]
  mul_smul g h x := by simp [algEquiv_smul_fiber_def, mul_smul]

lemma isField_of_isConnected (X : FiniteEtale (Spec (.of k))) [IsConnected X] :
    IsField Γ(X.left, ⊤) :=
  sorry

noncomputable instance (X : FiniteEtale (Spec (.of k))) [IsConnected X] : Field Γ(X.left, ⊤) :=
  (isField_of_isConnected _ X).toField

noncomputable
def homEquivAlgHom (X : FiniteEtale (Spec (.of k))) :
    (Over.mk (ξ k K) ⟶ X.toComma) ≃ (Γ(X.left, ⊤) →ₐ[k] K) where
  toFun x :=
    { __ := RingHom.comp (Scheme.ΓSpecIso _).hom.hom x.left.appTop.hom,
      commutes' a := by
        have := congr((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of K)).hom)
          ($(Over.w x).appTop.hom
            ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm a)))
        dsimp only [Functor.const_obj_obj, Over.mk_left, Scheme.comp_app,
          TopologicalSpace.Opens.map_top, CommRingCat.hom_comp, RingHom.coe_comp,
          Function.comp_apply, Functor.id_obj, Over.mk_hom] at this
        dsimp only [Over.mk_left, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
          MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply]
        rw [RingHom.algebraMap_toAlgebra]
        dsimp [Scheme.Hom.appTop]
        convert this
        · simp [Scheme.Hom.appLE]
        · dsimp [Iso.commRingCatIsoToRingEquiv]
          rw [← CommRingCat.comp_apply]
          rw [← CommRingCat.comp_apply]
          rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
          simp
        }
  invFun x := Over.homMk
      (Spec.map (CommRingCat.ofHom x.toRingHom) ≫ X.left.isoSpec.inv) <| by
    have := x.comp_algebraMap
    dsimp
    rw [← this]
    simp only [Category.assoc, CommRingCat.ofHom_comp, Spec.map_comp]
    congr
    rw [RingHom.algebraMap_toAlgebra]
    dsimp only [OverClass.fromOver_over, RingEquiv.toRingHom_eq_coe, CommRingCat.ofHom_comp,
      CommRingCat.ofHom_hom]
    rw [Spec.map_comp, Scheme.Hom.appLE]
    simp only [TopologicalSpace.Opens.map_top, homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv]
    rfl
  left_inv x := by
    ext1
    dsimp
    rw [Spec.map_comp, Category.assoc, Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv,
      ← Spec.map_comp_assoc, Iso.inv_hom_id]
    simp
  right_inv x := by
    apply AlgHom.coe_ringHom_injective
    dsimp
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Category.assoc, Scheme.ΓSpecIso_naturality]
    rw [← AlgebraicGeometry.Scheme.toSpecΓ_appTop, ← Scheme.comp_app_top_assoc, ← Scheme.Hom.appTop]
    simp

lemma homEquivAlgHom_smul (X : FiniteEtale (Spec (.of k))) [IsConnected X] (g : K ≃ₐ[k] K) (x) :
    (homEquivAlgHom k K X) (g • x) = g • (homEquivAlgHom k K X x) := by
  rw [homEquivAlgHom]
  dsimp only [Over.mk_left, AlgHom.toRingHom_eq_coe, Equiv.coe_fn_mk, algEquiv_smul_hom,
    Scheme.comp_app, TopologicalSpace.Opens.map_top, CommRingCat.hom_comp]
  rw [AlgEquiv.smul_algHom_def]
  ext1 a
  dsimp only [AlgHom.coe_mk, RingHom.coe_comp, Function.comp_apply, AlgHom.coe_comp, AlgHom.coe_coe]
  rw [← CommRingCat.comp_apply]
  simp

instance isGalois_of_isGalois (X : FiniteEtale (Spec (.of k))) [IsGalois X] :
    IsGalois k Γ(X.left, ⊤) :=
  sorry

instance [IsGalois k K] (X : FiniteEtale (Spec (.of k))) [IsGalois X] :
    MulAction.IsPretransitive (K ≃ₐ[k] K) (Over.mk (ξ k K) ⟶ X.toComma) := by
  constructor
  intro x y
  letI : Algebra Γ(X.left, ⊤) K := (homEquivAlgHom k K X x).toAlgebra
  obtain ⟨g, h⟩ := MulAction.exists_smul_eq (K ≃ₐ[k] K)
    (homEquivAlgHom k K X x) (homEquivAlgHom k K X y)
  use g
  apply (homEquivAlgHom k K X).injective
  rwa [homEquivAlgHom_smul]

lemma eq_one_of_smul_eq [Algebra.IsSeparable k K] (g : K ≃ₐ[k] K)
    (H : ∀ (X : FiniteEtale (Spec (.of k))) (x : (Over.mk (ξ k K) ⟶ X.toComma)), g • x = x) :
    g = 1 := by
  ext x
  let L := IntermediateField.adjoin k {x}
  have : IsFiniteEtale (ξ k L) := by
    rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finiteEtale_algebraMap_iff]
    have : Algebra.IsIntegral k L := inferInstance
    have : Module.Finite k L :=
      (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x)).finite_of_isAlgebraic
    have : Algebra.Etale k L :=
      ⟨.of_isSeparable k L, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
    constructor
  let X : FiniteEtale (Spec (.of k)) := FiniteEtale.mk (ξ k L)
  let y : Over.mk (ξ k K) ⟶ X.toComma := by
    refine Over.homMk (Spec.map <| CommRingCat.ofHom L.subtype) ?_
    simp [X, ← Spec.map_comp, Spec.map_injective.eq_iff, ConcreteCategory.ext_iff, RingHom.ext_iff]
  specialize H X y
  rw [CommaMorphism.ext_iff] at H
  simp only [Over.mk_left, Subalgebra.toSubsemiring_subtype,
    IntermediateField.coe_type_toSubalgebra, algEquiv_smul_hom, Over.homMk_left,
    CostructuredArrow.right_eq_id, and_true, y, X] at H
  rw [← Spec.map_comp, Spec.map_injective.eq_iff, ConcreteCategory.ext_iff, RingHom.ext_iff] at H
  exact H ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩

variable [IsGalois k K]

instance : IsFundamentalGroup (fib k K) (K ≃ₐ[k] K) where
  naturality g X Y f x := by
    apply (fiberObjEquivHom (ξ k K) Y).injective
    rw [algEquiv_smul_fiber_def, algEquiv_smul_fiber_def]
    simp only [fiberObjEquivHom_symm_naturality, Equiv.apply_symm_apply]
    ext1
    simp only [Over.mk_left, Over.comp_left, algEquiv_smul_hom, Category.assoc]
    rw [← Over.comp_left, fiberObjEquivHom_naturality]
  continuous_smul X := by
    constructor
    let u : (K ≃ₐ[k] K) × (fib k K).obj X → (fib k K).obj X :=
      (fiberObjEquivHom (ξ k K) X).symm ∘ (fun p ↦ p.1 • p.2) ∘
      fun p ↦ (p.1, fiberObjEquivHom (ξ k K) X p.2)
    show Continuous u
    dsimp [u]
    fun_prop
  transitive_of_isGalois X _ := by
    constructor
    intro x y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (K ≃ₐ[k] K)
      (fiberObjEquivHom _ _ x) (fiberObjEquivHom _ _ y)
    use g
    rw [algEquiv_smul_fiber_def]
    apply (fiberObjEquivHom (ξ k K) X).injective
    simp [hg]
  non_trivial' g H := by
    apply eq_one_of_smul_eq
    intro X x
    apply (fiberObjEquivHom (ξ k K) X).symm.injective
    specialize H X ((fiberObjEquivHom (ξ k K) X).symm x)
    rwa [algEquiv_smul_fiber_def, Equiv.apply_symm_apply] at H

end FiniteEtale

end AlgebraicGeometry
