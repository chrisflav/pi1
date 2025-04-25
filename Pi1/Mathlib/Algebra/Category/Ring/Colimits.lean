import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Pi1.Mathlib.RingTheory.IsTensorProduct

universe u

open CategoryTheory Limits TensorProduct

namespace CommRingCat

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
lemma isPushout_iff_isPushout {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {R' S' : Type u} [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S'] [Algebra R' S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] :
    IsPushout (ofHom <| algebraMap R R') (ofHom <| algebraMap R S)
      (ofHom <| algebraMap R' S') (ofHom <| algebraMap S S') ↔ Algebra.IsPushout R R' S S' := by
  refine ⟨fun h ↦ ?_, fun h ↦ isPushout_of_isPushout ..⟩
  let e := ((CommRingCat.isPushout_tensorProduct R R' S).isoPushout ≪≫
      h.isoPushout.symm).commRingCatIsoToRingEquiv
  dsimp at e
  have h2 (r : R') : (CommRingCat.isPushout_tensorProduct R R' S).isoPushout.hom
      (r ⊗ₜ 1) = (pushout.inl (ofHom _) (ofHom _)) r :=
    congr($((CommRingCat.isPushout_tensorProduct R R' S).inl_isoPushout_hom).hom r)
  let e' : R' ⊗[R] S ≃ₐ[R'] S' := {
    __ := e
    commutes' r := by
      simp only [Iso.commRingCatIsoToRingEquiv, AlgHom.toRingHom_eq_coe, Iso.trans_hom,
        Iso.symm_hom, hom_comp, Iso.trans_inv, Iso.symm_inv, RingEquiv.toEquiv_eq_coe,
        Algebra.TensorProduct.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply,
        Equiv.toFun_as_coe, EquivLike.coe_coe, RingEquiv.ofHomInv_apply, RingHom.coe_comp,
        Function.comp_apply, h2, e]
      rw [← CommRingCat.comp_apply]
      simp }
  refine Algebra.IsPushout.of_equiv _ e' ?_
  ext s
  have h1 : (CommRingCat.isPushout_tensorProduct R R' S).isoPushout.hom
      (algebraMap S (R' ⊗[R] S) s) = (pushout.inr (ofHom _) (ofHom _)) s :=
    congr($((CommRingCat.isPushout_tensorProduct R R' S).inr_isoPushout_hom).hom s)
  simp only [Iso.commRingCatIsoToRingEquiv, AlgHom.toRingHom_eq_coe, Iso.trans_hom, Iso.symm_hom,
    hom_comp, Iso.trans_inv, Iso.symm_inv, RingEquiv.toEquiv_eq_coe, AlgEquiv.toRingEquiv_eq_coe,
    RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp, RingHom.coe_coe,
    AlgEquiv.coe_mk, EquivLike.coe_coe, Function.comp_apply, RingEquiv.ofHomInv_apply, h1, e', e]
  rw [← CommRingCat.comp_apply]
  simp

end CommRingCat
