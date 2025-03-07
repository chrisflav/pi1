import Mathlib

universe u

open TensorProduct

namespace Algebra

namespace Extension

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (P : Extension R S)
variable (T : Type*) [CommRing T] [Algebra R T]

lemma exact_hCotangentι_cotangentComplex :
    Function.Exact h1Cotangentι P.cotangentComplex := by
  rw [LinearMap.exact_iff]
  symm
  apply Submodule.range_subtype

attribute [local instance] Algebra.TensorProduct.rightAlgebra

noncomputable
def toBaseChange : P.Hom (P.baseChange (T := T)) where
  toRingHom := TensorProduct.includeRight.toRingHom
  toRingHom_algebraMap x := by simp [baseChange]
  algebraMap_toRingHom x := rfl

end Extension

namespace Generators

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (P : Generators R S)
variable (T : Type u) [CommRing T] [Algebra R T]

noncomputable
def baseChangeFromBaseChange :
    (P.toExtension.baseChange (T := T)).Hom (P.baseChange (T := T)).toExtension where
  toRingHom := (MvPolynomial.algebraTensorAlgEquiv R T).toRingHom
  toRingHom_algebraMap x := by
    simp only [toExtension_Ring, Extension.baseChange, toExtension_commRing, toExtension_algebra₂,
      AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
      TensorProduct.algebraMap_apply, id.map_eq_id, RingHom.id_apply, MvPolynomial.algebraMap_eq]
    show (MvPolynomial.algebraTensorAlgEquiv R T) (x ⊗ₜ[R] 1) = MvPolynomial.C x
    simp only [MvPolynomial.algebraTensorAlgEquiv_tmul, map_one, smul_def,
      MvPolynomial.algebraMap_eq, mul_one]
  algebraMap_toRingHom x := by
    simp only [Extension.baseChange, toExtension_Ring, toExtension_commRing, toExtension_algebra₂,
      AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
      algebraMap_apply, id.map_eq_id, RingHomCompTriple.comp_apply] at x ⊢
    show (MvPolynomial.aeval P.baseChange.val) (MvPolynomial.algebraTensorAlgEquiv R T x) = _
    induction x with
    | zero => simp
    | add x y hx hy =>
      rw [map_add, RingHom.map_add, map_add, hx, hy]
    | tmul t x =>
      simp only [MvPolynomial.algebraTensorAlgEquiv_tmul, map_smul]
      rw [Algebra.smul_def]
      simp only [TensorProduct.algebraMap_apply, id.map_eq_id, RingHom.id_apply, baseChange,
        ofSurjective, AlgHom.toRingHom_eq_coe, MvPolynomial.aeval_map_algebraMap]
      induction x using MvPolynomial.induction_on with
      | h_C r =>
        simp only [MvPolynomial.algHom_C, TensorProduct.algebraMap_apply,
          TensorProduct.tmul_mul_tmul, mul_one, RingHom.algebraMap_toAlgebra,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
        rw [mul_comm, ← Algebra.smul_def, ← smul_tmul', ← tmul_smul, Algebra.smul_def, mul_one]
      | h_X p i hp =>
        simp only [map_mul, MvPolynomial.aeval_X]
        rw [← mul_assoc, hp]
        simp [RingHom.algebraMap_toAlgebra]
      | h_add p q hp hq =>
        simp only [map_add, mul_add, hp, hq]
        rw [tmul_add, RingHom.map_add]

noncomputable
def baseChangeToBaseChange :
    (P.baseChange (T := T)).toExtension.Hom (P.toExtension.baseChange (T := T)) where
  toRingHom := (MvPolynomial.algebraTensorAlgEquiv R T).symm.toRingHom
  algebraMap_toRingHom x := by
    have := (P.baseChangeFromBaseChange T).algebraMap_toRingHom <|
      (MvPolynomial.algebraTensorAlgEquiv R T).symm.toRingHom x
    simp only [toExtension_Ring, toExtension_commRing, toExtension_algebra₂,
      baseChangeFromBaseChange, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.toRingEquiv_toRingHom, AlgEquiv.symm_toRingEquiv, RingHom.coe_coe, algebraMap_apply,
      id.map_eq_id, RingHomCompTriple.comp_apply] at this
    convert this.symm
    show _ = (MvPolynomial.aeval P.baseChange.val)
      ((MvPolynomial.algebraTensorAlgEquiv R T) (((MvPolynomial.algebraTensorAlgEquiv R T)).symm x))
    simp only [id.map_eq_id, toExtension_Ring, toExtension_commRing, toExtension_algebra₂,
      algebraMap_apply, MvPolynomial.map_aeval, RingHomCompTriple.comp_eq, baseChange_val,
      RingHom.id_apply, MvPolynomial.coe_eval₂Hom, AlgEquiv.apply_symm_apply]
    rfl
  toRingHom_algebraMap x := by
    show (MvPolynomial.algebraTensorAlgEquiv R T).symm (MvPolynomial.C x) =
      (algebraMap T P.toExtension.baseChange.Ring) x
    rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    rfl

end Generators

end Algebra
