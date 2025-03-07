import Mathlib
import Pi1.RingTheory.KaehlerBaseChange
import Pi1.RingTheory.Cotangent.SpaceBaseChange
import Pi1.RingTheory.FiveLemma

noncomputable section

universe u

open TensorProduct

namespace TensorProduct.AlgebraTensorModule

variable {R : Type*} (A B : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable {N : Type*} [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]

def tensorQuotientEquiv (n : Submodule B N) :
    M ⊗[R] (N ⧸ n) ≃ₗ[A] (M ⊗[R] N) ⧸ LinearMap.range (lTensor A M (n.subtype.restrictScalars R)) :=
  let f : M ⊗[R] (N ⧸ n) ≃ₗ[R]
      M ⊗[R] N ⧸ LinearMap.range (lTensor A M (n.subtype.restrictScalars R)) :=
    TensorProduct.tensorQuotientEquiv M (n.restrictScalars R)
  f.toAddEquiv.toLinearEquiv <| fun c x ↦ by
    simp
    induction x with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul x y =>
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [smul_tmul']
    rfl

@[simp]
lemma tensorQuotientEquiv_apply_tmul (n : Submodule B N) (x : M) (y : N) :
    tensorQuotientEquiv A B M n (x ⊗ₜ[R] Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x ⊗ₜ[R] y) :=
  rfl

@[simp]
lemma tensorQuotientEquiv_symm_apply_mk_tmul (n : Submodule B N) (x : M) (y : N) :
    (tensorQuotientEquiv A B M n).symm (Submodule.Quotient.mk (x ⊗ₜ[R] y)) =
      x ⊗ₜ[R] Submodule.Quotient.mk y :=
  rfl

end TensorProduct.AlgebraTensorModule

namespace Algebra.TensorProduct

variable {R : Type*} (S T A : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T]
  [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

lemma map_includeRight_eq (I : Ideal T) :
    (I.map (includeRight (A := A) (R := R))).restrictScalars S =
      LinearMap.range ((AlgebraTensorModule.lTensor S A) (I.subtype.restrictScalars R)) := by
  have := I.map_includeRight_eq (R := R) (A := A)
  rwa [Submodule.ext_iff] at this ⊢

def tensorQuotientEquiv (I : Ideal T) :
    A ⊗[R] (T ⧸ I) ≃ₐ[S] (A ⊗[R] T) ⧸ I.map (includeRight (A := A) (R := R)) :=
  let f : A ⊗[R] (T ⧸ I) ≃ₗ[S]
      A ⊗[R] T ⧸ LinearMap.range ((AlgebraTensorModule.lTensor S A)
        (I.subtype.restrictScalars R)) :=
    AlgebraTensorModule.tensorQuotientEquiv (R := R) S T A I
  have heq : LinearMap.range ((AlgebraTensorModule.lTensor S A)
      (I.subtype.restrictScalars R)) =
        (I.map (includeRight (A := A) (R := R))).restrictScalars S := by
    symm
    have := I.map_includeRight_eq (R := R) (A := A)
    rwa [Submodule.ext_iff] at this ⊢
  let g : (A ⊗[R] T ⧸ LinearMap.range ((AlgebraTensorModule.lTensor S A)
      (I.subtype.restrictScalars R))) ≃ₗ[S]
      A ⊗[R] T ⧸ (I.map (includeRight (A := A) (R := R))).restrictScalars S :=
    Submodule.quotEquivOfEq _ _ heq
  let e : A ⊗[R] (T ⧸ I) ≃ₗ[S] (A ⊗[R] T) ⧸ I.map (includeRight (A := A) (R := R)) :=
    f ≪≫ₗ g
  AlgEquiv.ofLinearEquiv e rfl sorry

@[simp]
lemma tensorQuotientEquiv_apply_tmul (I : Ideal T) (a : A) (t : T) :
    tensorQuotientEquiv (R := R) S T A I (a ⊗ₜ t) = a ⊗ₜ[R] t :=
  rfl

@[simp]
lemma tensorQuotientEquiv_symm_apply_tmul (I : Ideal T) (a : A) (t : T) :
    (tensorQuotientEquiv (R := R) S T A I).symm (a ⊗ₜ[R] t) = a ⊗ₜ[R] (Ideal.Quotient.mk I t) :=
  rfl

end Algebra.TensorProduct

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (T : Type*) [CommRing T] [Algebra R T]
variable (I : Ideal S)

example : T ⊗[R] I →ₗ[T] T ⊗[R] S :=
  AlgebraTensorModule.lTensor T T I.subtype

attribute [local instance] Algebra.TensorProduct.rightAlgebra

--#check I.map (algebraMap S (T ⊗[R] S))

variable {I} in
def Cotangent.lift {M : Type*} [AddCommGroup M] [Module R M]
    (f : I →ₗ[R] M) (hf : ∀ (x y : I), f (x * y) = 0) :
    I.Cotangent →ₗ[R] M :=
  sorry

variable {I} in
@[simp]
lemma Cotangent.lift_toCotangent {M : Type*} [AddCommGroup M] [Module R M]
    (f : I →ₗ[R] M) (hf : ∀ (x y : I), f (x * y) = 0)
    (x : I) :
    Cotangent.lift f hf (I.toCotangent x) = f x :=
  sorry

variable (R)

def tensorCotangentTo :
    T ⊗[R] I.Cotangent →ₗ[T] (I.map <| algebraMap S (T ⊗[R] S)).Cotangent :=
  LinearMap.liftBaseChange T <|
    Cotangent.lift
      ((map (algebraMap S (T ⊗[R] S)) I).toCotangent.restrictScalars R ∘ₗ
        (Algebra.idealMap _ I).restrictScalars R)
      (fun x y ↦ sorry)

@[simp]
lemma tensorCotangentTo_tmul (t : T) (x : I) :
    tensorCotangentTo R T I (t ⊗ₜ[R] I.toCotangent x) =
      t • (I.map (algebraMap S (T ⊗[R] S))).toCotangent ((Algebra.idealMap (T ⊗[R] S) I) x) := by
  simp [tensorCotangentTo]

-- TODO: refactor using lift of surjective map is surjective
lemma tensorCotangentTo_surjective :
    Function.Surjective (I.tensorCotangentTo R T) := by
  intro x
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ x
  have := I.map_includeRight_eq (R := R) (A := T)
  rw [Submodule.ext_iff] at this
  simp at this
  have hmem (y : T ⊗[R] I) :
      (I.subtype.restrictScalars R).lTensor T y ∈ map (Algebra.TensorProduct.includeRight) I := by
    rw [this]
    use y
    rfl
  have : ∃ (y : T ⊗[R] I), ⟨(I.subtype.restrictScalars R).lTensor T y, hmem y⟩ = x := by
    obtain ⟨y, hy⟩ := (this _).mp x.property
    use y
    ext
    simpa
  have htxm (t : T) (x : I) : t ⊗ₜ[R] ↑x ∈ map (algebraMap S (T ⊗[R] S)) I := hmem (t ⊗ₜ[R] ↑x)
  have heq (t : T) (x : I) :
      (map (algebraMap S (T ⊗[R] S)) I).toCotangent ⟨t ⊗ₜ[R] x, htxm t x⟩ =
        t • (I.map (algebraMap S (T ⊗[R] S))).toCotangent ((Algebra.idealMap (T ⊗[R] S) I) x) := by
    have : t • (map (algebraMap S (T ⊗[R] S)) I).toCotangent ((Algebra.idealMap (T ⊗[R] S) I) x) =
        (map (algebraMap S (T ⊗[R] S)) I).toCotangent (t • (Algebra.idealMap (T ⊗[R] S) I) x) := by
      simp
    rw [this]
    congr
    simp
  obtain ⟨y, rfl⟩ := this
  induction y with
  | zero =>
    use 0
    simp
    symm
    apply map_zero
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    use a + b
    simp only [map_add, ha, hb]
    rfl
  | tmul t x =>
    use t ⊗ₜ I.toCotangent x
    simpa using (heq ..).symm

lemma cotangentToQuotientSquare_injective :
    Function.Injective I.cotangentToQuotientSquare := by
  simp only [cotangentToQuotientSquare]
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
  simp only [toCotangent] at hx
  erw [Submodule.mapQ_apply] at hx
  simp only [Submodule.coe_subtype, Quotient.mk_eq_mk] at hx
  rw [Ideal.toCotangent_eq_zero]
  exact (Submodule.Quotient.mk_eq_zero (I ^ 2)).mp hx

lemma tensorCotangentTo_injective_of_flat [Module.Flat R T] :
    Function.Injective (I.tensorCotangentTo R T) := by
  let f : (I.map <| algebraMap S (T ⊗[R] S)).Cotangent →ₗ[T]
      T ⊗[R] S ⧸ (I.map <| algebraMap S (T ⊗[R] S)) ^ 2 :=
    (Ideal.cotangentToQuotientSquare _).restrictScalars T
  suffices h : Function.Injective (f ∘ₗ tensorCotangentTo R T I) by
    exact Function.Injective.of_comp h
  let g : T ⊗[R] I.Cotangent →ₗ[T] T ⊗[R] (S ⧸ I ^ 2) :=
    AlgebraTensorModule.lTensor T T I.cotangentToQuotientSquare
  have : (I.map <| algebraMap S (T ⊗[R] S)) ^ 2 = (I ^ 2).map (algebraMap S (T ⊗[R] S)) := by
    rw [Ideal.map_pow]
  let u : T ⊗[R] (S ⧸ I ^ 2) ≃ₐ[T] T ⊗[R] S ⧸ map (algebraMap S (T ⊗[R] S)) (I ^ 2) :=
    Algebra.TensorProduct.tensorQuotientEquiv ..
  let hₐ : T ⊗[R] (S ⧸ I ^ 2) ≃ₐ[T] T ⊗[R] S ⧸ (I.map <| algebraMap S (T ⊗[R] S)) ^ 2 :=
    AlgEquiv.trans u (Ideal.quotientEquivAlgOfEq T this.symm)
  have (x : S) : (u (1 ⊗ₜ[R] (Quotient.mk (I ^ 2)) x)) = Quotient.mk _ (1 ⊗ₜ[R] x) := by
    apply Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul
  have : f ∘ₗ tensorCotangentTo R T I = hₐ.toLinearMap ∘ₗ g := by
    ext x
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    simp [f, g, hₐ, this]
    simp [RingHom.algebraMap_toAlgebra]
  simp only [this, LinearMap.coe_comp]
  apply Function.Injective.comp
  · exact hₐ.injective
  · apply Module.Flat.lTensor_preserves_injective_linearMap (M := T)
      (I.cotangentToQuotientSquare.restrictScalars R)
    apply cotangentToQuotientSquare_injective

noncomputable def tensorCotangent [Module.Flat R T] :
    T ⊗[R] I.Cotangent ≃ₗ[T] (I.map <| algebraMap S (T ⊗[R] S)).Cotangent :=
  LinearEquiv.ofBijective (I.tensorCotangentTo R T)
    ⟨I.tensorCotangentTo_injective_of_flat R T, I.tensorCotangentTo_surjective R T⟩

def Cotangent.equivOfEq (I J : Ideal S) (hIJ : I = J) :
    I.Cotangent ≃ₗ[S] J.Cotangent where
  __ := Cotangent.lift (J.toCotangent ∘ₗ LinearEquiv.ofEq I J hIJ) <| fun x y ↦ by
    simp [toCotangent_eq_zero, ← hIJ, sq, mul_mem_mul]
  invFun := Cotangent.lift (I.toCotangent ∘ₗ LinearEquiv.ofEq J I hIJ.symm) <| fun x y ↦ by
    simp [toCotangent_eq_zero, hIJ, sq, mul_mem_mul]
  left_inv x := by
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, lift_toCotangent, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply]
    rfl
  right_inv x := by
    obtain ⟨x, rfl⟩ := J.toCotangent_surjective x
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, lift_toCotangent, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply]
    rfl

lemma Cotangent.equivOfEq_toCotangent (I J : Ideal S) (hIJ : I = J) (x : I) :
    Cotangent.equivOfEq I J hIJ (I.toCotangent x) = J.toCotangent (LinearEquiv.ofEq I J hIJ x) := by
  simp [Cotangent.equivOfEq]
  sorry

end Ideal

namespace Algebra

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (P : Extension.{u, u, u} R S)
variable (T : Type u) [CommRing T] [Algebra R T]

namespace Extension

attribute [local instance] SMulCommClass.of_commMonoid
attribute [local instance] KaehlerDifferential.moduleBaseChange'

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- `Cotangent.val` as a linear isomorphism. -/
def valEquiv : P.Cotangent ≃ₗ[P.Ring] P.ker.Cotangent where
  toFun := Cotangent.val
  invFun := Cotangent.of
  map_add' x y := by simp
  map_smul' x y := by simp
  left_inv x := rfl
  right_inv x := rfl

noncomputable def tensorCotangent' [Module.Flat R T] :
    T ⊗[R] P.Cotangent ≃ₗ[T] (P.baseChange (T := T)).Cotangent :=
  let e₀ : T ⊗[R] P.Cotangent ≃ₗ[T] T ⊗[R] P.ker.Cotangent :=
    AlgebraTensorModule.congr (LinearEquiv.refl T T) (P.valEquiv.restrictScalars R)
  let e₁ := P.ker.tensorCotangent R T
  have : (Ideal.map (algebraMap P.Ring (T ⊗[R] P.Ring)) P.ker) = (P.baseChange (T := T)).ker := by
    simp [Extension.ker, RingHom.algebraMap_toAlgebra]
    symm
    exact Algebra.TensorProduct.lTensor_ker _ P.algebraMap_surjective
  let e₂ : (Ideal.map (algebraMap P.Ring (T ⊗[R] P.Ring)) P.ker).Cotangent ≃ₗ[T]
      (P.baseChange (T := T)).ker.Cotangent :=
    (Ideal.Cotangent.equivOfEq _ _ this).restrictScalars T
  let e₃ : (P.baseChange (T := T)).ker.Cotangent ≃ₗ[T] (P.baseChange (T := T)).Cotangent :=
    (P.baseChange (T := T)).valEquiv.symm.restrictScalars T
  e₀ ≪≫ₗ e₁ ≪≫ₗ e₂ ≪≫ₗ e₃

@[simp]
lemma tensorCotangent'_tmul [Module.Flat R T] (t : T) (x : P.Cotangent) :
    P.tensorCotangent' T (t ⊗ₜ x) = t • Cotangent.map (P.toBaseChange T) x :=
  sorry

#exit

noncomputable
def tensorToH1Cotangent :
    T ⊗[R] P.H1Cotangent →ₗ[T] (P.baseChange (T := T)).H1Cotangent :=
  let _ : Algebra S (T ⊗[R] S) := TensorProduct.includeRight.toRingHom.toAlgebra
  LinearMap.liftBaseChange T <|
    (Extension.H1Cotangent.map (P.toBaseChange T)).restrictScalars R

@[simp]
lemma tensorToH1Cotangent_tmul (t : T) (x : P.H1Cotangent) :
    (P.tensorToH1Cotangent T (t ⊗ₜ x)).val = t • Cotangent.map (P.toBaseChange T) x.val :=
  rfl

set_option maxHeartbeats 0 in
lemma tensorToH1Cotangent_bijective_of_flat [Module.Flat R T] :
    Function.Bijective (P.tensorToH1Cotangent T) := by
  apply LinearMap.bijective_of (M₁ := Unit) (N₁ := Unit) (M₂ := Unit) (N₂ := Unit)
      (M₄ := T ⊗[R] P.Cotangent) (N₄ := (P.baseChange (T := T)).Cotangent)
      (M₅ := T ⊗[R] P.CotangentSpace) (N₅ := (P.baseChange (T := T)).CotangentSpace)
    0
    0
    (((h1Cotangentι (P := P)).restrictScalars R).lTensor T)
    ((P.cotangentComplex.restrictScalars R).lTensor T)
    0
    0
    (h1Cotangentι.restrictScalars R)
    ((P.baseChange (T := T)).cotangentComplex.restrictScalars R)
    0
    0
    ((P.tensorToH1Cotangent T).restrictScalars R)
    ((P.tensorCotangent' T).restrictScalars R)
    ((P.tensorCotangentSpace' T).restrictScalars R)
  · simp
  · simp
  · ext t x
    simp
  · ext t x
    simp [CotangentSpace.map_cotangentComplex]
  · tauto
  · simp
    apply Module.Flat.lTensor_preserves_injective_linearMap
    simp only [LinearMap.coe_restrictScalars]
    exact h1Cotangentι_injective
  · apply Module.Flat.lTensor_exact
    simp only [LinearMap.coe_restrictScalars]
    exact P.exact_hCotangentι_cotangentComplex
  · tauto
  · rw [LinearMap.exact_zero_iff_injective]
    simp only [LinearMap.coe_restrictScalars]
    exact h1Cotangentι_injective
  · simp only [LinearMap.coe_restrictScalars]
    apply exact_hCotangentι_cotangentComplex
  · tauto
  · simp
  · exact (P.tensorCotangent' T).bijective
  · exact (P.tensorCotangentSpace' T).injective

end Extension

end

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- Flat base change commutes with `H1Cotangent`. -/
def tensorH1CotangentOfFlat (T : Type*) [CommRing T] [Algebra R T] [Module.Flat R T] :
    T ⊗[R] H1Cotangent R S ≃ₗ[T] H1Cotangent T (T ⊗[R] S) :=
  let _ : Algebra S (T ⊗[R] S) := TensorProduct.includeRight.toRingHom.toAlgebra
  let f := H1Cotangent.map R T S (T ⊗[R] S)
  let f' := (f.restrictScalars R).liftBaseChange T
  sorry

end Algebra
