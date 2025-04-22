import Pi1.RingTheory.FiniteEtale.Equalizer
-- TODO: disentangle imports
import Mathlib.RingTheory.Flat.Equalizer

universe u

open TensorProduct

variable {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R S] [Algebra R B]

namespace Algebra

local notation f " ≟ₐ " g => AlgHom.equalizer f g
--local notation "eq(" f " , " g ")" => AlgHom.equalizer f g

local notation S " ⊗ₘ " f => Algebra.TensorProduct.map (AlgHom.id S S) f

noncomputable
def TensorProduct.assoc' (R S A B C : Type*) [CommSemiring R] [Semiring A] [Semiring B]
    [Semiring C] [Algebra R A] [CommSemiring S] [Algebra R S] [Algebra S A]
    [IsScalarTower R S A] [Algebra R B] [Algebra R C] :
    (A ⊗[R] B) ⊗[R] C ≃ₐ[S] A ⊗[R] B ⊗[R] C where
  __ := Algebra.TensorProduct.assoc R A B C
  commutes' r := by simp [one_def]

@[simp]
lemma TensorProduct.assoc'_tmul (R S A B C : Type*) [CommSemiring R] [Semiring A] [Semiring B]
    [Semiring C] [Algebra R A] [CommSemiring S] [Algebra R S] [Algebra S A]
    [IsScalarTower R S A] [Algebra R B] [Algebra R C]
    (a : A) (b : B) (c : C) :
    TensorProduct.assoc' R S A B C (a ⊗ₜ b ⊗ₜ c) = a ⊗ₜ (b ⊗ₜ c) :=
  rfl

@[simp]
lemma TensorProduct.assoc'_symm_tmul (R S A B C : Type*) [CommSemiring R] [Semiring A] [Semiring B]
    [Semiring C] [Algebra R A] [CommSemiring S] [Algebra R S] [Algebra S A]
    [IsScalarTower R S A] [Algebra R B] [Algebra R C]
    (a : A) (b : B) (c : C) :
    (TensorProduct.assoc' R S A B C).symm (a ⊗ₜ (b ⊗ₜ c)) = a ⊗ₜ b ⊗ₜ c :=
  rfl

variable (R) in
def _root_.AlgHom.equalizerRestrictScalars [Algebra S A] [Algebra S B]
    [IsScalarTower R S A] [IsScalarTower R S B]
    (f g : A →ₐ[S] B) :
    AlgHom.equalizer (f.restrictScalars R) (g.restrictScalars R) ≃ₐ[R]
      AlgHom.equalizer f g :=
  AlgEquiv.refl

@[simp]
lemma _root_.AlgHom.equalizerRestrictScalars_symm_apply [Algebra S A] [Algebra S B]
    [IsScalarTower R S A] [IsScalarTower R S B]
    (f g : A →ₐ[S] B) (x) :
    (AlgHom.equalizerRestrictScalars R f g).symm x = x :=
  rfl

variable (S) in
set_option maxHeartbeats 0 in
noncomputable
def _root_.AlgHom.equalizerCancelBaseChange (f g : A →ₐ[R] B) (T : Type u) [CommRing T]
    [Algebra R T] :
    (((T ⊗[R] S) ⊗ₘ (T ⊗ₘ f)) ≟ₐ ((T ⊗[R] S) ⊗ₘ (T ⊗ₘ g))) ≃ₐ[T]
      (((T ⊗[R] S) ⊗ₘ f) ≟ₐ ((T ⊗[R] S) ⊗ₘ g)) :=
  AlgHom.equalizerCongr
    (TensorProduct.cancelBaseChange R T (T ⊗[R] S) (T ⊗[R] S) A)
    (TensorProduct.cancelBaseChange R T (T ⊗[R] S) (T ⊗[R] S) B)
    (by ext; simp) (by ext; simp) |>.restrictScalars T

@[simp]
lemma _root_.AlgHom.equalizerCancelBaseChange_algebraMap (f g : A →ₐ[R] B) (T : Type u) [CommRing T]
    [Algebra R T] (x : T ⊗[R] S) :
    AlgHom.equalizerCancelBaseChange S f g T (algebraMap _ _ x) = algebraMap _ _ x := by
  simp [AlgHom.equalizerCancelBaseChange]

lemma _root_.AlgHom.equalizerCongr_symm_apply {R A A' B B' : Type*} [CommSemiring R]
    [Semiring A] [Semiring A'] [Semiring B] [Semiring B']
    [Algebra R A] [Algebra R A'] [Algebra R B] [Algebra R B']
    (eA : A ≃ₐ[R] A') (eB : B ≃ₐ[R] B')
    {f g : A →ₐ[R] B} {f' g' : A' →ₐ[R] B'}
    (hf : eB.toAlgHom.comp f = f'.comp eA) (hg : eB.toAlgHom.comp g = g'.comp eA)
    (x : AlgHom.equalizer f' g') :
    (AlgHom.equalizerCongr eA eB hf hg).symm x =
      ⟨eA.symm x, ((AlgHom.equalizerCongr eA eB hf hg).symm x).2⟩ :=
  rfl

lemma _root_.AlgHom.equalizerCongr_apply {R A A' B B' : Type*} [CommSemiring R]
    [Semiring A] [Semiring A'] [Semiring B] [Semiring B']
    [Algebra R A] [Algebra R A'] [Algebra R B] [Algebra R B']
    (eA : A ≃ₐ[R] A') (eB : B ≃ₐ[R] B')
    {f g : A →ₐ[R] B} {f' g' : A' →ₐ[R] B'}
    (hf : eB.toAlgHom.comp f = f'.comp eA) (hg : eB.toAlgHom.comp g = g'.comp eA)
    (x : AlgHom.equalizer f g) :
    AlgHom.equalizerCongr eA eB hf hg x =
      ⟨eA x, (AlgHom.equalizerCongr eA eB hf hg x).2⟩ :=
  rfl

@[simp]
lemma _root_.AlgHom.equalizerCancelBaseChange_tmul (f g : A →ₐ[R] B) (T : Type u) [CommRing T]
    [Algebra R T] (x : A) (hx : x ∈ AlgHom.equalizer f g) :
    ((AlgHom.equalizerCancelBaseChange S f g T)
      ⟨1 ⊗ₜ[T] 1 ⊗ₜ[R] x, by simp [show f x = g x from hx]⟩) =
        ⟨1 ⊗ₜ x, by simp [show f x = g x from hx]⟩ := by
  ext : 1
  simp [AlgHom.equalizerCancelBaseChange, AlgHom.equalizerCongr_apply]

lemma _root_.AlgHom.tensorEqualizerEquiv_symm_apply
    {R : Type*} (S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] (T : Type*) [CommRing T]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f g : A →ₐ[R] B) [Module.Flat R T]
    (x : A) (hx : x ∈ AlgHom.equalizer f g) :
    (f.tensorEqualizerEquiv S T g).symm ⟨1 ⊗ₜ x, by simp [show f x = g x from hx]⟩ =
      1 ⊗ₜ ⟨x, hx⟩ := by
  apply (f.tensorEqualizerEquiv S T g).injective
  ext
  simp

set_option maxHeartbeats 0 in
noncomputable
def auxEquivRHS (f g : A →ₐ[R] B) (T : Type u) [CommRing T] [Algebra R T] [Module.Flat R T] :
    T ⊗[R] ((S ⊗ₘ f) ≟ₐ (S ⊗ₘ g)) ≃ₐ[T]
      ((T ⊗[R] S) ⊗ₘ (T ⊗ₘ f)) ≟ₐ ((T ⊗[R] S) ⊗ₘ (T ⊗ₘ g)) :=
  let aux :
      ↥(TensorProduct.map (.id T T) (TensorProduct.map (.id R S) f) ≟ₐ
        TensorProduct.map (.id T T) (TensorProduct.map (.id R S) g)) ≃ₐ[T]
      ↥(TensorProduct.map (.id (T ⊗[R] S) (T ⊗[R] S)) f ≟ₐ
        TensorProduct.map (.id (T ⊗[R] S) (T ⊗[R] S)) g) :=
    .trans
      (AlgHom.equalizerCongr
        (TensorProduct.assoc' R T T S A).symm
        (TensorProduct.assoc' R T T S B).symm
        (by ext <;> simp) (by ext <;> simp))
      (AlgHom.equalizerRestrictScalars T _ _)
  (TensorProduct.map (.id R S) f).tensorEqualizerEquiv T T (TensorProduct.map (.id R S) g) |>.trans
    aux |>.trans
    (f.equalizerCancelBaseChange S g T).symm

lemma auxEquivRHS_symm_tmul (f g : A →ₐ[R] B) (T : Type u) [CommRing T] [Algebra R T]
    [Module.Flat R T] (x : S) :
    (auxEquivRHS (S := S) f g T).symm (algebraMap (T ⊗[R] S) _ (1 ⊗ₜ x)) =
      1 ⊗ₜ algebraMap _ _ x := by
  simpa [auxEquivRHS, AlgHom.equalizerCongr_symm_apply] using
    AlgHom.tensorEqualizerEquiv_symm_apply ..

lemma auxEquivRHS_symm_tmul' (f g : A →ₐ[R] B) (T : Type u) [CommRing T] [Algebra R T]
    [Module.Flat R T] (x : AlgHom.equalizer f g) :
    (auxEquivRHS (S := S) f g T).symm ⟨1 ⊗ₜ (1 ⊗ₜ x), by simp [show f x = g x from x.2]⟩ =
      1 ⊗ₜ ⟨1 ⊗ₜ x, by simp [show f x = g x from x.2]⟩ := by
  simpa [auxEquivRHS, AlgHom.equalizerCongr_symm_apply] using
    AlgHom.tensorEqualizerEquiv_symm_apply ..

noncomputable
def auxEquivLHS (f g : A →ₐ[R] B) (T : Type u) [CommRing T] [Algebra R T] [Module.Flat R T] :
    T ⊗[R] (S ⊗[R] f ≟ₐ g) ≃ₐ[T] (T ⊗[R] S) ⊗[T] ((T ⊗ₘ f) ≟ₐ (T ⊗ₘ g)) :=
  .trans
    (.trans
      (TensorProduct.assoc' R T T S (f ≟ₐ g)).symm
      (TensorProduct.cancelBaseChange R T T (T ⊗[R] S) (f ≟ₐ g)).symm)
    (TensorProduct.congr .refl (f.tensorEqualizerEquiv T T g))

@[simp]
lemma auxEquivLHS_one_tmul_one (f g : A →ₐ[R] B) (T : Type u) [CommRing T] [Algebra R T]
    [Module.Flat R T] (x : S) :
    auxEquivLHS f g T (1 ⊗ₜ[R] x ⊗ₜ[R] 1) = (1 ⊗ₜ x) ⊗ₜ 1 :=
  rfl

lemma auxEquivLHS_one_one_tmul (f g : A →ₐ[R] B) (T : Type u) [CommRing T] [Algebra R T]
    [Module.Flat R T] (x : AlgHom.equalizer f g) :
    (auxEquivLHS (S := S) f g T) (1 ⊗ₜ[R] 1 ⊗ₜ[R] x) =
      1 ⊗ₜ ⟨1 ⊗ₜ x, by simp [show f x.1 = g x.1 from x.2]⟩ :=
  rfl

lemma _root_.AlgHom.tensorEqualizer_tmul_one (f g : A →ₐ[R] B) (x : S) :
    f.tensorEqualizer S S g (x ⊗ₜ 1) = algebraMap S _ x :=
  rfl

lemma _root_.AlgHom.tensorEqualizer_one_tmul {R : Type*} (S : Type*) [CommRing R]
      [CommRing S] [Algebra R S] (T : Type*) [CommRing T]
      [Algebra R T] [Algebra S T] [IsScalarTower R S T]
      {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (f g : A →ₐ[R] B) (x : AlgHom.equalizer f g) :
    f.tensorEqualizer S T g (1 ⊗ₜ x) = ⟨1 ⊗ₜ x, by simp [show f x.1 = g x.1 from x.2]⟩ :=
  rfl

lemma _root_.AlgHom.tensorEqualizer_tmul_one' {R : Type*} (S : Type*) [CommRing R]
      [CommRing S] [Algebra R S] (T : Type*) [CommRing T]
      [Algebra R T] [Algebra S T] [IsScalarTower R S T]
      {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (f g : A →ₐ[R] B) (x : T) :
    f.tensorEqualizer S T g (x ⊗ₜ 1) = ⟨x ⊗ₜ 1, by simp⟩ :=
  rfl

variable (S) in
set_option maxHeartbeats 0 in
lemma TensorProduct.map_tensorEqualizer_bijective_iff_tensorEqualizer_map_bijective
    (f g : A →ₐ[R] B) (T : Type u) [CommRing T] [Algebra R T] [Module.Flat R T] :
    Function.Bijective ⇑(TensorProduct.map (AlgHom.id T T) (AlgHom.tensorEqualizer R S f g)) ↔
    Function.Bijective
            ((TensorProduct.map (.id T T) f).tensorEqualizer T (T ⊗[R] S)
                  (TensorProduct.map (.id T T) g)) := by
  let eLHS : T ⊗[R] (S ⊗[R] f ≟ₐ g) ≃ₐ[T] (T ⊗[R] S) ⊗[T]
      ((T ⊗ₘ f) ≟ₐ (T ⊗ₘ g)) :=
    auxEquivLHS f g T
  let eRHS : T ⊗[R] ((S ⊗ₘ f) ≟ₐ (S ⊗ₘ g)) ≃ₐ[T]
      ((T ⊗[R] S) ⊗ₘ (T ⊗ₘ f)) ≟ₐ ((T ⊗[R] S) ⊗ₘ (T ⊗ₘ g)) :=
    auxEquivRHS f g T
  have : IsScalarTower R T
      (T ⊗[R] ↥(TensorProduct.map (AlgHom.id R S) f ≟ₐ TensorProduct.map (AlgHom.id R S) g)) :=
    TensorProduct.isScalarTower_left
  let u := (TensorProduct.map (.id T T) f).tensorEqualizer T (T ⊗[R] S)
    (TensorProduct.map (.id T T) g)
  have heq : TensorProduct.map (AlgHom.id T T) (AlgHom.tensorEqualizer R S f g) =
      eRHS.symm.toAlgHom.comp
        (((TensorProduct.map (.id T T) f).tensorEqualizer T (T ⊗[R] S)
            (TensorProduct.map (.id T T) g)).comp
          eLHS.toAlgHom) := by
    ext x
    · simp only [TensorProduct.map_restrictScalars_comp_includeRight, AlgHom.coe_comp,
        Function.comp_apply, TensorProduct.includeLeft_apply, TensorProduct.includeRight_apply,
        AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_restrictScalars']
      erw [AlgHom.comp_apply]
      erw [AlgHom.comp_apply]
      simp only [AlgHom.coe_coe, auxEquivLHS_one_tmul_one, eLHS]
      show 1 ⊗ₜ[R] (AlgHom.tensorEqualizer S S f g) (x ⊗ₜ 1) = eRHS.symm
        ((AlgHom.tensorEqualizer (T ⊗[R] S) (T ⊗[R] S)
          (TensorProduct.map (AlgHom.id T T) f) (TensorProduct.map (AlgHom.id T T) g))
          ((1 ⊗ₜ[R] x) ⊗ₜ[T] 1))
      rw [AlgHom.tensorEqualizer_tmul_one, AlgHom.tensorEqualizer_tmul_one,
        auxEquivRHS_symm_tmul]
    · simp only [TensorProduct.map_restrictScalars_comp_includeRight, AlgHom.coe_comp,
        AlgHom.coe_restrictScalars', Function.comp_apply, TensorProduct.includeRight_apply,
        AlgEquiv.toAlgHom_eq_coe, eLHS]
      erw [AlgHom.comp_apply]
      erw [AlgHom.comp_apply]
      simp only [AlgHom.coe_coe, eLHS]
      rw [auxEquivLHS_one_one_tmul]
      rw [AlgHom.tensorEqualizer_one_tmul, AlgHom.tensorEqualizer_one_tmul,
        auxEquivRHS_symm_tmul']
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · rw [heq] at H
    rw [← Function.Bijective.of_comp_iff _ eLHS.bijective]
    rw [← Function.Bijective.of_comp_iff' eRHS.symm.bijective]
    exact H
  · rw [heq]
    dsimp
    apply eRHS.symm.bijective.comp
    exact H.comp eLHS.bijective

end Algebra
