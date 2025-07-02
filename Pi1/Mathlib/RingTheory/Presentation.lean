import Mathlib.RingTheory.Presentation

noncomputable section

universe t₁ t₂

open TensorProduct MvPolynomial

variable {R : Type*} [CommRing R]

namespace Algebra

lemma aeval_mk_X_eq_mk {σ : Type*} (I : Ideal (MvPolynomial σ R)) :
    aeval (fun i ↦ Ideal.Quotient.mk I (X i)) = Ideal.Quotient.mkₐ _ I := by
  rw [aeval_unique (Ideal.Quotient.mkₐ _ I)]
  rfl

def Generators.naive {σ : Type t₁} {ι : Type t₂} (v : ι → MvPolynomial σ R)
    (s : MvPolynomial σ R ⧸ (Ideal.span <| Set.range v) → MvPolynomial σ R :=
      Function.surjInv Ideal.Quotient.mk_surjective)
    (hs : ∀ x, Ideal.Quotient.mk _ (s x) = x := by apply Function.surjInv_eq) :
    Generators.{t₁} R (MvPolynomial σ R ⧸ (Ideal.span <| Set.range v)) where
  vars := σ
  val i := Ideal.Quotient.mk _ (X i)
  σ' := s
  aeval_val_σ' x := by
    rw [aeval_mk_X_eq_mk]
    apply hs
  algebra := inferInstance
  algebraMap_eq := by
    ext x
    · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, algHom_C]
      rfl
    · simp

lemma Generators.naive_val {σ ι : Type*} (v : ι → MvPolynomial σ R)
    (s : MvPolynomial σ R ⧸ (Ideal.span <| Set.range v) → MvPolynomial σ R)
    (hs : ∀ x, Ideal.Quotient.mk _ (s x) = x) (i : σ) :
    (Generators.naive v s hs).val i = Ideal.Quotient.mk _ (X i) :=
  rfl

lemma Generators.naive_ker {σ ι : Type*} (v : ι → MvPolynomial σ R)
    (s : MvPolynomial σ R ⧸ (Ideal.span <| Set.range v) → MvPolynomial σ R)
    (hs : ∀ x, Ideal.Quotient.mk _ (s x) = x) :
    (Generators.naive v s hs).ker = Ideal.span (Set.range v) :=
  (Ideal.span (Set.range v)).mk_ker

lemma Generators.naive_σ {σ ι : Type*} (v : ι → MvPolynomial σ R)
    (s : MvPolynomial σ R ⧸ (Ideal.span <| Set.range v) → MvPolynomial σ R)
    (hs : ∀ x, Ideal.Quotient.mk _ (s x) = x)
    (x : MvPolynomial σ R ⧸ (Ideal.span <| Set.range v)) :
    (Generators.naive v s hs).σ x = s x :=
  rfl

def Presentation.naive {σ : Type t₁} {ι : Type t₂} (v : ι → MvPolynomial σ R)
    (s : MvPolynomial σ R ⧸ (Ideal.span <| Set.range v) → MvPolynomial σ R :=
      Function.surjInv Ideal.Quotient.mk_surjective)
    (hs : ∀ x, Ideal.Quotient.mk _ (s x) = x := by apply Function.surjInv_eq) :
    Presentation.{t₂, t₁} R (MvPolynomial σ R ⧸ (Ideal.span <| Set.range v)) where
  __ := Generators.naive v s hs
  rels := ι
  relation := v
  span_range_relation_eq_ker := (Generators.naive_ker v s hs).symm

end Algebra
