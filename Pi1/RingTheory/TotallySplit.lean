import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Pi1.RingTheory.FinitePresentation
import Pi1.RingTheory.RankAtStalk
import Pi1.RingTheory.SmoothFlat
import Pi1.Mathlib.RingTheory.TensorProduct.Basic

open TensorProduct

universe u v

section

instance {R S T : Type*} [CommSemiring R] [Semiring S] [Semiring T] [Algebra R S] [Algebra R T]
    [Subsingleton T] :
    Inhabited (S →ₐ[R] T) where
  default := AlgHom.ofLinearMap default (Subsingleton.elim _ _) (fun _ _ ↦ (Subsingleton.elim _ _))

@[simp]
lemma AlgHom.default_apply {R S T : Type*} [CommSemiring R] [Semiring S] [Semiring T] [Algebra R S]
    [Algebra R T] [Subsingleton T] (x : S) :
    (default : S →ₐ[R] T) x = 0 :=
  rfl

instance {R S T : Type*} [CommSemiring R] [Semiring S] [Semiring T] [Algebra R S] [Algebra R T]
    [Subsingleton S] [Subsingleton T] :
    Inhabited (S ≃ₐ[R] T) where
  default := AlgEquiv.ofAlgHom default default
    (AlgHom.ext fun _ ↦ Subsingleton.elim _ _)
    (AlgHom.ext fun _ ↦ Subsingleton.elim _ _)

@[simp]
lemma AlgEquiv.default_apply {R S T : Type*} [CommSemiring R] [Semiring S] [Semiring T]
    [Algebra R S] [Algebra R T] [Subsingleton S] [Subsingleton T] (x : S) :
    (default : S ≃ₐ[R] T) x = 0 :=
  rfl

instance (R : Type u) [CommRing R] : Algebra.Etale R R :=
    Algebra.instEtaleOfIsStandardSmoothOfRelativeDimensionOfNatNat.{u, 0, 0}

instance (R : Type u) [CommRing R] (n : Type) [Finite n] :
    Algebra.Etale R (n → R) where
  formallyEtale :=
    have : Algebra.Etale R R :=
      Algebra.instEtaleOfIsStandardSmoothOfRelativeDimensionOfNatNat.{u, 0, 0}
    have : Algebra.FormallyEtale R R := Algebra.Etale.formallyEtale
    Algebra.FormallyEtale.instForallOfFinite (fun _ : n ↦ R)

instance (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S] :
    Algebra.Smooth R S where

instance (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S] :
    Algebra.Unramified R S where

instance (R S : Type u) [CommRing R] [CommRing S] :
    letI : Algebra (R × S) S := (RingHom.snd R S).toAlgebra
    Algebra.Etale (R × S) S := by
  algebraize [RingHom.snd R S]
  exact Algebra.Etale.of_isLocalization_Away (0, 1)

instance (R S : Type u) [CommRing R] [CommRing S] :
    letI : Algebra (R × S) R := (RingHom.fst R S).toAlgebra
    Algebra.Etale (R × S) R := by
  algebraize [RingHom.fst R S]
  exact Algebra.Etale.of_isLocalization_Away (1, 0)

lemma RingHom.prod_bijective_of_isIdempotentElem {R : Type*} [CommRing R]
    {e f : R} (he : IsIdempotentElem e) (hf : IsIdempotentElem f) (hef₁ : (1 - e) * (1 - f) = 0)
    (hef₂ : e * f = 0) :
    Function.Bijective ((Ideal.Quotient.mk <| Ideal.span {e}).prod
      (Ideal.Quotient.mk <| Ideal.span {f})) := by
  let o (i : Fin 2) : R := match i with
    | 0 => e
    | 1 => f
  show Function.Bijective
    (piFinTwoEquiv _ ∘ Pi.ringHom (fun i : Fin 2 ↦ Ideal.Quotient.mk (Ideal.span {o i})))
  rw [(Equiv.bijective _).of_comp_iff']
  simp only [o]
  apply bijective_pi_of_isIdempotentElem
  · intro i
    fin_cases i <;> simpa [o]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> simpa [mul_comm]
  · simpa

noncomputable
nonrec def Algebra.TensorProduct.prodRight (R S T A B : Type*) [CommRing R] [CommRing A]
    [CommRing B] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [Algebra R A] [Algebra R B] :
    T ⊗[R] (A × B) ≃ₐ[S] T ⊗[R] A × T ⊗[R] B :=
  AlgEquiv.ofLinearEquiv (TensorProduct.prodRight R S T A B)
    (by simp [Algebra.TensorProduct.one_def])
    (map_mul_of_map_mul_tmul (fun _ _ _ _ ↦ by simp))

def AlgEquiv.prodCongr {R S T A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra R A] [Algebra R B]
    (l : S ≃ₐ[R] A) (r : T ≃ₐ[R] B) :
    (S × T) ≃ₐ[R] A × B :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.prodCongr l r) <| by simp

def AlgEquiv.funUnique (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (ι : Type*) [Unique ι] :
    (ι → S) ≃ₐ[R] S :=
  AlgEquiv.ofAlgHom (Pi.evalAlgHom R (fun _ ↦ S) default) (Pi.constAlgHom R ι S)
    (by ext; simp) (by ext f i; simp [Unique.default_eq i])

def Algebra.prodPiEquiv (R A α β : Type*) [CommRing R] [CommRing A] [Algebra R A] :
    (α ⊕ β → A) ≃ₐ[R] (α → A) × (β → A) :=
  AlgEquiv.ofLinearEquiv (LinearEquiv.sumArrowLequivProdArrow α β R A) rfl <| fun x y ↦ by
    ext <;> simp

def AlgEquiv.piCongrLeft' {ι ι' : Type*} (R : Type*) (S : ι → Type*) (e : ι ≃ ι')
    [CommSemiring R] [∀ i, Semiring (S i)] [∀ i, Algebra R (S i)] :
    (Π i, S i) ≃ₐ[R] Π i, S (e.symm i) :=
  AlgEquiv.ofLinearEquiv (LinearEquiv.piCongrLeft' R S e)
    (by ext; simp) (by intro x y; ext; simp)

def AlgEquiv.piCongrLeft {ι ι' : Type*} (R : Type*) (S : ι → Type*) (e : ι' ≃ ι)
    [CommSemiring R] [∀ i, Semiring (S i)] [∀ i, Algebra R (S i)] :
    (Π i, S (e i)) ≃ₐ[R] Π i, S i :=
  (AlgEquiv.piCongrLeft' R S e.symm).symm

noncomputable
def AlgEquiv.prodQuotientOfIsIdempotentElem {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {e f : S} (he : IsIdempotentElem e) (hf : IsIdempotentElem f) (hef₁ : (1 - e) * (1 - f) = 0)
    (hef₂ : e * f = 0) :
    S ≃ₐ[R] (S ⧸ Ideal.span {e}) × (S ⧸ Ideal.span {f}) :=
  AlgEquiv.ofBijective ((Ideal.Quotient.mkₐ _ _).prod (Ideal.Quotient.mkₐ _ _)) <|
    RingHom.prod_bijective_of_isIdempotentElem he hf hef₁ hef₂

lemma exists_split_of_formallyUnramified (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra S T), Nonempty (S ⊗[R] S ≃ₐ[S] S × T) := by
  have : Subsingleton (Ω[S⁄R]) := inferInstance
  apply (Ideal.cotangent_subsingleton_iff _).mp at this
  apply (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg R S)).mp at this
  obtain ⟨e, he, hsp⟩ := this
  let eq := AlgEquiv.prodQuotientOfIsIdempotentElem (R := S) he he.one_sub
    (by simp [he]) (by simp [he])
  let eq2 : (S ⊗[R] S ⧸ Ideal.span {e}) ≃ₐ[S] S :=
    ((Ideal.span {e}).quotientEquivAlgOfEq S hsp.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective <|
      fun x ↦ by use x ⊗ₜ 1; simp [Algebra.TensorProduct.lmul''])
  refine ⟨(S ⊗[R] S) ⧸ Ideal.span {1 - e}, inferInstance, inferInstance, ⟨?_⟩⟩
  exact eq.trans (AlgEquiv.prodCongr eq2 AlgEquiv.refl)

end

open IsLocalRing

lemma Algebra.Etale.faithfullyFlat_of_rankAtStalk_pos (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.Etale R S] [Module.Finite R S]
    (h : ∀ p, 0 < Module.rankAtStalk (R := R) S p) :
    Module.FaithfullyFlat R S := by
  apply Module.FaithfullyFlat.of_specComap_surjective
  rwa [← Algebra.rankAtStalk_pos_iff_specComap_surjective]

class Algebra.IsSplitOfRank (n : outParam ℕ) (R S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] : Prop where
  nonempty_algEquiv_fun' : Nonempty (S ≃ₐ[R] Fin n → R)

namespace Algebra.IsSplitOfRank

section

variable {n : ℕ}
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

variable (n R S) in
lemma nonempty_algEquiv_fun [IsSplitOfRank n R S] : Nonempty (S ≃ₐ[R] Fin n → R) :=
  nonempty_algEquiv_fun'

instance {T : Type*} [CommRing T] [Algebra R T] [IsSplitOfRank n R S] :
    IsSplitOfRank n T (T ⊗[R] S) := by
  obtain ⟨e⟩ := Algebra.IsSplitOfRank.nonempty_algEquiv_fun n R S
  refine ⟨⟨?_⟩⟩
  exact (Algebra.TensorProduct.congr AlgEquiv.refl e).trans
    ((Algebra.TensorProduct.piRight R T T (fun _ : Fin n ↦ R)).trans <|
      AlgEquiv.piCongrRight fun i ↦ TensorProduct.rid R T T)

lemma of_equiv {S' : Type*} [CommRing S'] [Algebra R S'] (e : S ≃ₐ[R] S') [IsSplitOfRank n R S] :
    IsSplitOfRank n R S' := by
  obtain ⟨f⟩ := nonempty_algEquiv_fun n R S
  exact ⟨⟨e.symm.trans f⟩⟩

lemma iff_subsingleton_of_isEmpty (hn : n = 0) :
    IsSplitOfRank n R S ↔ Subsingleton S := by
  subst hn
  exact ⟨fun ⟨⟨e⟩⟩ ↦ e.subsingleton, fun hs ↦ ⟨⟨default⟩⟩⟩

lemma of_card_eq {ι : Type*} [Finite ι] (h : Nat.card ι = n) (e : S ≃ₐ[R] ι → R) :
    IsSplitOfRank n R S := by
  cases nonempty_fintype ι
  let f : (ι → R) ≃ₐ[R] (Fin n → R) := AlgEquiv.piCongrLeft' _ _
    (Fintype.equivOfCardEq (by simpa using h))
  refine ⟨⟨e.trans f⟩⟩

lemma of_subsingleton [Subsingleton R] : IsSplitOfRank n R S := by
  have : Subsingleton S := RingHom.codomain_trivial (algebraMap R S)
  exact ⟨⟨default⟩⟩

instance [Algebra.IsSplitOfRank n R S] : Module.Free R S := by
  obtain ⟨e⟩ := nonempty_algEquiv_fun n R S
  exact Module.Free.of_equiv e.symm.toLinearEquiv

lemma finrank_eq [Nontrivial R] [Algebra.IsSplitOfRank n R S] : Module.finrank R S = n := by
  obtain ⟨e⟩ := nonempty_algEquiv_fun n R S
  simp [e.toLinearEquiv.finrank_eq]

lemma rankAtStalk_eq [Nontrivial R] [Algebra.IsSplitOfRank n R S] :
    Module.rankAtStalk (R := R) S = n := by
  rw [Module.rankAtStalk_eq_finrank_of_free, finrank_eq]

instance [Algebra.IsSplitOfRank n R S] : Module.FinitePresentation R S := by
  obtain ⟨e⟩ := nonempty_algEquiv_fun n R S
  apply Module.FinitePresentation.of_equiv e.symm.toLinearEquiv

end

section

variable {n : ℕ} {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

instance [IsSplitOfRank n R S] : Etale R S := by
  obtain ⟨e⟩ := Algebra.IsSplitOfRank.nonempty_algEquiv_fun n R S
  exact Algebra.Etale.of_equiv e.symm

lemma exists_isSplitOfRank_tensorProduct [Etale R S] [Module.Finite R S] {n : ℕ}
    (hn : Module.rankAtStalk (R := R) S = n) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Module.FaithfullyFlat R T),
      IsSplitOfRank n T (T ⊗[R] S) := by
  induction n generalizing R S with
  | zero =>
      use R, inferInstance, inferInstance, inferInstance
      let e : R ⊗[R] S ≃ₐ[R] S := TensorProduct.lid R S
      have : IsSplitOfRank 0 R S := by
        rw [iff_subsingleton_of_isEmpty]
        simp only [Nat.cast_zero] at hn
        rwa [Module.rankAtStalk_eq_zero_iff_subsingleton] at hn
        rfl
      apply IsSplitOfRank.of_equiv e.symm
  | succ n ih =>
      cases subsingleton_or_nontrivial R
      · use R, inferInstance, inferInstance, inferInstance
        have : IsSplitOfRank (n + 1) R S := .of_subsingleton
        apply IsSplitOfRank.of_equiv (TensorProduct.lid R S).symm
      have : Nontrivial S := by
        apply Module.nontrivial_of_rankAtStalk_pos (R := R) (p := Nonempty.some inferInstance)
        simp [hn]
      obtain ⟨U, _, _, ⟨e⟩⟩ := exists_split_of_formallyUnramified R S
      algebraize [RingHom.snd S U]
      have : IsScalarTower S (S × U) U := IsScalarTower.of_algebraMap_eq' rfl
      have : Etale S U := by
        have : Etale S (S × U) := Etale.of_equiv e
        apply Etale.comp S (S × U) U
      have : Module.Finite S U := by
        have : Module.Finite S (S × U) := Module.Finite.equiv e.toLinearEquiv
        have : Module.Finite (S × U) U :=
          Module.Finite.of_surjective (Algebra.linearMap (S × U) U) (RingHom.snd S U).surjective
        apply Module.Finite.trans (S × U)
      have (p : PrimeSpectrum S) : Module.rankAtStalk (R := S) (S × U) p = n + 1 := by
        rw [Module.rankAtStalk_eq_of_equiv e.symm.toLinearEquiv]
        simp [Module.rankAtStalk_tensorProduct, hn]
      simp_rw [Module.rankAtStalk_prod , Module.rankAtStalk_self, Pi.one_apply] at this
      have : Module.rankAtStalk (R := S) U = n := by
        ext p
        simp only [Pi.natCast_def, Nat.cast_id]
        have := this p
        omega
      obtain ⟨V, _, _, _, hV⟩ := ih this
      obtain ⟨f⟩ := hV.nonempty_algEquiv_fun
      algebraize [(algebraMap S V).comp (algebraMap R S)]
      let e₁ : V ⊗[R] S ≃ₐ[V] V ⊗[S] (S ⊗[R] S) :=
        (Algebra.TensorProduct.cancelBaseChange R S V V S).symm
      let e₂ : V ⊗[S] (S ⊗[R] S) ≃ₐ[V] V ⊗[S] (S × U) :=
        TensorProduct.congr AlgEquiv.refl e
      let e₃ : V ⊗[S] (S × U) ≃ₐ[V] V ⊗[S] S × V ⊗[S] U :=
        TensorProduct.prodRight S V V S U
      let e₄ : (V ⊗[S] S × V ⊗[S] U) ≃ₐ[V] V × (Fin n → V) :=
        AlgEquiv.prodCongr (TensorProduct.rid S V V) f
      let e₅ : (V × (Fin n → V)) ≃ₐ[V] (Unit ⊕ Fin n) → V :=
        AlgEquiv.trans (AlgEquiv.prodCongr (AlgEquiv.funUnique _ _ _).symm AlgEquiv.refl)
          (Algebra.prodPiEquiv V V Unit (Fin n)).symm
      let e := e₁.trans <| e₂.trans <| e₃.trans <| e₄.trans e₅
      refine ⟨V, inferInstance, inferInstance, ?_, ?_⟩
      · have : Module.FaithfullyFlat R S := by
          apply Algebra.Etale.faithfullyFlat_of_rankAtStalk_pos
          intro p
          simp [hn]
        exact Module.FaithfullyFlat.trans R S V
      · exact IsSplitOfRank.of_card_eq (ι := Unit ⊕ Fin n) (by simp [add_comm]) e

end

end Algebra.IsSplitOfRank

class Algebra.IsSplit (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] : Prop where
