import Mathlib.RingTheory.Idempotents

-- #24518

lemma RingHom.prod_bijective_of_isIdempotentElem {R : Type*} [CommRing R]
    {e f : R} (he : IsIdempotentElem e) (hf : IsIdempotentElem f) (hef₁ : e + f = 1)
    (hef₂ : e * f = 0) :
    Function.Bijective ((Ideal.Quotient.mk <| Ideal.span {e}).prod
      (Ideal.Quotient.mk <| Ideal.span {f})) := by
  let o (i : Fin 2) : R := match i with
    | 0 => e
    | 1 => f
  show Function.Bijective
    (piFinTwoEquiv _ ∘ Pi.ringHom (fun i : Fin 2 ↦ Ideal.Quotient.mk (Ideal.span {o i})))
  rw [(Equiv.bijective _).of_comp_iff']
  apply bijective_pi_of_isIdempotentElem
  · intro i
    fin_cases i <;> simpa [o]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      simp [o, mul_comm, sub_mul, mul_sub, hef₂, ← hef₁]
  · simpa

/-- If `e` and `f` are idempotent elements such that `e + f = 1` and `e * f = 0`,
`S` is isomorphic as an `R`-algebra to `S ⧸ (e) × S ⧸ (f)`. -/
noncomputable
def AlgEquiv.prodQuotientOfIsIdempotentElem {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {e f : S} (he : IsIdempotentElem e) (hf : IsIdempotentElem f) (hef₁ : e + f = 1)
    (hef₂ : e * f = 0) :
    S ≃ₐ[R] (S ⧸ Ideal.span {e}) × S ⧸ Ideal.span {f} :=
  AlgEquiv.ofBijective ((Ideal.Quotient.mkₐ _ _).prod (Ideal.Quotient.mkₐ _ _)) <|
    RingHom.prod_bijective_of_isIdempotentElem he hf hef₁ hef₂
