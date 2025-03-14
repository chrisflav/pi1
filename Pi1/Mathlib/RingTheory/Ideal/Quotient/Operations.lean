import Mathlib.RingTheory.Ideal.Quotient.Operations

@[simp]
lemma RingEquiv.quotientBot_mk {R : Type*} [Ring R] (r : R) :
    RingEquiv.quotientBot R (Ideal.Quotient.mk ⊥ r) = r :=
  rfl

@[simp]
lemma RingEquiv.quotientBot_symm_mk {R : Type*} [Ring R] (r : R) :
    (RingEquiv.quotientBot R).symm r = r :=
  rfl

/-- `RingEquiv.quotientBot` as an algebra isomorphism. -/
def AlgEquiv.quotientBot (R S : Type*) [CommSemiring R] [CommRing S] [Algebra R S] :
    (S ⧸ (⊥ : Ideal S)) ≃ₐ[R] S where
  __ := RingEquiv.quotientBot S
  commutes' x := by
    rw [← Ideal.Quotient.mk_algebraMap]
    simp [-Ideal.Quotient.mk_algebraMap]

@[simp]
lemma AlgEquiv.quotientBot_mk (R S : Type*) [CommSemiring R] [CommRing S] [Algebra R S] (s : S) :
    AlgEquiv.quotientBot R S (Ideal.Quotient.mk ⊥ s) = s :=
  rfl

@[simp]
lemma AlgEquiv.quotientBot_symm_mk (R S : Type*) [CommSemiring R] [CommRing S] [Algebra R S]
    (s : S) : (AlgEquiv.quotientBot R S).symm s = s :=
  rfl
