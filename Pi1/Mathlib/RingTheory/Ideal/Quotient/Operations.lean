import Mathlib.RingTheory.Ideal.Quotient.Operations

@[simp]
lemma Ideal.quotientInfRingEquivPiQuotient_mk {R ι : Type*} [Finite ι] [CommRing R]
    (I : ι → Ideal R) (hI : Pairwise (Function.onFun IsCoprime I)) (x : R) :
    Ideal.quotientInfRingEquivPiQuotient I hI x = fun _ ↦ Ideal.Quotient.mk _ x := rfl
