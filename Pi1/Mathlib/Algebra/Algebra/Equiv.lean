import Mathlib.Algebra.Algebra.Equiv

instance {R S T : Type*} [CommSemiring R] [Semiring S] [Semiring T] [Algebra R S] [Algebra R T]
    [Subsingleton S] [Subsingleton T] :
    Inhabited (S ≃ₐ[R] T) where
  default := AlgEquiv.ofAlgHom default default
    (AlgHom.ext fun _ ↦ Subsingleton.elim _ _)
    (AlgHom.ext fun _ ↦ Subsingleton.elim _ _)
