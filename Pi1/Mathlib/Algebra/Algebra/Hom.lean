import Mathlib.Algebra.Algebra.Hom

instance {R S T : Type*} [CommSemiring R] [Semiring S] [Semiring T] [Algebra R S] [Algebra R T]
    [Subsingleton T] :
    Unique (S →ₐ[R] T) where
  default := AlgHom.ofLinearMap default (Subsingleton.elim _ _) (fun _ _ ↦ (Subsingleton.elim _ _))
  uniq _ := DFunLike.ext _ _ <| fun _ ↦ Subsingleton.elim _ _

@[simp]
lemma AlgHom.default_apply {R S T : Type*} [CommSemiring R] [Semiring S] [Semiring T] [Algebra R S]
    [Algebra R T] [Subsingleton T] (x : S) :
    (default : S →ₐ[R] T) x = 0 :=
  rfl
