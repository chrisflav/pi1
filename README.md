# The étale fundamental group of a scheme

In this repository we formalise the étale fundamental group of a connected scheme in Lean 4,
building on top of Lean's math library [mathlib4](https://github.com/leanprover-community/mathlib4).

The étale fundamental group `π₁ᵉᵗ(ξ)` of a connected scheme `X` at a geometric point `ξ` is defined
as the automorphism group of the fiber functor associated to `ξ`

We verify that if `X` is a connected scheme, the category of schemes finite étale over `X`
is a Galois category and taking geometric fibers over a geometric point is a fiber functor.

The main result is `AlgebraicGeometry.FiniteEtale.galoisCategory` in
[`Pi1.FundamentalGroup.Galois`](Pi1/FundamentalGroup/Galois.lean).

In particular, by the general framework of Galois categories, `π₁ᵉᵗ(ξ)` is a pro-finite group and
the fiber functor associated to `ξ` induces an equivalence of category with the category
of finite `π₁ᵉᵗ(ξ)`-sets.

## Integration into mathlib

Everything in this repository will eventually be integrated into mathlib.
