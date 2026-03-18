import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MvPolynomial.CommRing

/- An affine V variety in kⁿ is a common zero set of polynomials in k[x₁,...,xₙ].
  The corresponding vanishing ideal I(V) is given by the ideal of all polynomials that vanish on V.
  Write k[V] = k[x₁,..,xₙ]/I(V) for the corresponding coordinate ring.
  Now suppose that V ⊆ kᵐ, W ⊆ kⁿ and f = (f₁,..,fₙ) is a tuple of polynomials in k[x₁,..,xₘ]
  such that f(V) ⊆ W.
  Then f naturally determines an algebra morphism k[W] →ₐ k[V].
  Define this map and show that it is an algebra morphism
   -/

variable {n: ℕ} {k : Type} [Field k]

def zeroLocus (s : Set (MvPolynomial (Fin n) k)) : Set (Fin n → k) := sorry

def isZeroLocus (V : Set (Fin n → k)) : Prop := sorry

def vanishingIdeal (V : Set (Fin n → k)) : Ideal (MvPolynomial (Fin n) k) := sorry

def CoordRing (V : Set (Fin n → k)) : Type := (MvPolynomial (Fin n) k) ⧸  (vanishingIdeal V)

#check MvPolynomial.aeval
