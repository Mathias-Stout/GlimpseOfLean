import Mathlib
/- Formalize the following statement: given any permutation of the numbers {1,..,n^2 +1},
  one may find a monotone subsequence (i.e. either increasing or decreasing). -/

/- (https://www.sfu.ca/~jtmulhol/math302/puzzles-rc-cubology.html)
  Any state of a rubic's cube can be described by an element of the group
  (S₈ x (ℤ/3)⁸) × (S₁₂ x (ℤ/2)⁸).
  The first factor describes the permutation + orientation of the 8 corner pieces
  The second factor describes the permutation + orientation of the 12 edge pieces.
  Not all of these configurations can actually be obtained.
  It turns out that the subset of all possible configurations is given by those
  (ρ,v,σ,w) for which
  · sign(ρ) = sign(σ)
  · v₁ + ... + v₈ = 0
  · w₁ + ... + w₁₂ = 0

  State this theorem.
  Hint: some extra work is needed to describe what the subgroup of possible cube states is.
    -/
