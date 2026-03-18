import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Tactic
import Mathlib.Util.Delaborators

/- An n-dimensional vector over some type 𝕜 is essentially a map `Fin n → 𝕜`,
 where `Fin n` is the canonical type on `n` elements, correspoding to the set
 {0,1..,n-1} in set-based mathematics.
 A vector can be constructed using the notation `![x1,…,xₙ]` -/

#check ![1,2]

-- Adding vectors
#eval ![1, 2] + ![3, 4]  -- ![4, 6]

/- Matrices are constructed using similar notation. Note the semicolon -/

-- An object of type `Matrix (Fin 2) (Fin 3)` (2 rows, 3 columns)
#check !![1, 2, 3; 3, 4, 5]

/- The above matrix has its rows and columns indexed by elements of the type `Fin n` (where n = 2).
 More generally, one can talk about the type `Matrix α β` for matrices whose rows and columns are
 indexed by arbitrary types `α`, resp. `β`. It is not required that `α` and `β` are finite.
 This is useful for describing e.g. the ad
 We will mostly stick with objects of type `Matrix (Fin n) (Fin m)`.
 We collect some useful operations below. -/

open Matrix -- Gives access to Matrix-specific notation *ᵥ below

-- Adding matrices
#eval !![1, 2; 3, 4] + !![3, 4; 5, 6]  -- !![4, 6; 8, 10]

-- Multiplying matrices
#eval !![1, 2; 3, 4] * !![3, 4; 5, 6]  -- !![13, 16; 29, 36]

-- matrices acting on vectors on the left
#eval !![1, 2; 3, 4] *ᵥ ![1, 1] -- ![3, 7]

-- Determinant
#simp !![(1 : ℝ), 2; 3, 4].det -- `4 - 2*3`

#norm_num !![(1 : ℝ), 2; 3, 4].det -- `-2`

-- Trace
#norm_num !![(1 : ℝ), 2; 3, 4].trace -- `5`

variable (a b c d : ℝ) in
#simp !![a, b; c, d].det -- `a * d – b * c`

-- Note that we explicitly tell Lean we are taking entries over ℝ
-- The same matrix with entries over ℤ cannot be inverted
#norm_num [Matrix.inv_def] !![(1 : ℝ), 2; 3, 4]⁻¹ -- !![-2, 1; 3 / 2, -(1 / 2)]

example : !![(1 : ℝ), 2; 3, 4]⁻¹ * !![(1 : ℝ), 2; 3, 4] = 1 := by
  have : Invertible !![(1 : ℝ), 2; 3, 4] := by
    apply Matrix.invertibleOfIsUnitDet
    norm_num
  simp

/- The underlying data of a `Matrix (Fin m) (Fin n) R` is a function
  `Fin m → Fin n → R`.
  A matrix can be constructed out of such a function using `Matrix.of`. -/

/- Define the Vandermonde matrix over a vector `v` of length `n`, using `Matrix.of`.
  Recall that the `j`-th column of this matrix is the `j`-th power of the entries of `v`-/
def myVandermonde {n : ℕ} (v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j => (v i) ^ (j : ℕ))

-- Once you complete the definition above, this proof should be `by rfl`
example  {n : ℕ} (v : Fin n → ℝ) : myVandermonde v =  Matrix.vandermonde v := by rfl


/-!
## Gaussian Elimination for 2×2 Matrices

We prove that any 2×2 matrix over a field with nonzero `(1,1)`-entry can be reduced
to diagonal form by left- and right-multiplication by *transvections*.

A `transvection i j c` is the matrix `1 + single i j c`:
- Left-multiplying by it adds `c` times row `j` to row `i`.
- Right-multiplying by it adds `c` times column `i` to column `j`.

**The algorithm** (for `M` with `M 1 1 ≠ 0`):
1. Left-multiply by `transvection 0 1 (-M 0 1 / M 1 1)` to zero out the `(0,1)`-entry.
   This adds `(-M 0 1 / M 1 1)` times row 1 to row 0, and does not touch row 1.
2. Right-multiply by `transvection 1 0 (-M 1 0 / M 1 1)` to zero out the `(1,0)`-entry.
   This adds `(-M 1 0 / M 1 1)` times column 1 to column 0, and does not touch column 1.
   Since step 1 did not change row 1, the coefficient `-M 1 0 / M 1 1` is still correct.
   Since step 2 does not touch column 1, the zero at `(0,1)` from step 1 is preserved.
-/
section GaussianElimination

variable {𝕜 : Type*} [Field 𝕜]

/-
### Warm-ups: the transvection API

The key simp lemmas for working with transvections are listed below.
They are sufficient to solve the exercises below (and can even be found using `apply?`).
-/

-- Left-multiplying by `transvection i j c` adds `c` times row `j` to row `i`:
#check transvection_mul_apply_same
-- The other rows are unchanged:
#check transvection_mul_apply_of_ne
-- Right-multiplying by `transvection i j c` adds `c` times column `i` to column `j`:
#check mul_transvection_apply_same
-- The other columns are unchanged:
#check mul_transvection_apply_of_ne


/-- Left-multiplying by `transvection 0 1 c` adds `c` times row 1 to row 0. -/
example (M : Matrix (Fin 2) (Fin 2) 𝕜) (c : 𝕜) (b : Fin 2) :
    (transvection (0 : Fin 2) 1 c * M) 0 b = M 0 b + c * M 1 b := by
  exact transvection_mul_apply_same 0 1 b c M

/-- Left-multiplying by `transvection 0 1 c` does not change row 1. -/
example (M : Matrix (Fin 2) (Fin 2) 𝕜) (c : 𝕜) (b : Fin 2) :
    (transvection (0 : Fin 2) 1 c * M) 1 b = M 1 b := by
  apply transvection_mul_apply_of_ne
  exact Ne.symm Fin.zero_ne_one

/-- Right-multiplying by `transvection 1 0 c` adds `c` times column 1 to column 0. -/
example (M : Matrix (Fin 2) (Fin 2) 𝕜) (c : 𝕜) (a : Fin 2) :
    (M * transvection (1 : Fin 2) 0 c) a 0 = M a 0 + c * M a 1 := by
  exact mul_transvection_apply_same 1 0 a c M

/-- Right-multiplying by `transvection 1 0 c` does not change column 1. -/
example (M : Matrix (Fin 2) (Fin 2) 𝕜) (c : 𝕜) (a : Fin 2) :
    (M * transvection (1 : Fin 2) 0 c) a 1 = M a 1 := by
  apply mul_transvection_apply_of_ne
  exact Ne.symm Fin.zero_ne_one

/-
### TransvectionStructs
  An object of type `TransvectionStruct` is by definition the collection of data corresponding
  to a transvection. It can be turned into a matrix using the `toMatrix` function
-/

#check TransvectionStruct
#check TransvectionStruct.mk
#check (⟨1,2,by simp,5⟩ : TransvectionStruct (Fin 2) ℝ)

open TransvectionStruct

#check (⟨1,2,by simp,5⟩ : TransvectionStruct (Fin 2) ℝ).toMatrix


/-- **Gaussian elimination for 2×2 matrices**: any matrix with `M 1 1 ≠ 0`
can be brought to diagonal form by one column operation and one row operation.
  The tactics `b_cases`, `simp` and `fin_cases` and `ext` may be useful.
  Hint: write out the row and column operations on a piece of paper first to figure out
  which transvections to use (Or you can peek at the algorithm at the beginning of this section). -/
theorem gaussian_elim_2x2 (M : Matrix (Fin 2) (Fin 2) 𝕜) (hM : M 1 1 ≠ 0) :
    ∃ T₁ T₂ : TransvectionStruct (Fin 2) 𝕜 , ∃ D : Fin 2 → 𝕜,
     T₁.toMatrix * M * T₂.toMatrix = diagonal D := by
  let T₁ : TransvectionStruct (Fin 2) 𝕜 :=  ⟨0, 1, by simp, (-M 0 1 / M 1 1)⟩
  let T₂ : TransvectionStruct (Fin 2) 𝕜 :=  ⟨1, 0, by simp, (-M 1 0 / M 1 1)⟩
  use T₁, T₂
  use fun i => (T₁.toMatrix * M * T₂.toMatrix) i i
  ext i j
  by_cases hij : i = j
  · rw [hij]
    simp
  · fin_cases i <;> fin_cases j <;> simp_all [T₁,T₂]

/- As a challenge, you can try the case where M 1 1 = 0, or think about the 3x3 case.
  You can gain some inspiration by looking at Mathlib's proof of the general case.
-/

/- Note: `apply?` finds and applies the general theorem.
  You might find it more rewarding to produce to the required lists L, L' of transvections yourself.
  Hint: you can use a separate definition `def myDef : someType := theDefinition` to define these-/
theorem gaussian_elim_3x3 (M : Matrix (Fin 3) (Fin 3) 𝕜) (h11 : M 1 1 ≠ 0) (h22 : M 2 2 ≠ 0) :
    ∃ (L L' : List (TransvectionStruct (Fin 3) 𝕜)) (D : Fin 3 → 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D := by apply?


end GaussianElimination
