import GlimpseOfLean.Library.Basic
open Set

namespace ClassicalPropositionalLogic

/- Let's try to implement a language of classical propositional logic
-/

def Variable : Type := ℕ

/- We define the notion of propositional `Formula` inductively.
    The base cases consist of variable, indexed by the `Variable` type defined above, or the falsum.
    New formulas are made through conjunction, disjunction and implication.
    The negation `~A` of a formula `A` is defined as `A ⇒ bot`, see below. -/
inductive Formula : Type where
  | var : Variable → Formula -- indexed variable symbols
  | bot : Formula -- the falsum
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | imp : Formula → Formula → Formula

/- We define some notation. Recall that you can mouse over a symbol to see how to write it. -/
open Formula
local notation:max (priority := high) "#" x:max => var x
local infix:30 (priority := high) " || " => disj
local infix:35 (priority := high) " && " => conj
local infix:28 (priority := high) " ⇒ " => imp
local notation (priority := high) "⊥" => bot

def neg (A : Formula) : Formula := A ⇒ ⊥
local notation:(max+2) (priority := high) "~" x:max => neg x

def top : Formula := ~⊥
local notation (priority := high) "⊤" => top

def equiv (A B : Formula) : Formula := (A ⇒ B) && (B ⇒ A)
local infix:29 (priority := high) " ⇔ " => equiv

/- Given an evaluation to `True` or `False` for each variable symbol,
  we can inductively define "truth" (with respect to Lean's underlying logic)
  of arbitrary propositional formulas. -/
@[simp]
def IsTrue (φ : Variable → Prop) : Formula → Prop
  | ⊥      => False
  | # P    => φ P
  | A || B => IsTrue φ A ∨ IsTrue φ B
  | A && B => IsTrue φ A ∧ IsTrue φ B
  | A ⇒ B => IsTrue φ A → IsTrue φ B

/-- A set of Formulas is satisfied if every element evaluates to `True`-/
def Satisfies (φ : Variable → Prop) (Γ : Set Formula) : Prop := ∀ {A}, A ∈ Γ → IsTrue φ A

/-- A formula `A` is modeled by a theory (= Set of formulas) `Γ` if `A` holds
  whenever `Γ` is satisfied. -/
def Models (Γ : Set Formula) (A : Formula) : Prop := ∀ {φ}, Satisfies φ Γ → IsTrue φ A

local infix:27 (priority := high) " ⊨ " => Models

/-- If a formula is modeled by the empty theory, then it is a valid formula. -/
def Valid (A : Formula) : Prop := ∅ ⊨ A

variable {φ : Variable → Prop} {A B : Formula}

/- We record some lemmas below that are not strictly necessary.
  They help to rewrite the more syntactic left-hand side to the more  semantic right-hand side.
  This may be helpful when exploring proof strategies. -/
lemma isTrue_bot : IsTrue φ ⊥ ↔ False := Iff.rfl

lemma isTrue_var {P} : IsTrue φ (# P) ↔ φ P := Iff.rfl

lemma isTrue_or : IsTrue φ (A || B) ↔ IsTrue φ A ∨ IsTrue φ B := Iff.rfl

lemma isTrue_and : IsTrue φ (A && B) ↔ IsTrue φ A ∧ IsTrue φ B := Iff.rfl

lemma isTrue_imp : IsTrue φ (A ⇒ B) ↔ IsTrue φ A → IsTrue φ B := Iff.rfl

/- Here are some basic properties of validity.
We tag these lemmas with `@[simp]` so that they are automatically used by the `simp` tactic. -/

@[simp] lemma isTrue_neg : IsTrue φ ~A ↔ ¬ IsTrue φ A := by
  rw [neg, isTrue_imp]
  -- After the rewrite below, we are done, as `¬ x` is defined as `x → ⊥` internally in Lean
  rw [isTrue_bot]

/- Alternate proof method-/
lemma isTrue_neg' : IsTrue φ ~A ↔ ¬ IsTrue φ A := by simp [neg]

@[simp] lemma isTrue_top : IsTrue φ ⊤ := by
  intro h
  exact h

lemma isTrue_top' : IsTrue φ ⊤ := by
  simp [top]

lemma isTrue_top'' : IsTrue φ ⊤ := id


@[simp] lemma isTrue_equiv : IsTrue φ (A ⇔ B) ↔ (IsTrue φ A ↔ IsTrue φ B) := by
  rw [equiv, isTrue_and, isTrue_imp, isTrue_imp]
  exact Iff.symm iff_iff_implies_and_implies

lemma isTrue_equiv' : IsTrue φ (A ⇔ B) ↔ (IsTrue φ A ↔ IsTrue φ B) := by
  exact Iff.symm iff_iff_implies_and_implies

lemma isTrue_equiv'' : IsTrue φ (A ⇔ B) ↔ (IsTrue φ A ↔ IsTrue φ B) := by
  simp [equiv]
  tauto

/- As an exercise, let's prove (using classical logic) the double negation elimination principle. -/
example : Valid (~~A ⇔ A) := by
  intros φ _
  simp

example : Valid (~~A ⇔ A) := by
  rw [Valid, Models]
  intro φ h
  rw [isTrue_equiv, isTrue_neg, isTrue_neg]
  exact not_not


/- We will frequently need to add an element to a set. This is done using
the `insert` function: `insert A Γ` means `Γ ∪ {A}`. -/
@[simp] lemma satisfies_insert_iff {Γ} : Satisfies φ (insert A Γ) ↔ IsTrue φ A ∧ Satisfies φ Γ := by
  simp [Satisfies]

/- Let's define provability w.r.t. classical logic. -/
section
set_option hygiene false -- this is a hacky way to allow forward reference in notation
local infix:27 " ⊢ " => ProvableFrom

/- `Γ ⊢ A` is the predicate that there is a proof tree with conclusion `A` with assumptions from
  `Γ`. This is a typical list of rules for natural deduction with classical logic. -/
inductive ProvableFrom : Set Formula → Formula → Prop
  -- `A` belongs to the list of axioms
  | ax    : ∀ {Γ A},   A ∈ Γ   → Γ ⊢ A
  -- If we can prove `B` from `Γ ∪ {a}`, then `Γ ⊢ A ⇒ B`
  | impI  : ∀ {Γ A B},  insert A Γ ⊢ B                → Γ ⊢ A ⇒ B
  /- If we have a proof that `A ⇒ B` also of `A`, then obtain a proof of `B`.
    The variable `A` is made explicit here to help get more context from the Lean InfoView. -/
  | impE  : ∀ {Γ B} (A),           Γ ⊢ (A ⇒ B) → Γ ⊢ A  → Γ ⊢ B
  | andI  : ∀ {Γ A B},           Γ ⊢ A       → Γ ⊢ B  → Γ ⊢ A && B
  | andE1 : ∀ {Γ A B},           Γ ⊢ A && B           → Γ ⊢ A
  | andE2 : ∀ {Γ A B},           Γ ⊢ A && B           → Γ ⊢ B
  | orI1  : ∀ {Γ A B},           Γ ⊢ A                → Γ ⊢ A || B
  | orI2  : ∀ {Γ A B},           Γ ⊢ B                → Γ ⊢ A || B
  -- Recall that `insert A Γ` means `Γ ∪ {A}`
  | orE   : ∀ {Γ A B C}, Γ ⊢ A || B → insert A Γ ⊢ C → insert B Γ ⊢ C → Γ ⊢ C
  | botC  : ∀ {Γ A},   insert ~A Γ ⊢ ⊥                → Γ ⊢ A

end

local infix:27 (priority := high) " ⊢ " => ProvableFrom

/- A formula is provable if it is provable from an empty set of assumption. -/
def Provable (A : Formula) := ∅ ⊢ A

export ProvableFrom (ax impI impE botC andI andE1 andE2 orI1 orI2 orE)
variable {Γ : Set Formula}

/- Proving something using the ax rule requires showing that `A ∈ Γ`. In the concrete situations we
  will encounter, the following lemmas about insert will suffice most of the time.
  ```
  mem_singleton x : x ∈ {x}
  mem_insert x s : x ∈ insert x s
  mem_insert_of_mem y : x ∈ s → x ∈ insert y s
  ```
  -/

/- Prove the following using lemmas about `insert`-/
example : {A, B} ⊢ A && B := by
  apply andI
  · apply ax
    exact mem_insert A {B}
  · apply ax
    apply mem_insert_of_mem
    rfl

-- A one-line solution
example : {A, B} ⊢ A && B := by
  exact andI (ax (mem_insert _ _)) (ax (mem_insert_of_mem _ (mem_singleton _)))

/- Arguments as above can become pretty tedious.
  We define a simple tactic `apply_ax`: it proves statements that can be shwon from the ax rule,
  combined with the three lemmas above
     -/
syntax "solve_mem" : tactic
syntax "apply_ax" : tactic
macro_rules
  | `(tactic| solve_mem) =>
    `(tactic| first | apply mem_singleton | apply mem_insert |
                      apply mem_insert_of_mem; solve_mem
                    | fail "tactic \'apply_ax\' failed")
  | `(tactic| apply_ax)  => `(tactic| { apply ax; solve_mem })

-- Now use the `apply_ax` tactic to show the same example
example : {A, B} ⊢ A && B := by
  apply andI
  · apply_ax
  · apply_ax

/- All of the below examples can be completed by a chain of `apply (proofRule)` statements, combined
  with our custom `apply_ax` tactic. -/

example : Provable (~~A ⇔ A) := by
  apply andI
  · apply impI
    apply botC
    apply impE _ _ (by apply_ax)
    apply_ax
  · apply impI
    apply impI
    apply impE _ (by apply_ax)
    apply_ax

/- Optional exercise: prove the law of excluded middle. -/
example : Provable (A || ~A) := by
  apply botC
  apply impE _ (by apply_ax)
  apply orI2
  apply impI
  apply impE _ (by apply_ax)
  apply orI1 (by apply_ax)

/- Optional exercise: prove one of the de-Morgan laws.
  This is a bit more work than the previous ones -/
example : Provable (~(A && B) ⇔ ~A || ~B) := by
  apply andI
  · apply impI
    apply botC
    apply impE (A := A && B) (by apply_ax)
    apply andI
    · apply botC
      apply impE (A := _ || _) (by apply_ax)
      apply orI1 (by apply_ax)
    · apply botC
      apply impE (A := _ || _) (by apply_ax)
      apply orI2 (by apply_ax)
  · apply impI
    apply impI
    apply orE (by apply_ax)
    · apply impE _ (by apply_ax)
      apply andE1 (by apply_ax)
    · apply impE _ (by apply_ax)
      apply andE2 (by apply_ax)

/- You can prove the following using `induction` on `h`. You will want to tell Lean that you want
  to prove it for all `Δ` simultaneously using `induction h generalizing Δ`.
  Lean will mark created assumptions as inaccessible (marked with †)
  if you don't explicitly name them.
  You can name the last inaccessible variables using for example `rename_i ih` or
  `rename_i A B h ih`. Or you can prove a particular case using `case impI ih => <proof>`.
  You will probably need to use the lemma
  `insert_subset_insert : s ⊆ t → insert x s ⊆ insert x t`. -/
lemma weakening {Δ : Set Formula} (h : Γ ⊢ A) (h2 : Γ ⊆ Δ) : Δ ⊢ A := by
  induction h generalizing Δ
  case ax A ih => apply ax; exact mem_of_subset_of_mem h2 ih
  case impI A B ih₁ ih₂ => apply impI; apply ih₂; exact insert_subset_insert h2
  case impE A B hA hB ih₁ ih₂ => apply impE _ (ih₁ h2) (ih₂ h2)
  case andI ih₁ ih₂ => apply andI (ih₁ h2) (ih₂ h2)
  case andE1 A B hAB ih => apply andE1 (ih h2)
  case andE2 A B hAB ih => apply andE2 (ih h2)
  case orI1 A B hA ih => apply orI1 (ih h2)
  case orI2 A B hB ih => apply orI2 (ih h2)
  case orE A B C hAB hA hB ih₁ ih₂ ih₃ =>
    apply orE (ih₁ h2) (ih₂ (insert_subset_insert h2)) (ih₃ (insert_subset_insert h2))
  case botC A hA ih => apply botC (ih (insert_subset_insert h2))

lemma weakening' {Δ} (h : Γ ⊢ A) (h2 : Γ ⊆ Δ) : Δ ⊢ A := by
  induction h generalizing Δ
  case ax => apply ax; (expose_names; exact mem_of_subset_of_mem h2 h)
  case impI ih => apply impI; solve_by_elim [insert_subset_insert]
  case impE ih₁ ih₂ => apply impE <;> solve_by_elim
  case andI ih₁ ih₂ => apply andI <;> solve_by_elim
  case andE1 ih => apply andE1 <;> solve_by_elim
  case andE2 ih => apply andE2 <;> solve_by_elim
  case orI1 ih => apply orI1; solve_by_elim
  case orI2 ih => apply orI2; solve_by_elim
  case orE ih₁ ih₂ ih₃ => apply orE <;> solve_by_elim [insert_subset_insert]
  case botC ih => apply botC; solve_by_elim [insert_subset_insert]

/- Use the `apply?` tactic to find the lemma that states `Γ ⊆ insert x Γ`.
  You can click the blue suggestion in the right panel to automatically apply the suggestion. -/
lemma ProvableFrom.insert (h : Γ ⊢ A) : insert B Γ ⊢ A := by
  apply weakening h
  exact subset_insert B Γ

/- Proving the deduction theorem is now easy. -/
lemma deduction_theorem (h : Γ ⊢ A) : insert (A ⇒ B) Γ ⊢ B := by
  apply impE A
  · apply_ax
  · exact ProvableFrom.insert h

lemma Provable.mp (h1 : Provable (A ⇒ B)) (h2 : Γ ⊢ A) : Γ ⊢ B := by
  apply impE A
  · apply weakening h1 (empty_subset _)
  · exact h2

/-- To prove a disjunction, you can use the tactics `left` and `right`, or directly use
  the constructors `Or.inl` and `Or.inr`.
  To eliminate from a disjunction `h`, you can use `cases h` and obtain cases `inl a` and `inr b`. -/
theorem soundness_theorem (h : Γ ⊢ A) : Γ ⊨ A := by
  -- Take any valuation v such that every formula in `Γ` evaluates to `True`.
  intro v hφ
  -- We peform induction on the complexity of the proof `Γ ⊢ A`.
  induction h
  case ax ih => exact hφ ih
  case impI ih₁ ih₂ =>
    -- We assume that `A†` holds and move to prove `B†`.
    intro hA
    --  It suffices to show that the sufficient condition in `ih₂` holds.
    apply ih₂
    -- Thus we need to show that every formula `D` belonging to `insert A Γ†` is True.
    intro D hD
    -- `D` belongs to `insert A Γ†` iff (`D` = A or `D` belongs to `Γ†`) .
    rw [mem_insert_iff] at hD
    -- Now perform case distinction on hD.
    cases hD
    -- If `D = A`, then we are done, since `hA` tells us `IsTrue v A`
    case inl h =>
    /- note that this rewrite is necessary! A are not literally the same object,
      we "merely" have a proof of equality. -/
      rw [h]
      exact hA
    -- Now hφ tells us that every formula in `Γ†` is true, while `h` tells us that `D ∈ Γ†`.
    case inr h => exact hφ h
  case impE ih₁ ih₂ => exact (ih₁ hφ) (ih₂ hφ)
  case andI ih₁ ih₂   => rw [isTrue_and]; exact And.intro (ih₁ hφ) (ih₂ hφ)
  /- Some notes about the solution above:
    1. the rewrite `rw [isTrue_and]` is not strictly necessary
    2. the constructor `And.intro` can be replaced by the anonymous constructor ⟨_, _⟩
  Thus one alternate solution is
    case andI ih₁ ih₂ => exact ⟨ih₁ hφ, ih₂ hφ⟩ -/
  case andE1 ih  => apply (ih hφ).left
  case andE2 ih  => apply (ih hφ).right
  case orI1 ih =>
    rw [isTrue_or]
    left
    apply ih
    exact hφ
  /- As in the andI case, the proof of `orI1` and `orI2` can be golfed  -/
  case orI2 ih => exact .inr (ih hφ)
  case orE A B C _ _ _ ih₁ ih₂ ih₃ =>
    -- Either A or B is true
    have hAB : IsTrue v A ∨ IsTrue v B := ih₁ hφ
    cases hAB
    /- The simp tactic is strong enough to perform the necessary menial labour for us. Compare this
    agains the explicit proof in the `impI` case.-/
    case inl hA => simp [*]
    case inr hB => simp [*]
/- the `orE` case also admits a one-line proof. The symbol `<;>` instructs the next tactic
  (`simp [*]`) to run on every subgoal. We could have also used this trick in the above solution.
`case orE ih₁ ih₂ ih₃ => refine (ih₁ hφ).elim (fun hA => ih₂ ?_) (fun hB => ih₃ ?_) <;> simp [*]`-/
  case botC ih =>
    -- Suppose `¬ IsTrue v A†`.
    by_contra hnA
    -- Then `IsTrue v (~A†)`
    rw [← isTrue_neg] at hnA
    apply ih
    simp [*]

theorem soundness_theorem' (h : Γ ⊢ A) : Γ ⊨ A := by
  -- sorry
  induction h <;> intros φ hφ
  solve_by_elim
  case impI ih => intro hA; apply ih; simp [*]
  case impE ih₁ ih₂ => exact ih₁ hφ (ih₂ hφ)
  case botC ih => by_contra hA; apply ih (satisfies_insert_iff.mpr ⟨by exact hA, hφ⟩)
  case andI ih₁ ih₂ => exact ⟨ih₁ hφ, ih₂ hφ⟩
  case andE1 ih => exact (ih hφ).1
  case andE2 ih => exact (ih hφ).2
  case orI1 ih => exact .inl (ih hφ)
  case orI2 ih => exact .inr (ih hφ)
  case orE ih₁ ih₂ ih₃ => refine (ih₁ hφ).elim (fun hA => ih₂ ?_) (fun hB => ih₃ ?_) <;> simp [*]
  -- sorry

theorem valid_of_provable (h : Provable A) : Valid A := by
  -- sorry
  exact soundness_theorem h
  -- sorry

/-
  If you want, you can now try some these longer projects.

  1. Prove completeness: if a formula is valid, then it is provable
  Here is one possible strategy for this proof:
  * If a formula is valid, then so is its negation normal form (NNF);
  * If a formula in NNF is valid, then so is its conjunctive normal form (CNF);
  * If a formula in CNF is valid then it is syntactically valid:
      all its clauses contain both `A` and `¬ A` in it for some `A` (or contain `⊤`);
  * If a formula in CNF is syntactically valid, then its provable;
  * If the CNF of a formula in NNF is provable, then so is the formula itself.
  * If the NNF of a formula is provable, then so is the formula itself.

  2. Define Gentzen's sequent calculus for propositional logic, and prove that this gives rise
  to the same provability.
-/

end ClassicalPropositionalLogic
