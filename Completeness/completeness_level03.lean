import data.real.basic -- hide 
import game.Completeness.completeness_level01 -- hide
import game.Completeness.completeness_level02 -- hide 
open_locale classical -- hide 

/-
# Chapter 6 : Completeness

## Level 3 

The infimum, call it y, of a set A is the greatest lower bound
of A. In lean, we define the infimum as the maximum of the lwoer bound. 


Prove that for any number in a lower bounded set, 
there exists an element in A such that 
the element will be less than the number. 

Hint: it may help to prove by contrapositive. 
-/

def low_bounds (A : set ℝ) := { x : ℝ | ∀ a ∈ A, x ≤ a}

def is_inf (x : ℝ) (A : set ℝ) := x is_a_max_of (low_bounds A)
infix ` is_an_inf_of `:55 := is_inf



lemma inf_lt {A : set ℝ} {x : ℝ} (hx : x is_an_inf_of A) :
  ∀ y, x < y → ∃ a ∈ A, a < y :=
begin
  -- Let `y` be any real number.
  intro y,
  -- Let's prove the contrapositive
  contrapose,
  -- The symbol `¬` means negation. Let's ask Lean to rewrite the goal without negation,
  -- pushing negation through quantifiers and inequalities
  push_neg,
  -- Let's assume the premise, calling the assumption `h`
  intro h,
  -- `h` is exactly saying `y` is a lower bound of `A` so the second part of
  -- the infimum assumption `hx` applied to `y` and `h` is exactly what we want.
  exact hx.2 y h
end

