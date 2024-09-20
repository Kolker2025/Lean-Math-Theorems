
import data.real.basic -- hide 

open_locale classical -- hide 

namespace xena --hide 

/-
# Chapter 6 : Completeness

## Level 1  


In the Completeness world, youj will be solving proofs regarding 
theroems and properties of bounded sets of reals.  

In Lean, we define the lower bounds of a set A such that 
∀ x : ℝ, | ∀ a ∈ A, x ≤ a. Essentially, for any number x, 
x is less than or equal to any element a in the set A.    

For the upper bounds, we define the upper bounds of a set A such that 
∀ x : ℝ, | ∀ a ∈ A, a ≤ x. Saying that for any number x, 
x is greater than or equal to any element a in the set A. 




For this proof, prove that there is a unique max on a set A of real numbers.
-/




def low_bounds (A : set ℝ) := { x : ℝ | ∀ a ∈ A, x ≤ a}
def up_bounds (A : set ℝ) := { x : ℝ | ∀ a ∈ A, a ≤ x}

 
def is_maximum (a : ℝ) (A : set ℝ) := a ∈ A ∧ a ∈ up_bounds A



infix ` is_a_max_of `:55 := is_maximum

def is_inf (x : ℝ) (A : set ℝ) := x is_a_max_of (low_bounds A)


infix ` is_an_inf_of `:55 := is_inf 






example (A : set ℝ) (x y : ℝ) (hx : x is_a_max_of A) (hy : y is_a_max_of A) : x = y :=
begin 

  have : x ≤ y, from hy.2 x hx.1, 
  have : y ≤ x, from hx.2 y hy.1,
  linarith,

  
end

end xena --hide 


