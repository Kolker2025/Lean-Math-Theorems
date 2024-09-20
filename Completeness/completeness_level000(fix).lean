-- sup(s) - ε < s ≤ sup(s) level 

import data.real.basic
import tactic.suggest 
import game.Completeness.completeness_level01
import game.Completeness.completeness_level02
import game.Completeness.completeness_level03
import game.Completeness.completeness_level06
import game.sup_inf.level01
import game.sup_inf.level02
import game.sup_inf.level03
import game.sup_inf.level04
namespace xena 

noncomputable theory 
open_locale classical  
def sup (A : set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x ∧ ∀ y, ∀ a ∈ A, a ≤ y → x ≤ y


lemma do_now {x : ℝ} {S : set ℝ} (h : S ≠ ∅) (Hsup : is_sup S x)  : (∀ ε > 0, ∃ s ∈ S, x-ε<s ∧ s ≤ x) := 
begin
    

    rw is_sup at Hsup, 
    cases Hsup with a ha, 
    rw upper_bound at a,    

    intro ε, intro h, 
    use x, split, swap, 

    split, 
    linarith, linarith, 

    specialize a x, 
     specialize ha x, unfold upper_bound at ha, 
     have K : x ≤ x, linarith, hint, 

    



     -- rewrite this level cause I am pretty sure it is written incorrectly 

     
    
end

lemma le_of_le_add_eps {x y : ℝ} : (∀ ε > 0, y ≤ x + ε) →  y ≤ x :=
begin
  -- Let's prove the contrapositive, asking Lean to push negations right away.
  contrapose!,
  -- Assume `h : x < y`.
  intro h,
  -- We need to find `ε` such that `ε` is positive and `x + ε < y`.
  -- Let's use `(y-x)/2`
  use ((y-x)/2),
  -- we now have two properties to prove. Let's do both in turn, using `linarith`
  split,
  linarith,
  linarith,
end

end xena 