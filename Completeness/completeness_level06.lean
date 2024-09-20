import data.real.basic -- hide
import tactic.suggest -- hide
import game.Completeness.completeness_level01 -- hide
import game.Completeness.completeness_level02 -- hide
import game.Completeness.completeness_level03 -- hide
--import game.Completeness.completeness_level04
import game.sup_inf.level01 -- hide
import game.sup_inf.level02 -- hide
import game.sup_inf.level03 -- hide
import game.sup_inf.level04 -- hide
namespace xena  -- hide

noncomputable theory -- hide 
open_locale classical -- hide

/-
# Chapter 6 : Completeness

## Level 6  

Prove that a nonempty and upper bounded 
set has a unique least upper bound. 

-/

theorem nonempty_and_bounded_has_unique_LUB (x y : ℝ) (S : set ℝ) (H : has_lub S) (hx : is_lub S x) (hy : is_lub S y):
(S ≠ ∅) ∧ (has_lub S)  → x = y := 
begin 
    intro h, 
    cases h with t ht, 
    cases ht with d hd, 

    cases hx with d hd,  
    cases hy with f hf, 

    specialize hd y, 
    specialize hf x,

    specialize hf d, 
    specialize hd f, 
    linarith,         

    

end

end xena  -- hide