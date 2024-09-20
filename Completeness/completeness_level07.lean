import data.real.basic-- hide
import tactic.suggest -- hide
import game.Completeness.completeness_level01 -- hide
import game.Completeness.completeness_level02 -- hide
import game.Completeness.completeness_level03 -- hide
--import game.Completeness.completeness_level04
import game.sup_inf.level01 -- hide
import game.sup_inf.level02 -- hide
import game.sup_inf.level03 -- hide
import game.sup_inf.level04 -- hide
import data.nat.basic -- hide
import algebra.order -- hide
namespace xena -- hide

noncomputable theory -- hide
open_locale classical  -- hide

/-
# Chapter 6 : Completeness

## Level 7  


Prove the the supremum of the set {3 - 1 / n : n ∈ ℕ} is 3. 

Hint: Try using tauto when the goal looks obvious.

-/

example (S : set ℝ) (H : S = {r | ∃ v ∈ ℕ, r  = 3 - 1/(v + 1 : ℝ)}) : is_sup S 3 := 
begin 
 rw is_sup,  
 split, rw upper_bound, 
 intros h j, 
 rw le_iff_eq_or_lt, 
 right, rw H at j, 
 cases j with v hv, cases hv with f hf, 
 rw hf,
 refine sub_lt.mp _,
 norm_num, 
 tauto, 

 intro h, 
 rw upper_bound,
 cases H with t ht,
 intro j, 
 apply j, tauto,  


end 


end xena  -- hide