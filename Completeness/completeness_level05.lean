import data.real.basic -- hide 
import tactic.suggest  -- hide
import game.Completeness.completeness_level01 -- hide
import game.Completeness.completeness_level02 -- hide
import game.Completeness.completeness_level03 -- hide
--import game.Completeness.completeness_level04
import game.sup_inf.level01 -- hide
import game.sup_inf.level02 -- hide
import game.sup_inf.level03 -- hide
import game.sup_inf.level04 -- hide
namespace xena  -- hidev

noncomputable theory  -- hide
open_locale classical -- hide

/-
# Chapter 6 : Completeness

## Level 5 


Prove that b is the supremum of the set (a,b). 

-/

example (a b : ℝ) (h : a < b) : is_sup (set.Ioo a b) b := 
begin 
   
     
     unfold is_sup,
    split, 
    intro t, 
    intro j,
    rw set.Ioo at j,
    cases j with d hd, 
    exact le_of_lt hd, 

    intro t, 
    intro j, 
    apply le_of_not_gt, 
    intro k,

    rcases lt_trichotomy a t with han | haz | hap, 
    have l : t + b < b + b, linarith, ring at l, 
    have l1 : (t + b) /2 < b, linarith, 

    have P : t + t < t + b, linarith, ring at l, 
    have P1 : t  < (b + t) /2, linarith, 
    have s : a < (t + b) / 2, linarith, 

   
    have avgIn : a < (t + b)/2 ∧ (t + b)/2 < b, 
    split, 
    exact s, exact l1, 

    

    have R : (t + b)/2 ∈ set.Ioo a b, 
    split, 
    exact s, exact l1,

    unfold upper_bound at j, 
    revert j, 
    contrapose!, intro q, use (t + b)/2, split, 
    exact R, linarith, 

    
    have l : a + a < a + b, linarith, ring at l, 
    have l1 : (a + b) /2 < b, linarith,

    have P : a + b < b + b, linarith, ring at P, 
    have P1 : a  < (b + a) /2, linarith, 
    have s : (a + b) /2 < b, linarith, 

      have avgIn : a < (a + b)/2 ∧ (a + b)/2 < b,
      split, linarith,
    exact s, 

    have R : (a + b)/2 ∈ set.Ioo a b, 
    split, 
    rw haz, 
    rw haz at s, rw haz at P1, linarith, 

    rw haz, rw haz at s, exact s, 
    rw haz at R, 
    unfold upper_bound at j, 
    revert j, rw haz, 
    contrapose!, intro q, use (t + b)/2, split, 
    exact R, linarith,

    have P : a + b < b + b, linarith, ring at P, 
    have P1 : a  < (b + a) /2, linarith, 
    have s : (a + b) /2 < b, linarith, 

    have t1 : t < (b + a) /2, linarith, 
    revert j, unfold upper_bound, contrapose!, intro f, 
    use (a+b) /2, split, 
    
    have avgIn : a < (a + b)/2 ∧ (a + b)/2 < b,
      split, linarith,
    exact s, 

    have R : (a+b)/2 ∈ set.Ioo a b, 
    split, linarith, exact s, exact R, 
    linarith, 

end 

end xena  -- hide
    