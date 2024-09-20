import game.limits.bounded_if_convergent -- hide
import game.limits.Lemmas -- hide
import game.limits.Blockus_time -- hide
import game.sets.L01defs -- hide
import game.sup_inf.GLBprop_if_LUBprop -- hide
import data.real.basic -- hide
import tactic.linarith -- hide

namespace xena -- hide

/-
# Chapter 7 : Limits

## Level 6

In this proof you will be showing that if you have two real numbers a and b in which b is positive.
and multiply them together, the product will be ≤ e * b if a ≤ e. This is true regardless of
what is being added to a * b or e * b as long as it is consistent. 
Just like the last proof this should be a pretty obvious fact but to Lean it isn't trivial.

-/
lemma pos_mul_pos_add_pos_mul_pos_le2 {a b c d e: ℝ} (hb : 0 ≤ b) 
  (hae: a ≤ e): a * b + c * d ≤ e * b + c * d :=
begin
have L1 : b ≤ b, linarith, 
have L2 : a * b ≤ e * b, 
exact mul_le_mul_right1 hb hae,  
linarith, 

end 

end xena -- hide
