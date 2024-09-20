import game.limits.bounded_if_convergent
import game.limits.Blockus_time
import game.sets.L01defs
import game.sup_inf.GLBprop_if_LUBprop
import data.real.basic
import tactic.linarith


/-
# Chapter 7 : Limit Lemmas

## Level 10



This lemma will help in dealing with obvious math roadblocks that Lean sometimes 
does not comprehend well. 

Just looking at this equation and all the hypothesis, we know it's true. 
But Lean just needs to know this. 
-/




lemma soul_sucking_deep_sadness {ε a : ℝ} (h : 0 < ε) (ha : a ≠ 0): (1 / a) * (a * ε) = ε :=
begin 
simp, rw ← mul_assoc, rw inv_mul_cancel, linarith, exact ha, 
end 


