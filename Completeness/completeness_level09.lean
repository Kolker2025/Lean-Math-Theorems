import game.sup_inf.level01 -- hide
import game.sup_inf.level02 -- hide
import data.real.basic -- hide
import game.limits.Blockus_time -- hide
import game.Completeness.completeness_lemmas -- hide
import game.Completeness.level09 -- hide
import tactic -- hide

namespace xena -- hide

/-
# Chapter 6 : Completeness

## Level 9


Suppose that a sequence (a) is monotonically increasing. That is, ∀ (n : ℕ), a n ≤ a (n + 1). 
Assume that the sequence is bounded above as well. That is, there exists a number x such that a n ≤ x for all n ∈ ℕ. 
Prove that the sequence converges. 
-/



/- 
Here, we need to use the axiom of choice, 
which says that given any collection of bins, 
each containing at least one object, 
it is possible to construct a set by arbitrarily 
choosing one object from each bin, even if the collection is infinite.

-/

 axiom choice {α : Sort*} : nonempty α → α

  class inductive nonempty (α : Sort*) : Prop
| intro : α → nonempty

  example (α : Type*) : nonempty α ↔ ∃ x : α, true :=
iff.intro (λ ⟨a⟩, ⟨a, trivial⟩) (λ ⟨a, h⟩, ⟨a⟩)




/- Hide
Lemma : thing4 
{n N : ℕ} {a : ℕ → ℝ} (h : ∀n : ℕ, a n ≤ a (n + 1)) (h2 : N ≤ n) :  a N ≤ a n
-/ 
 



theorem mono_incr_seq_sup {a : ℕ → ℝ} {S : set.range a} {x : ℝ} (ha : ∀ (n : ℕ), a n ≤ a (n + 1)) (h2 : is_lub (set.range a) x) : is_limit a x := 
begin 
rw is_limit, 
intro ε, intro hε,
 


unfold_coes at S,
simp at S,
cases S with d hd,
cases hd with n₀ hn,

have Q := generate_element h2 (ε),
specialize Q hε,
unfold is_upper_bound at Q,
push_neg at Q,
cases Q with v hv,
cases hv with t ht,
unfold set.range at t,
cases t with N hN,
use N,
intro n,
intro j,
have U : a N ≤ x,
unfold is_lub at h2,
cases h2 with e he,
rw is_upper_bound at e,
specialize e (a N),

have Q : a N ∈ set.range a, by simp, 
specialize e Q, exact e,

have R : a N < x + ε,
linarith,
rw ← hN at ht,

have J : x - ε < a N ∧ a N < x + ε,
split,
exact ht, exact R,
have I : |a n - x| = |x - a n|,
rw abs_eq_abs_neg,
simp,
have B : a N ≤ a n, exact thing4 ha j,
have duh1 : 0 ≤ x - a N, linarith,
have duh3 : -a n ≤ - a N, linarith,
have duh4 : x - a n ≤ x - a N, linarith,
have duh5 : |x - a n| = x - a n,
unfold abs,
simp,
unfold is_lub at h2,
cases h2 with batman robin,
unfold is_upper_bound at batman,

apply batman,
simp,
have V : |x - a n| ≤ x - a N, linarith,
rw I, rw duh5, linarith, simp, 


end 

end xena -- hide