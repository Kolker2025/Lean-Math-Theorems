import data.real.basic
import tactic.suggest 
import game.Completeness.completeness_level01
import game.Completeness.completeness_level02
import game.Completeness.completeness_level03
import game.Completeness.completeness_level06
import game.Completeness.completeness_level07
import game.Completeness.completeness_level08
import game.sup_inf.level01
import game.sup_inf.level02
import game.sup_inf.level03
import game.sup_inf.level04
import game.Completeness.completeness_level10
namespace xena 

noncomputable theory 
open_locale classical  

lemma thing1 {d n : ℕ} (hd : 0 < d) (nd : d ≤ n) : 1 / n ≤ 1 / d := 
begin 

sorry, 

end 

lemma thing2 {d n : ℕ} (hd : 0 < d) (nd : d ≤ n) (nd : 1 / n ≤ 1 / d ) : 1 / (n + 1) < 1 / d := 
begin 

sorry, 

end 

lemma one_div_pos_plz {x : ℝ} : 0 < x  ↔ 0 < 1 / x :=
begin 
sorry, 

end 

lemma thing11 {d n : ℝ} (hd : 0 < d) (nd : d ≤ n) : 1 / n ≤ 1 / d := 
begin 

sorry, 

end 

lemma thing22 {d n : ℝ} (hd : 0 < d) (nd : d ≤ n) (nd : 1 / n ≤ 1 / d ) : 1 / (n + 1) < 1 / d := 
begin 

sorry, 

end 

lemma bruh {a : ℕ → ℝ} {n N : ℕ} (N1 : N ≤ n) : a N ≤ a n :=
begin
induction N with t ht, sorry, sorry,   

end

lemma lemmmmmmaaaaaa {x y z : ℝ} {S : set ℝ} {h : S ≠ ∅} (Ssup : is_sup S x) : z < x → ¬(is_upper_bound S z) := 
begin
unfold is_sup at Ssup,
intro l, 
cases Ssup with t ht, 
intro j, rw is_upper_bound at j, 
have T : upper_bound S z, exact j, 

have P := ht(z), 
have K := P(T), 
linarith, 
   
end


lemma generate_element {x : ℝ}{S : set ℝ} {h1 : S ≠ ∅} (h2 : is_lub S x) (ε : ℝ) : (0 < ε)→ ¬ (is_upper_bound S (x-ε)) :=
begin
intro h,
unfold is_lub at h2,
cases h2 with h2l h2r,
have Q := h2r(x-ε),
by_contradiction,
have R := Q(a),
linarith,
end  

--lemma thing4 


end xena 