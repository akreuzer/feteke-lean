/- Copyright (c) Alexander Kreuzer 2016

Lean Utilities Proofs for a proof of Feteke's lemma

All theorems are contained in the namespace ak.
Since these theorem come from different fields they are separated by sections.
-/

import theories.analysis.real_limit
import standard
import ak_compat
open eq.ops real analysis

set_option pp.coercions true
--set_option pp.implicit true

namespace ak

section

open nat

variable {A : Type}
variable [s : decidable_linear_order A]
include s
 
definition seq_max_to  (X : ℕ → A): ℕ → A
  | seq_max_to 0 := X 0
  | seq_max_to (n+1) := max (seq_max_to n)  (X (n+1))

proposition seq_max_to_le (X : ℕ → A) : 
  ∀ {n : ℕ}, ∀ { k : ℕ }, k ≤ n → X k ≤ seq_max_to X n :=
  begin
    intro n,
    induction n with n IH,
    intro k,
    intro this,
    have k < 0 ∨ k = 0, from lt_or_eq_of_le this,
    have k = 0, by simp,
    rewrite [this,↑seq_max_to],
    apply le_of_lt_or_eq,
    right,
    trivial,

    intro k,
    intro this,
    have k < succ n ∨ k = succ n, from lt_or_eq_of_le this,
    cases this,
    have k ≤ n, from le_of_lt_succ a,
    have H1: X k ≤ seq_max_to X n, from IH this, 
    have seq_max_to X n ≤ seq_max_to X (n+1), from 
      show seq_max_to X n ≤ max (seq_max_to X n)  (X (n+1)), from le_max_left _ _,
    apply le.trans H1 this,

    rewrite [a,↑seq_max_to],
    apply le_max_right
  end

-- We need the same with min instead of max
-- For now this is just a copy with max replace by min
-- Is there any better way by just taking the "reverse order"?
definition seq_min_to  (X : ℕ → A): ℕ → A
  | seq_min_to 0 := X 0
  | seq_min_to (n+1) := min (seq_min_to n)  (X (n+1))

proposition seq_min_to_ge (X : ℕ → A) : 
  ∀ {n : ℕ}, ∀ { k : ℕ }, k ≤ n → X k ≥ seq_min_to X n :=
  begin
    intro n,
    induction n with n IH,
    intro k,
    intro this,
    have k < 0 ∨ k = 0, from lt_or_eq_of_le this,
    have k = 0, by simp,
    rewrite [this,↑seq_min_to],
    apply le_of_lt_or_eq,
    right,
    trivial,

    intro k,
    intro this,
    have k < succ n ∨ k = succ n, from lt_or_eq_of_le this,
    cases this,
    have k ≤ n, from le_of_lt_succ a,
    have H1: X k ≥ seq_min_to X n, from IH this, 
    have seq_min_to X n ≥ seq_min_to X (n+1), from 
      show seq_min_to X n ≥ min (seq_min_to X n)  (X (n+1)), from min_le_left _ _,
    apply le.trans  this H1,

    rewrite [a,↑seq_min_to],
    apply min_le_right
  end

end

section 

open classical
open real

/-
 If x is the infimum of a set X 
 then for every epsilon > 0 
 there exists a point y epsilon close to x
-/
theorem inf_exists_point (X: set ℝ) (x: ℝ) (Hx: is_inf X x) (epsilon: ℝ) (Hepsilon: epsilon > 0) :
  ∃ (y : ℝ), (X y) ∧ (y-x < epsilon) :=
  by_contradiction 
  (begin
    intro H,
    have ∀ (y:ℝ), ¬ (X y ∧ (y-x < epsilon)), from iff.mp(forall_iff_not_exists) H,
    have ∀ (y:ℝ), (X y) → (y-x ≥ epsilon), from 
    begin
      intro y,
      intro HXy,
      have ¬ (X y) ∨ ¬ y-x < epsilon, from iff.mp !not_and_iff_not_or_not (this y),
      have ¬ y-x < epsilon, from or.elim this (assume Hp: ¬ (X y), absurd HXy Hp) (assume Hp: ¬ y-x < epsilon, Hp),
      apply le_of_not_gt,
      rewrite [↑gt],
      exact this
    end,
    have lb X (x+epsilon),  from 
    begin
      rewrite [↑lb],
      intros [y, HXy],
      apply eq.subst (add.comm  epsilon x),
      apply iff.mpr !add_le_iff_le_sub_right,
      exact (this y HXy)
    end,
    rewrite [↑is_inf at Hx],
    have x+epsilon≤ x, from (and.elim_right Hx) (x+epsilon) this,
    have epsilon ≤ 0, from eq.subst (sub_self x) (le_sub_left_of_add_le this),
    have epsilon < epsilon, from lt_of_le_of_lt this Hepsilon,
    exact absurd this (real.lt_irrefl epsilon)
  end)

open set rat nat

/-
 If a sequence X converges to x
 and y is the infimum of X ' univ
 then x must be greater or equal to y

 This theorem is actually not used in feteke.lean
-/
theorem inf_le_limit (X : ℕ → ℝ) (x : ℝ) (Hx : ak_compat.converges_to_seq X x):
  ∀ (y: ℝ), is_inf (X ' univ) y → x ≥ y := 
  begin
    intro,
    intro Hy,
    show _, from  or.elim (em (x≥ y)) (assume H: _, H) 
      begin
        intro Hc,
        let ε := (y - x) * (of_rat 0.5),
        have 0 < ε, from mul_pos (sub_pos_of_lt (lt_of_not_ge Hc)) (of_rat_lt_of_rat_of_lt dec_trivial),       
        unfold ak_compat.converges_to_seq at Hx,
        show _, from exists.elim (Hx this) 
        begin 
          intro N,
          intro HN,
          unfold ge at HN,
          have Hl1: X N < x + ε, from lt_add_of_sub_lt_right (sub_lt_of_abs_sub_lt_right (HN (le.refl N))),
          have Hl2: x + ε < y, from
          begin
            rewrite [mul_sub_right_distrib,add_sub,-sub_add_eq_add_sub],
            apply add_lt_of_lt_sub_right,
            rewrite [-mul_one x,-mul_one y,+mul.assoc,one_mul,-+mul_sub_left_distrib],
            apply mul_lt_mul_of_pos_right,
            exact (lt_of_not_ge Hc),
            xrewrite [-of_rat_one],
            xrewrite -of_rat_sub,
            apply of_rat_lt_of_rat_of_lt,
            exact dec_trivial,
          end,
          have Hl: X N < y, from lt.trans Hl1 Hl2,
          unfold [is_inf,lb,univ,image,mem,set_of] at Hy,
          have X N ≥ y, from (and.left Hy) (X N) (exists.intro N (and.intro true.intro rfl)),
          exact absurd Hl (not_lt_of_ge this) 
        end
      end
  end

/-
 If a sequence X has a limit then the infinimum of the X ' univ exists
-/
theorem ex_inf_of_seq_from_limit (X: ℕ → ℝ) [H : ak_compat.converges_seq X]:
  ∃ (y:ℝ), is_inf (X ' univ) y := 
  begin
    have ∃ (N:ℕ), ∀ (n:ℕ), n ≥ N → abs (X n - ak_compat.limit_seq X H) < 1, from ak_compat.converges_to_limit_seq X H zero_lt_one,
    exact exists.elim this 
    begin
      intros [N,Hn],
      let lb1 := seq_min_to X N,
      let lb2 := ak_compat.limit_seq X H - 1,
      let lbt := min lb1 lb2,

      apply exists_is_inf_of_inh_of_bdd,
      show (X ' univ ) (X 0), from 
      begin
        unfold [univ,image,mem,set_of],
        existsi 0,
        split,
        trivial,
        exact rfl
      end,

      unfold [lb,univ,image,mem,set_of],
      intros,
      exact exists.elim a
      begin
        intros [m,Hm],
        cases Hm with [Hm',Hm''],
        rewrite -Hm'',
        
        exact or.elim(decidable.em (m≥ N))
        begin
          intro HmN,
          have lb2 < X m, from sub_lt_of_abs_sub_lt_left (Hn m HmN),
          exact le.trans (min_le_right lb1 _) (le_of_lt this) 
        end
        begin
          intro HmN,
          have m ≤ N, from le_of_lt (lt_of_not_ge HmN),
          have lb1 ≤ X m, from seq_min_to_ge X this,
          exact le.trans !min_le_left this 
        end
      end
    end
  end
end


section 
open nat real

/-
 This theorem shows that
 "Integer division of x with y" - "Rational division of x with y" is in [0;1[
-/
theorem nat_div_estimate (x : ℕ) (y : ℕ) (Hy : y > (0:ℕ)):
  (of_nat x) / (of_nat y) - (of_nat (div x y)) < 1 ∧ (of_nat x) / (of_nat y) - of_nat (div x y) ≥ 0   :=
  begin
    have of_nat x = of_nat ((div x y) * y) + of_nat (x % y), from calc
      of_nat x = of_nat ((div x y) * y + (x % y)) : eq_div_mul_add_mod x y
      ... = of_nat ((div x y) * y) + of_nat (x % y) : !of_nat_add,
    have of_nat x / of_nat y = (of_nat ((div x y) * y) + of_nat (x % y)) / of_nat y, from this ▸ rfl,
    have H1: of_nat x / of_nat y = of_nat ((div x y) * y) / of_nat y + of_nat (x % y) / of_nat y, from eq.trans this (div_add_div_same (of_nat ((div x y) * y)) (of_nat (x % y)) (of_nat y))⁻¹,
    have dvd y ((div x y) * y) , from dvd_of_mod_eq_zero (mul_mod_left (div x y) y),
    have of_nat (div ((div x y) * y) y) = of_nat ((div x y) * y) / of_nat y, from of_nat_div _ _ this,
    rewrite [H1,-this,(nat.mul_div_cancel (x/y) Hy),add.comm,add_sub_cancel],
    have H2 : 0 < of_nat y, from of_nat_lt_of_nat_of_lt Hy,
    split,
    have H3: of_nat (x%y) / of_nat y  * of_nat y < of_nat y → of_nat (x%y) / of_nat y < of_nat y / of_nat y, from lt_div_of_mul_lt H2,
    have of_nat (x%y) / of_nat y * of_nat y = of_nat (x%y), from div_mul_cancel _ (ne_of_gt H2),
    have of_nat (x%y) < of_nat y → of_nat(x%y) / of_nat y < 1, from   ((div_self (ne_of_gt H2)) ▸ this ▸ H3),
    apply this,
    apply of_nat_lt_of_nat_of_lt,
    exact mod_lt x Hy,
    unfold ge,
    eapply le_div_of_mul_le,
    assumption,
    rewrite zero_mul,
    have 0 = of_nat 0, from rfl,
    rewrite this,
    apply of_nat_le_of_nat_of_le,
    exact !zero_le
  end

end


/-
 Section on real/ordered_field inequalities
-/
section

theorem div_lt_of_lt_mul_pos {A: Type} [s : linear_ordered_field A] {a b c: A} (Hc: 0<c):
  a < b * c → a / c < b := 
  begin
    intro H,
    have b = b * c * (inv c), from (mul.assoc b c (inv c))⁻¹ ▸ (mul_inv_cancel (ne_of_gt Hc))⁻¹  ▸ (mul_one b)⁻¹,
    rewrite [division.def,this],
    apply mul_lt_mul_of_pos_right,
    assumption,
    rewrite [inv_eq_one_div],
    apply one_div_pos_of_pos,
    assumption
  end

theorem inv_mul_lt_of_lt_pos_mul {A: Type} [s : linear_ordered_field A] {a b c: A} (Hb : 0<b):
  (inv b) * a < c → a < b * c :=
  begin
    intro H,
    have a = b * ((inv b) * a), from !mul.assoc ▸ (mul_inv_cancel (ne_of_gt Hb))⁻¹ ▸ (one_mul a)⁻¹,
    rewrite [this],
    apply mul_lt_mul_of_pos_left,
    repeat assumption
  end

theorem mul_lt_of_lt_pos_inv_mul {A: Type} [s : linear_ordered_field A] {a b c: A} (Hb : 0<b):
  b * a < c → a < (inv b) * c :=
  begin
    intro H,
    have a = inv b * (b * a), from !mul.assoc ▸ (inv_mul_cancel (ne_of_gt Hb))⁻¹ ▸ (one_mul a)⁻¹,
    rewrite [this],
    apply mul_lt_mul_of_pos_left,
    assumption,
    rewrite inv_eq_one_div,
    apply one_div_pos_of_pos,
    assumption
  end
 

theorem gt_div_of_mul_neg_lt {A: Type} [s : linear_ordered_field A] {a b c: A} (Hb : b<0):
  a * b < c → a > c / b :=
  begin
    intro H,
    rewrite division.def,
    have a = (a * b) * inv b, from !mul.assoc⁻¹ ▸ (mul_inv_cancel (ne_of_lt Hb))⁻¹ ▸ (mul_one a)⁻¹,
    rewrite this,
    apply mul_lt_mul_of_neg_right,
    assumption,
    rewrite [-one_mul,-division.def],
    apply one_div_neg_of_neg,
    assumption
  end

theorem mul_lt_of_gt_div_neg {A: Type} [s : linear_ordered_field A] {a b c: A} (Hb : b<0):
  a > c / b → a * b < c :=
  begin
    intro H,
    have c = (c * inv b) * b, from !mul.assoc⁻¹ ▸ (inv_mul_cancel (ne_of_lt Hb))⁻¹ ▸ (mul_one c)⁻¹,
    rewrite this,
    apply mul_lt_mul_of_neg_right,
    rewrite [-division.def],
    repeat assumption
  end

end 

-- Integer facts

section
open int

theorem le_nat_abs (a: ℤ) :
  a ≤ nat_abs a := 
  begin
    cases a,
    apply le_of_eq,
    apply of_nat_nat_abs_of_nonneg,
    apply dec_trivial,
    apply dec_trivial
  end

end
end ak

