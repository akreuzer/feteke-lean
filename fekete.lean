/- Copyright (c) Alexander Kreuzer 2016

LEAN Proof of Feteke's lemma
-/

import theories.analysis.real_limit
import standard
import ak_utils
open real nat set rat pnat num classical int
open eq.ops

open ak

set_option pp.coercions true

definition subadditive (X : ℕ → ℝ) : Prop :=
   ∀ {n1: ℕ}, ∀ {n2: ℕ}, X (n1 + n2) ≤ X n1 + X n2

noncomputable definition seq_quot (X : ℕ → ℝ) : ℕ → ℝ
 | 0 := X 1
 | n := (X n) / real.of_nat n

lemma seq_quod_nn (X : ℕ→ℝ) (n : ℕ) (Hn : n > 0) :
  seq_quot X n = (X n) / real.of_nat n :=
begin
  cases n,
  have ¬ 0 > (0:ℕ), from not_lt_zero 0,
  apply absurd Hn this,
  unfold seq_quot
end

lemma seq_quod_eq_zero_one (X : ℕ → ℝ) :
  seq_quot X 0 = seq_quot X 1 :=
begin
  unfold seq_quot,
  have of_nat (succ zero) = (1:ℝ), from rfl,
  rewrite [this],
  xrewrite [div_one (X (succ zero))]
end


definition seq_mulindex (X : ℕ → ℝ) (c: ℕ) : ℕ → ℝ := λ n , X ( c * n) 

proposition subadditive_seq_mulindex (X : ℕ → ℝ) (Hsa : subadditive X) (c : ℕ) : subadditive (seq_mulindex X c) :=
  take n1,
  take n2,
  have H1: X ( c * n1 +  c * n2) ≤ X ( c * n1) + X ( c * n2), from Hsa,
  show X ( c * (n1 + n2)) ≤ X ( c * n1) + X ( c * n2), from  (left_distrib c n1 n2)⁻¹ ▸ H1

proposition t1 (X : ℕ → ℝ) (Hsa : subadditive(X)) (n: ℕ):
  X (n + 1) ≤ of_nat (n+1) * X 1 :=
  nat.induction_on n
    (show X 1 ≤ 1 * X 1, from  (one_mul (X 1))⁻¹ ▸  (real.le_refl (X 1)) )
      (take n,
        assume IH : X (n+1) ≤ of_nat (n+1) * (X 1),
        have H1 : X (n+1+1) ≤ X (n+1) + (X 1) , from Hsa,
        have H2 : X (n+1) + X 1 ≤ of_nat (n+1) * X 1 + X 1, from add_le_add_right IH (X 1),
        have H2': 1 * X 1 = X 1, from one_mul (X 1),
        have H2'': of_nat 1 = (1:ℝ), from rfl,
        have H2''': of_nat (n+1+1)  = of_nat (n+1) + of_nat 1, from of_nat_add (n+1) 1,
        have H3 : of_nat (n+1) * X 1 + X 1 = of_nat (n+1+1) * X 1, from calc
          of_nat (n+1) * (X 1) + (X 1) = of_nat (n+1) * X 1 + 1  * X 1 : H2'
          ...    = (of_nat (n+1) + 1) * X 1 : right_distrib
          ...    = (of_nat (n+1) + of_nat 1) * X 1 : H2''
          ...    = (of_nat (n+1+1)) * X 1 : H2''',
        have H4 : X (n+1) + X 1 ≤ of_nat (n+1+1) * X 1, from H3 ▸ H2,
        show X (n+1+1) ≤ of_nat (n+1+1) * X 1, from real.le_trans Hsa H4)


attribute subadditive [irreducible]

corollary t1b (X : ℕ → ℝ) (Hsa : subadditive X) (c: ℕ) (n: ℕ):
  X (c * (n + 1)) ≤ of_nat (n+1) * X c:=
  let Y := seq_mulindex X c in
  let HY := subadditive_seq_mulindex X Hsa c in
    have H: Y (n+1) ≤ of_nat (n+1) * Y 1, from  t1 Y HY n,
    have H': Y (n+1) = X(c * (n +1)), from rfl,
    have H'': Y 1 = X(c), from eq.subst (mul_one c) rfl,
    show  X(c * (n + 1)) ≤ of_nat (n+1) * X c , from eq.subst H'' (eq.subst H'  H)

proposition t2 (X : ℕ → ℝ) (Hsa : subadditive X) (c : ℕ) (n : ℕ) :
  X n ≤ of_nat (div n c) * X c + X (n % c) :=
  assert H1: X n ≤ X (n / c * c) + X (n % c), from
  begin      
    esimp [subadditive] at Hsa,
    have X n = X ((n / c * c) + n % c), from eq.subst (eq_div_mul_add_mod n c) rfl,
    rewrite [this],
    apply Hsa
  end,
  begin
    have div n c = 0 ∨ div n c ≠ 0, from !em,
    cases this,
    have n = n % c + (div n c) * c, from eq.subst !nat.add_comm  (eq_div_mul_add_mod n c),
    have n - (div n c) * c = n % c, from nat.sub_eq_of_eq_add this,
    rewrite [-this,a],
    have H: n - 0 = n, from rfl,
    have of_nat 0 * X c = 0, from zero_mul (X c),
    rewrite [zero_mul,H,this,zero_add],
    apply le_of_eq,
    apply rfl,

    have Ha: div n c = succ (pred (div n c)), from 
      or.elim (eq_zero_or_eq_succ_pred (div n c)) (by contradiction) (assume Hp: _, Hp),   
    rewrite [Ha],
    have X (c * succ (pred (div n c))) ≤ succ (pred (div n c)) * X c, from t1b X Hsa _ _,
    have H2: X (c * succ (pred (div n c))) + X (n % c) ≤ succ (pred (div n c)) * X c + X (n % c), from add_le_add_right this _,
    have H1': (div n c) * c = c * succ (pred (div n c)), from eq.subst Ha (nat.mul_comm (div n c) c),
    show _, from real.le_trans (eq.subst H1' H1) H2,
  end
  
corollary t2c (X : ℕ → ℝ) (Hsa : subadditive X) (c : ℕ) (n : ℕ) (Hc: c > (0 : ℕ)):
  X n ≤ of_nat (div n c) * X c + (seq_max_to X c) :=
  have n % c ≤ c, from le_of_lt (mod_lt _ Hc),
  have X(n % c) ≤ seq_max_to X c, from seq_max_to_le X this,
  have of_nat (div n c) * X c + X (n % c) ≤ of_nat (div n c) * X c + seq_max_to X c, from add_le_add_left this _,
  show _, from le.trans (t2 X Hsa c n) this 


lemma seq_quot_inf_conv ( X : ℕ → ℝ) (Hsa : subadditive X):
  ∀ (x : ℝ), is_inf ((seq_quot X) '[univ]) x → converges_to_seq (seq_quot X) x :=
  let Xq := seq_quot X in
begin
  intros [x, Hinfx],
  have HinfxEx: ∀ (n : ℕ), Xq n ≥ x, from
  begin
    intro n,
    unfold is_inf at Hinfx,
    cases Hinfx with [Hinfx1,Hinfx2],
    unfold lb at Hinfx1,
    apply (Hinfx1 (Xq n)),
    esimp [image,mem,set_of,univ],
    existsi n,
    split,
    trivial,
    apply rfl
  end,
  unfold converges_to_seq,
  intro [ε, epspos],
  have ε * of_rat 0.3 > 0, from mul_pos epspos (of_rat_lt_of_rat_of_lt dec_trivial),
  have ∃ (y : ℝ), (y∈ Xq '[univ]) ∧ (y - x < ε * of_rat 0.3), from inf_exists_point _ x Hinfx (ε * of_rat 0.3) this,
  have ∃ (n : ℕ), (Xq n - x < ε * of_rat 0.3) ∧ n > 0, from exists.elim this 
  begin
    intros [a, Ha],
    cases Ha with [Ha1,Ha2],
    esimp [image,mem,set_of] at Ha1,
    show ∃ (n : ℕ), ((Xq n) - x < ε * of_rat 0.3) ∧ n > 0, from exists.elim Ha1
    begin
      intro [n, Hn],
      cases Hn with [Hn1, Hn2],
      cases n with [n0],
      -- case n = 0
      existsi 1,
      rewrite [-seq_quod_eq_zero_one,Hn2],
      split,
      assumption,
      exact zero_lt_one,
      -- case n =/= 0
      existsi (succ n0),
      rewrite [Hn2],
      split,
      assumption,
      exact !zero_lt_succ
    end
  end,
  show ∃ (N:ℕ), ∀ {n:ℕ},  n≥ N → abs(seq_quot X n - x) < ε, from exists.elim this
  begin    
    intros [c,Hc],
    cases Hc with [Hc1, Hc2],
    let lb1 := inv (ε * of_rat 0.3) * seq_max_to X c,
    let lb2 := inv (ε * of_rat (-0.3)) * X c,
    existsi succ (max (int.nat_abs (ceil lb1)) (int.nat_abs (ceil lb2))),
    intros [n,Hn],
    have Xq n - x ≥ 0, from sub_nonneg_of_le (HinfxEx n),
    rewrite [abs_of_nonneg this],
    apply sub_lt_left_of_lt_add,
    have Hn': n > 0, from lt_of_lt_of_le (zero_lt_succ _) Hn,
    rewrite [seq_quod_nn X n Hn'],
    have X n ≤ of_nat (div n c) * X c + (seq_max_to X c), from t2c X Hsa c n Hc2,
    have Ht2c1: X n / of_nat n ≤  (of_nat (div n c) * X c + (seq_max_to X c)) / of_nat n, from div_le_div_of_le_of_pos this (of_nat_lt_of_nat_of_lt (eq.subst rfl  Hn')),
    have (of_nat (div n c) * X c + (seq_max_to X c)) / of_nat n = of_nat (div n c) * X c / of_nat n + (seq_max_to X c) / of_nat n, 
      from eq.symm (div_add_div_same (of_nat (div n c) * X c) (seq_max_to X c) (of_nat n)),
    have Ht2c1': X n / of_nat n ≤ of_nat (div n c) * X c / of_nat n + (seq_max_to X c) / of_nat n, from this ▸ Ht2c1,

    have H1: (seq_max_to X c) / of_nat n < ε * of_rat 0.3, from
    begin
      apply div_lt_of_lt_mul_pos,
      apply of_nat_lt_of_nat_of_lt,
      apply Hn',

      apply inv_mul_lt_of_lt_pos_mul,
      assumption,
      
      have lb1 ≤ nat_abs (ceil lb1), from le.trans (le_ceil lb1) (of_int_le_of_int_of_le (le_nat_abs (ceil lb1))),
      apply (lt_of_le_of_lt this),
      apply of_nat_lt_of_nat_of_lt,
      apply lt_of_le_of_lt !le_max_left (lt_of_succ_le Hn),
    end,
    have H2: of_nat (div n c) * X c / of_nat n < x + ε * of_rat 0.6, from 
    begin
      apply div_lt_of_lt_mul_pos,
      apply of_nat_lt_of_nat_of_lt,
      apply Hn',

      have c= succ (pred c), from or.elim (eq_zero_or_eq_succ_pred c) (assume H: _, absurd H (ne_of_gt Hc2))  (assume H: _, H),
      have Hseq_quot: X c / of_nat c = seq_quot X c, from calc
        X c / of_nat c = X (succ (pred c)) / of_nat (succ (pred c)) : this
        ... = seq_quot X (succ (pred c)) : rfl
        ... = seq_quot X c : this,

      have Hn'': 0< of_nat n, from
      begin
        cases n,
        have false, from (iff.mp (lt_self_iff_false 0) Hn'),
        exfalso,
        trivial,
        apply of_nat_lt_of_nat_of_lt,
        apply dec_trivial,
      end,

      cases em (X c ≥ 0) with [HXc,HXcn],
      have of_nat (n / c) ≤ of_nat n / of_nat c, from le_of_sub_nonneg (and.elim_right (nat_div_estimate n c Hc2)), 
      have of_nat (n / c) * X c ≤ (of_nat n / of_nat c) * X c, from mul_le_mul_of_nonneg_right this HXc,
      apply lt_of_le_of_lt this,
      xrewrite (division.def (of_nat n) (of_nat c)),
      rewrite [mul.assoc,mul.comm],
      apply mul_lt_mul_of_pos_right,
      rewrite [mul.comm,-division.def],

      xrewrite Hseq_quot,
      apply lt_add_of_sub_lt_left,
      apply lt.trans Hc1,
      apply mul_lt_mul_of_pos_left,
      apply of_rat_lt_of_rat_of_lt,
      apply dec_trivial,
      assumption,
      assumption,
      
      have  of_nat n / of_nat c - 1 < of_nat (n / c), from sub_lt_right_of_lt_add (lt_add_of_sub_lt_left (and.elim_left (nat_div_estimate n c Hc2))),
      have of_nat (n / c) * X c < (of_nat n / of_nat c - 1) * X c, from mul_lt_mul_of_neg_right this (lt_of_not_ge HXcn),
      apply lt.trans this,
      rewrite [mul_sub_right_distrib,-mul_inv_cancel (ne_of_gt (of_nat_lt_of_nat_of_lt Hn')) ],
      xrewrite (division.def (of_nat n) (of_nat c)),
      rewrite [*mul.assoc,-mul_sub_left_distrib,mul.comm],
      apply mul_lt_mul_of_pos_right,
      apply sub_lt_left_of_lt_add,
      rewrite [mul.comm,-division.def],
      xrewrite Hseq_quot,
      rewrite [add.comm,add.assoc],
      apply lt_add_of_sub_lt_left,
      apply lt.trans Hc1,
      apply lt_add_of_sub_lt_left,
      rewrite [-mul_sub_left_distrib],
      xrewrite [-of_rat_sub],
      apply mul_lt_of_lt_pos_inv_mul,
      assumption,
      have (0.3:ℚ) - 0.6 = -0.3, from dec_trivial,
      rewrite this,
      apply mul_lt_of_gt_div_neg,
      apply mul_neg_of_pos_of_neg,
      assumption,
      apply of_rat_lt_of_rat_of_lt,
      apply dec_trivial,
      have lb2 ≤ nat_abs (ceil lb2), from le.trans (le_ceil lb2) (of_int_le_of_int_of_le (le_nat_abs (ceil lb2))),
      rewrite [division.def,mul.comm],
      apply (lt_of_le_of_lt this),
      apply of_nat_lt_of_nat_of_lt,
      apply lt_of_le_of_lt !le_max_right (lt_of_succ_le Hn),
      
      assumption
    end,
    apply lt_of_le_of_lt Ht2c1',
    apply lt_of_lt_of_le (add_lt_add H2 H1),
    rewrite add.assoc,
    apply add_le_add_left,
    rewrite [-left_distrib,-(mul_one ε),mul.assoc],
    apply mul_le_mul_of_nonneg_left,
    rewrite [one_mul,-of_rat_one],
    xrewrite -of_rat_add,
    apply of_rat_le_of_rat_of_le,
    apply dec_trivial,

    apply real.le_of_lt,
    exact epspos
  end,
end

lemma seq_quot_conv_inf (X : ℕ → ℝ) (Hsa : subadditive X):
  ∀ (x : ℝ),  converges_to_seq (seq_quot X) x → is_inf ((seq_quot X) '[univ]) x :=
  begin
    intros [x,Hx],
    have lb (X '[univ]) x, from
    begin
      unfold [lb,univ,image,mem,set_of],
      intros [y,Hy],
      exact exists.elim Hy 
      begin
        intro [n,Hn],
        rewrite -(and.right Hn),
        exact or.elim(em (x ≤ X n)) (assume H: _, H)
        begin
          intro He,
          let ε := (x - X n) * of_rat (0.5),
          have 0 < ε, from mul_pos (sub_pos_of_lt (lt_of_not_ge He)) (of_rat_lt_of_rat_of_lt dec_trivial),
          unfold converges_to_seq at Hx,
          exact exists.elim (Hx this)
          begin
            intro [N,HN],
            apply sorry
          end
        end
      end
    end,
    apply sorry
  end


-- Feteke's Lemma
-- This will be just a combination of seq_quot_inf_conv and seq_quot_conv_inf
theorem feteke (X : ℕ → ℝ) (Hsa: subadditive X):
  ∀ (x: ℝ), converges_to_seq (seq_quot X) x ↔ is_inf ((seq_quot X) '[univ]) x
  := 
  take x, iff.intro (seq_quot_conv_inf X Hsa x) (seq_quot_inf_conv X Hsa x)
