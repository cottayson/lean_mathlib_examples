import tactic.norm_num
import data.real.basic

open tactic

-- for avoiding ?m_1, ?m_2, etc
inductive x : Prop | intro : x
inductive y : Prop | intro : y
inductive z : Prop | intro : z
lemma hx : x := x.intro
lemma hy : y := y.intro
lemma hz : z := z.intro

#check (eq_true_intro _).mpr
-- (eq_true_intro ?M_2).mpr : true → ?M_1
-- how ?M_2 related to ?M_1 ? You don't know.

#check (eq_true_intro hx).mpr
-- (eq_true_intro hx).mpr : true → x
-- Now you know it: x is type of hx.

#check @eq_true_intro

example : 1 ≤ 1 := by {
  norm_num,
  trace_result,
}

example : 1 ≤ 1 :=
(eq_true_intro (le_refl 1)).mpr trivial

example : 1 ≤ 1 := le_refl 1

/-- A predicate representing partial progress in a proof of `min_fac`. -/
def min_fac_helper (n k : ℕ) : Prop :=
0 < k ∧ bit1 k ≤ nat.min_fac (bit1 n)

example : 6 = (bit0 $ bit1 $ bit1 0) := rfl
example : 16 = 
(bit0 $ bit0 $ bit0 $ bit0 $ bit1 0) := rfl
example : ∀ x, bit0 x = 2 * x     := nat.bit0_val
example : ∀ x, bit1 x = 2 * x + 1 := nat.bit1_val


set_option pp.beta true
set_option trace.simplify.rewrite true

lemma helper (h : 5 ≤ 1) : false := by {
  have H := nat.le.dest h,
  have not_H : ¬ ∃ (k : ℕ), 5 + k = 1 := sorry,
  exact absurd H not_H,
}

example : ¬ min_fac_helper 0 2 := by {
  unfold min_fac_helper,
  intro h,
  cases h with h₁ h₂,
  clear h₁, -- because h₁ : true
  rw nat.min_fac_one at h₂,
  exact helper h₂,
}

lemma test1 : (2 : ℝ) + 2 = 4 := by norm_num1
lemma test2 : (12345.2 : ℝ) ≠ 12345.3 := by norm_num1
lemma test3 : (73 : ℝ) < 789/2 := by norm_num1
lemma test4 : 123456789 + 987654321 = 1111111110 := by norm_num1
lemma test5 (R : Type*) [ring R] : (2 : R) + 2 = 4 := by norm_num1
lemma test6 (F : Type*) [linear_ordered_field F] : (2 : F) + 2 < 5 := by norm_num1
lemma test7 : nat.prime (2^13 - 1) := by norm_num1
lemma test8 : ¬ nat.prime (2^11 - 1) := by norm_num
lemma test9 (x : ℝ) (h : x = 123 + 456) : x = 579 := by norm_num at h; assumption


#print test1
-- (id
--    ((congr (congr_arg eq (norm_num.add_bit0_bit0 1 1 2 norm_num.one_succ)) (eq.refl 4)).trans
--       (eq_true_intro (eq.refl 4)))).mpr
--   trivial
/-short proof for test1:-/

example : (2 : ℝ) + 2 = 4 := norm_num.add_bit0_bit0 1 1 2 norm_num.one_succ
-- 1 + 1 = 2 from one_succ => 1 * 2 + 1 * 2 = 2 * 2 by add_bit0_bit0 => 2 + 2 = 4 Qed.

example :(2 : ℝ) + 1 = 3 := norm_num.bit0_succ 1

example :(2 : ℝ) + 3 = 5 := norm_num.add_bit0_bit1 1 1 2 norm_num.one_succ

example :(15 : ℝ) + 5 = 20 := 
  norm_num.add_bit1_bit1 7 2 10 (norm_num.adc_bit1_bit0 3 1 5 (norm_num.adc_bit1_one 1 2 norm_num.one_succ))

open norm_num
open tactic
meta def apply_step : tactic unit :=
  do 
    exact add_bit0_bit0,
    trace "hello"

example : (15 : ℝ) + 5 = 20 := by {
  repeat {
    apply add_bit0_bit0 <|> apply add_bit0_bit1 <|> apply add_bit1_bit1 <|> apply add_bit1_bit0
  <|> apply one_succ <|> apply bit0_succ <|> apply adc_bit1_one },
  -- <|> apply first tactic in the list => it's not backtracks
}

#print test2

/-short proof for test2:
12345 = 12345 by range (1, 5)
.2 ≠ .3 <= 2 ≠ 3 <= dec_trivial
-/