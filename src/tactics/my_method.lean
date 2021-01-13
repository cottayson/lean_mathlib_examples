import data.nat.modeq -- modular arithmetic
import data.nat.prime -- prime number stuff
import tactic.norm_num -- a tactic for fast computations
import tactic.show_term

namespace inequality_example
-- http://wwwf.imperial.ac.uk/~buzzard/xena/natural_number_game/?world=9&level=1
theorem mul_pos (a b : nat) : a ≠ 0 → b ≠ 0 → a * b ≠ 0 :=
begin
  intros ha hb,
  simp at ha hb,
  -- letσ name this goal state with state_A
  by_cases b = 0,
    { contradiction, },
    { 
      clear h, 
      -- goal state is state_A => wrong way to prove
      sorry,
    },
  /-
    ha : a ≠ 0
    hb : b ≠ 0

    (let a = 0 => a * b = 0 * b = 0 => contradiction with a * b ≠ 0) => a ≠ 0
    analogically for b:
    let's define some function:
      define proof a b = let a = 0 => a * b = 0 * b = 0 => contradiction with a * b ≠ 0
    proof b a => b ≠ 0
    
  -/
end

end inequality_example

namespace hidden

variables (x y z : bool)

constant or : bool -> bool -> bool
constant and : bool -> bool -> bool
constant xor : bool -> bool -> bool
constant imp : bool -> bool -> bool
constant sheffer : bool -> bool -> bool
constant not : bool -> bool

axiom or_true : or tt x = tt
axiom or_false : or ff x = x
axiom and_true : and tt x = x
axiom and_false : and ff x = ff
axiom not_def : not x ≠ x

lemma or_refl  : or  x x = x := by cases x; repeat {rw or_false  <|> rw or_true }
lemma and_refl : and x x = x := by cases x; repeat {rw and_false <|> rw and_true}

lemma or_comm : or x y = or y x :=
begin
  destruct x; intros h₁; rw h₁,
  all_goals { 
    try { rw or_false, },
    try { rw or_true,  },
    destruct y; intros h₂; rw h₂,
  },
  repeat { simp only [or_true, or_false] },
end

lemma and_comm : and x y = and y x := by cases x; cases y; repeat {rw and_false <|> rw and_true}

#check nat.lt.base
#check @nat.lt.step
#check nat.le_succ
#check @nat.less_than_or_equal.refl
#check @nat.less_than_or_equal.step

example : 1 + 1 > 1 := nat.lt.base 1
lemma test : 20 > 10 := by repeat { apply nat.lt.base <|> apply nat.lt.step }
#print test

-- ∀ {p : ℕ → Prop} (a : ℕ), p 0 → (∀ (n : ℕ), (∀ (m : ℕ), m ≤ n → p m) → p n.succ) → p a


lemma test_rewrite (A B : Prop) (h : A = B) : A -> B :=
begin
  have U : A → B, sorry,
  rw h at U,
  have do_nothing : (A → B) → A → B := id,
  apply do_nothing,
  -- apply eq.subst h, works
  -- exact do_nothing, fail
  exact h ▸ id,
end

example (n : nat) : n + 1 = 1 + n :=
begin
  type_check @nat.case_strong_induction_on,
  apply @nat.case_strong_induction_on (λ n, n + 1 = 1 + n),
  { refl },
  intros n h,
  change ∀ m, _ → _ = _ at h,
  have h₂ := h n,
  have h₃ : n ≤ n := @nat.less_than_or_equal.refl n,
  have ih := h₂ h₃,
  clear h₃ h₂ h,
  change n.succ = 1 + n at ih,
  rw ih,
  change n + 1 = _ at ih,
  rw add_assoc,
  rw ih,
end

end hidden

namespace example_logic_tactic


-- split tactic

open nat


variables (a b : ℕ)
example : (∀ k : ℕ, k > 1 → k ∣ a → ¬ (k ∣ b) ) → coprime a b := coprime_of_dvd
example : coprime a b → gcd a b = 1 := coprime.gcd_eq_one
example : (∀ k : ℕ, k > 1 → k ∣ a → ¬ (k ∣ b) ) → gcd a b = 1 := λ h, coprime.gcd_eq_one $ coprime_of_dvd h

example : 5 ≡ 1 [MOD 4] := rfl
example (a b c d m : nat):
  a ≡ b [MOD m] → c ≡ d [MOD m] → a * c ≡ b * d [MOD m] :=
  @modeq.modeq_mul m a b c d


lemma prime_2 : prime 2 := dec_trivial

lemma prime_5 : prime 5 := by norm_num

#print prime_5
-- (id
--    (eq_true_intro
--       (norm_num.is_prime_helper 5 (norm_num.lt_one_bit1 2 (bit0_pos zero_lt_one))
--          (norm_num.min_fac_helper_5 2 1 9
--             (norm_num.mul_bit1_bit1 1 1 1 2 4 (one_mul 1) norm_num.one_succ
--                (norm_num.add_bit0_bit0 1 1 2 norm_num.one_succ))
--             (norm_num.lt_bit1_bit1 2 4 (norm_num.lt_bit0_bit0 1 2 (norm_num.lt_one_bit0 1 (le_refl 1))))
--             (norm_num.min_fac_helper_0 2 (bit0_pos zero_lt_one)))))).mpr
--   trivial

#eval factors 1023 -- [3, 11, 31]
#eval (factors 1024).length -- 10

open tactic 
meta def show_term' :=
  do
    g :: rest ← get_goals,
    trace get_goals


example {P Q R : Prop} (h₁ : Q → P) (h₂ : R) (h₃ : R → Q) : P ∧ R :=
by show_term { tactic.tauto }

lemma test_split (A B : Prop) : A ∧ B → B ∧ A := by {
  intros h,
  split,
  show_term',
  all_goals { sorry },
}

meta def split' : tactic 

meta def split_unit : tactic unit := 
  concat_tags split'






end example_logic_tactic

