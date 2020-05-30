import data.nat.prime
import data.list
-- import data.bool

set_option trace.simplify.rewrite true
set_option trace.simplify true
set_option trace.simplify.failure false
set_option trace.simplify.rewrite_failure false


namespace first
constants a b : ℤ
constant f : ℤ → ℤ
constant g : ℤ → ℤ → ℤ

#check λ x : ℤ, g (f (g a x)) (g x _)
-- λ (x : ℤ), g (f (g a x)) (g x ?M_1) : ℤ → ℤ
#check λx, g (f (g a x)) (g x b)
-- λ x <=> λx
end first

namespace trools
constant trool : Type

-- @[pattern]
constants trool.true trool.false trool.maybe : trool

-- def trool_to_bool (x: trool) :=
-- match x with
-- | trool.true := tt
-- | trool.false := ff
-- end

-- def trool_to_bool: trool → bool
-- | trool.true := tt
-- | trool.false := ff
-- | _ := ff

-- def prime (p : ℕ) := 2 ≤ p ∧ ∀ m ∣ p, m = 1 ∨ m = p
def or (a b : trool) := (a = trool.true) ∨ (b = trool.true)

-- lemma or_self (a : trool) : or a a = trool_to_bool a :=
-- begin
--   simp [or],
--   sorry,
-- end
end trools

namespace axiom_examples
constants a b : ℤ
-- lemma a_less_b : a < b := sorry 
-- <=>
axiom a_less_b : a < b
axiom symm_lt (x y : ℤ): x < y → y > x
axiom not_eq_imp_lt (x y : ℤ): x ≠ y → x < y ∨ x > y

example : b > a :=
begin
  have s := symm_lt _ _ a_less_b,
  exact s,
end

lemma p_q_not (P Q: Prop) : P = Q → P ∧ ¬ Q → false := 
begin
  intro pq,
  rw ← pq,
  intro h,
  simp at h,
  exact h,
end

example (x: nat): x = x := 
begin
  have h1: 1 = 1,{refl,},
  have h2: 2 = 2 := rfl,
  -- have h3 := h1 ∧ h2, -- wrong
  have h3 := and.intro h1 h2, -- right
  refl,
end

constants P Q : Type
-- lemma p_q_not (p : P)(q : Q) : p = q → p ∧ ¬ q → false := sorry


lemma example_forward_proof (p : P) : p = p :=
begin
  -- simp, -- [simplify.rewrite] [eq_self_iff_true]: p = p ==> true
  -- refl,
  -- apply eq_self_iff_true p,
  have h := eq_self_iff_true p,
  have h2 := propext h,
  have h3 := h2.mpr,
  apply h3, -- some backward proof
  trivial,
end
#print example_forward_proof
-- λ (p : P), (id (propext (eq_self_iff_true p))).mpr trivial

example (expr : Prop): (expr ∨ expr) → true :=
begin
  simp,
-- 0. [simplify.rewrite] [or_self]: expr ∨ expr ==> expr
-- 0. [simplify.rewrite] [forall_true_iff]: expr → true ==> true
  -- rw or_self,
  -- exact expr,
end


example (x y : ℤ): ¬ (x = y) ∧ ¬ (x > y) → (y > x) :=
begin
  assume f : ¬x = y ∧ ¬x > y,
  apply symm_lt,
  -- exact a_less_b, -- not works
  have f₂ : _ ∧ _ := f, -- example pattern matching
  clear f₂,
  have h₂ : ¬ (x = y) → x ≠ y, from begin
                                      simp,
                                    end,
  have f1 := f.1,
  have f2 := f.2,
  clear f,
  have not_eq_xy : x ≠ y := h₂ f1,
  have h₃ : x < y ∨ x > y := not_eq_imp_lt _ _ not_eq_xy,
  cases h₃ with first second,
  {
    -- first : x < y
    -- i think this one command `exact first` must be solution
    exact first,
  }, 
  {
    -- contradiction,
    exfalso,
    -- have t₁ := p_q_not second f2,
    -- have h₅ := p_q_not _ _,
    have u := and.intro second f2,
    simp [second] at u,
    exact u,
  },
end 


end axiom_examples

namespace backward_proofs
/-
Forward proof:
From a and a → b, we have b. (Goal unchanged)
From b and b → c, we have c, as desired.
* A forward proof only manipulates theorems, not goals.

Backward proof:
To prove c, by b → c it suffices to prove b. (Goal changed from ⊢ c to ⊢ b)
To prove b, by a → b it suffices to prove a. (Goal changed from ⊢ b to ⊢ a)
To prove a, we use a.
* A Backward proof start from the goal and work backwards towards the already proved lemmas.
-/

-- Example of forward proof:
lemma fst_of_two_props :
  ∀ a b : Prop, a → b → a :=
begin -- ⊢ ∀ (a b : Prop), a → b → a
  intros a b,
  -- have h1 := ,
  sorry,
end

-- Example of backward proof:
lemma fst_of_two_props' :
  ∀ a b : Prop, a → b → a :=
begin -- ⊢ ∀ (a b : Prop), a → b → a
  intros a b, -- ⊢ a → b → a (Goal changed)
  intros ha hb, -- ⊢ a (Goal changed)
  apply ha, -- goals accomplished (Goal changed)
end

lemma and_swap :
  ∀ a b : Prop, a ∧ b → b ∧ a :=
begin
  intros a b hab,
  apply and.intro,
  -- { exact hab.2 },
  -- { exact hab.1 },
  { exact and.elim_right hab },
  { exact and.elim_left hab },
end

def double (n : ℕ) := n + n

lemma nat_exists_double_iden :
  ∃ n : ℕ, double n = n :=
begin
  apply exists.intro 0,
  refl,
end

lemma double_prop : ∀ n : ℕ, n ≠ 1 → double n ≠ n + 1 :=
begin
  type_check double.equations._eqn_1, -- ∀ (n : ℕ), double n = n + n
  intros,
  apply not.intro,
  induction n with x hx,
  simp [double],
  have a2 : x ≠ 0, from sorry,
  dsimp only [double],
  simp,
  -- simp at hx ⊢, -- example how to simplify goal and hypothesis simultaniously
  simp only [a],
  trivial,
end

#print double_prop

end backward_proofs

namespace lemma_statements

set_option trace.simplify.rewrite_failure true

lemma my_add_comm (m n : ℕ) :
  nat.add m n = nat.add n m :=
begin
  simp,
  simp only [backward_proofs.double_prop, nat.add_comm],  --
  -- output:
  -- perm rejected: n + m !< m + n
  -- [simplify.rewrite] [nat.add_comm]: n + m ==> m + n

  -- simp works only with second part of equation n + m = m + n:
  -- n + m = (m + n) ==> n + m = (n + m) ==> true
  -- 1. because theorem nat.add_comm is ∀ (m n : ℕ), m + n = n + m [it's wrong]
  -- 2. 
  -- maybe simp use lecsicographical order? 
end

#print nat.add_comm

lemma and_swap (a b : Prop) :
  a ∧ b → b ∧ a :=
begin
  intro hab,
  apply and.intro,
  -- {
        -- apply and.elim_right,
        -- exact hab,
  -- }
  -- <=>
  -- apply and.elim_right hab, <=>
  exact hab.2,
  exact hab.1,
end

/-
  3.1 Structured Proofs
-/

lemma fst_of_two_props'' :
  ∀ a b : Prop, a → b → a :=
assume a b : Prop,
assume (ha : a)(hb : b),
show a, from ha

lemma snd_of_two_props'' :
  ∀ a b : Prop, a → b → b :=
assume a b : Prop,
assume (ha : a)(hb : b),
show _, from hb -- placeholder _ is important thing

lemma prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c :=
assume ha : a,
have hb : b := hab ha,
have hc : c := hbc hb,
show c, from hc

#print fst_of_two_props''
-- λ (a b : Prop) (ha : a) (hb : b), show a, from ha
#print snd_of_two_props''
-- λ (a b : Prop) (ha : a) (hb : b), show b, from hb
#print prop_comp
-- λ (a b c : Prop) (hab : a → b) (hbc : b → c) (ha : a),
--   have hb : b, from hab ha,
--   have hc : c, from hbc hb,
--   show c, from hc


/-
  3.3 Forward Reasoning about Connectives and Quantifiers
-/

-- lemma forall.one_point {α : Type} (t : α) (p : α → Prop) :
--   (∀x, x = t → p x) ↔ p t :=
-- iff.intro
--   (assume hall : ∀x, x = t → p x,
--     show p t, from
--      begin
--        apply hall t,
--        refl
--      end)
--   (assume hp : p t,
--     fix x,
--     assume heq : x = t,
--     show p x, from
--     begin
--       rewrite heq,
--       exact hp
--     end)

lemma forall.one_point' {α : Type} (t : α) (p : α → Prop) :
  (∀x, x = t → p x) ↔ p t :=
iff.intro
  (assume hall: ∀ x, x = t → p x,
   show p t, from sorry)
  (sorry)

lemma beast_666 (beast : ℕ) :
  (∀n, n = 666 → beast ≥ n) ↔ beast ≥ 666 :=
forall.one_point' _ _
-- λ (beast : ℕ), forall.one_point' 666 (λ (n : ℕ), beast ≥ n)

#print beast_666

/-
  3.4 Calculational Proofs
-/
-- Calculational proof example:
lemma two_mul_example (m n : nat) :
  2 * m + n = m + n + m :=
calc  2 * m + n
    = (m + m) + n : by rewrite two_mul
    ... = m + n + m : by cc

-- Forward proof example:
lemma two_mul_example₂ (m n : nat) :
  2 * m + n = m + n + m :=
have h₁ : 2 * m + n = (m + m) + n :=
  by rewrite two_mul,
have h₂ : (m + m) + n = m + n + m :=
  by cc,
show _, from
  eq.trans h₁ h₂

end lemma_statements

namespace proofs_by_induction

constant add : ℕ → ℕ → ℕ

axiom add_zero (m : ℕ): add m 0 = m
axiom add_succ (m n : ℕ): add n (nat.succ n) = nat.succ (add m n)

-- lemma add_zero (n : ℕ)

end proofs_by_induction

namespace induction_by_pattern_matching

def reverse {α : Type} : list α → list α
| []       := []
| (x :: xs) := reverse xs ++ [x]

-- The induction step is:
-- ih : ∀xs, reverse (reverse xs) = xs ⊢ reverse (reverse xs ++ [x]) = x :: xs

/-
We need a way to "distribute" the outer reverse over ++ to obtain a term
matches the induction hypothesis's left-hand side. The trick is to prove
and use the following lemma:
-/

-- Step 1:
-- lemma reverse_append {α : Type} :
--   ∀xs ys : list α, reverse (xs ++ ys) = reverse ys ++ reverse xs
-- | [] ys := sorry
-- | (x :: xs) ys := sorry

-- Step 2:

-- failed to prove recursive application is decreasing, well founded relation
lemma reverse_append_wrong {α : Type} :
  ∀xs ys : list α, reverse (xs ++ ys) = reverse ys ++ reverse xs
| [] ys := begin
  -- rw reverse,
  -- simp,
  rw reverse_append_wrong,
end
| (x :: xs) ys := begin
  simp [reverse, reverse_append_wrong xs],
end

-- OK
lemma reverse_append {α : Type} :
  ∀xs ys : list α, reverse (xs ++ ys) = reverse ys ++ reverse xs
| [] ys := begin
  rw reverse,
  simp,
  -- rw reverse_append,
end
| (x :: xs) ys := begin
  simp [reverse, reverse_append xs],
end

lemma reverse_append₂ {α : Type} (xs ys : list α) :
  reverse (xs ++ ys) = reverse ys ++ reverse xs :=
begin
  induction xs with xs list_h ih,
  case nil {
    simp [reverse],
  },
  case cons {
    simp [reverse, ih],
  },
end

set_option trace.simp_lemmas false

lemma reverse_reverse {α : Type} :
  ∀xs : list α, reverse (reverse xs) = xs
| [] := rfl
| (x :: xs) := begin
  -- rw reverse_reverse, -- failed to prove recursive application is decreasing
  rw reverse,
  rw reverse_append,
  rw reverse_reverse,
  rw reverse.equations._eqn_2,
  rw reverse.equations._eqn_1,
  rw list.nil_append,
  rw list.cons_append,
  rw list.nil_append,
  -- rw reverse,
  -- simp [reverse],
  -- Trace output of simplify.rewrite:
  -- 1. [reverse.equations._eqn_2]: reverse [x] ==> reverse list.nil ++ [x]
  -- 2. [reverse.equations._eqn_1]: reverse list.nil ==> list.nil
  -- 3. [list.nil_append]: list.nil ++ [x] ==> [x]
  -- 4. [list.cons_append]: [x] ++ xs ==> x :: (list.nil ++ xs)
  -- 5. [list.nil_append]: list.nil ++ xs ==> xs
  -- 6. [eq_self_iff_true]: x = x ==> true
  -- 7. [eq_self_iff_true]: xs = xs ==> true
  -- 8. [and_self]: true ∧ true ==> true
end

lemma reverse_reverse₂ {α : Type} :
  ∀xs : list α, reverse (reverse xs) = xs
| [] := rfl
| (x :: xs) := by simp [reverse, reverse_append, reverse_reverse₂ xs]



end induction_by_pattern_matching
namespace inductive_types

namespace hidden
inductive nat : Type
| zero : nat
| succ : nat → nat
end hidden
-- <=>
namespace hidden2
constant nat : Type
constant nat.zero : nat
constant nat.succ : nat → nat
end hidden2
-- + some properties about nat.zero and nat.succ, which is why we use the "inductive" commmand

set_option trace.debug.dsimplify true
-- set_option trace.simplify false
set_option trace.simplify.context false
set_option trace.simplify.congruence false
set_option trace.simplify.canonize false
set_option trace.simplify.rewrite true

lemma succ_neq_self (n : ℕ) :
  nat.succ n ≠ n :=
begin
  induction n with n ih,
  {
    -- [nat.nat_zero_eq_zero]: 0 ==> 0
    -- [ne.def]: 1 ≠ 0 ==> ¬1 = 0
    simp,
  }, 
  {
    rewrite ne.def,
    simp only [ih, ne.def, not_false_iff],
  },
  -- [ne.def]: n_n.succ.succ ≠ n_n.succ ==> ¬n_n.succ.succ = n_n.succ
-- 2. [simplify.rewrite] [n_ih]: n_n.succ = n_n ==> false
-- [simplify] eq: not
-- 1. [simplify.rewrite] [not_false_iff]: ¬false ==> true
end

end inductive_types