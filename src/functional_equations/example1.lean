import tactic.find

#find (ff = _)

constants 
(f : nat → nat)
(f₀ : f 0 = 0)
(f₁ : f 1 = 1)
(f₂ : f 2 = 1)
(f_next : ∀ n : nat, f (n + 3) = f (n + 2) + f (n + 1) ∨ f (n + 3) = f (n + 1) + f n)

namespace evaluation

meta def hasElement : list nat → nat → bool
| [] _ := ff
| (x :: xs) e := if e = x then tt else hasElement xs e

#eval hasElement [1,2,3] 1 -- tt
#eval hasElement [1,2,3] 4 -- ff

#reduce hasElement [1,2,3] 1 -- tt

-- def union (lx ly : list nat) : list nat :=
-- match lx, ly with
-- | [], listy := listy
-- | listx, [] := listx
-- | (x :: xs), listy := if hasElem listy x then union xs listy else union xs (x :: listy)
-- end
-- @[reducible]
meta def union : list nat → list nat → list nat
| [] ys := ys
| (x :: xs) ys := if hasElement ys x then union xs ys else union xs (x :: ys)

#print union._main

#eval union [1,2,3,4,5] [1] -- [5, 4, 3, 2, 1]
#eval union [1,2,3] [4,5,6] -- [3, 2, 1, 4, 5, 6]

#eval union [1,2,3] [] -- [3, 2, 1]
#reduce union [1,2,3] [] -- [union._main] [2, 3] [1], why reduce doesn't return the same result as eval?

end evaluation

namespace lemmas

set_option trace.simplify.rewrite true

constant hasElement : list nat → nat → bool

namespace hasElement

axiom base (n : nat) : hasElement [] n = ff
axiom step (x : nat) (xs : list nat) : hasElement (x :: xs) x = tt
axiom step_not_eq (x y : nat) (xs : list nat) (h : x ≠ y) :
  hasElement (x :: xs) y = hasElement xs y

lemma empty_not_contains_any (x : nat) : ¬ hasElement [] x = tt :=
begin
  rw hasElement.base _,
  -- change ¬ false = true, -- fail
  -- rw not.elim, -- fail
  -- rw not_false_iff, -- fail
  apply not.intro,
  exact bool.ff_ne_tt,
end

lemma single {x : nat} : hasElement [x] x := 
  hasElement.step x []

lemma two (x y : nat) : hasElement [x, y] y :=
begin
  -- if x = y => tt
  -- if x ≠ y => hasElement [y] y => tt [by single]
  by_cases (x = y),
  {
    rw ←h,
    exact hasElement.step x [x],
  },
  {
    change x ≠ y at h,
    -- rw hasElement.step_not_eq _ _ _ h, -- OK
    rw hasElement.step_not_eq,
    { exact @single y },
    { exact h },
  },
end

example : ¬ hasElement [0] 1 :=
begin
  rw hasElement.step_not_eq,
  apply empty_not_contains_any,
  exact zero_ne_one,
end

#print two


end hasElement

variables {x : ℕ} {xs ys : list ℕ}

constant union : list nat → list nat → list nat

axiom union_base (xs : list nat) :
  union [] xs = xs

axiom union_step₁ (h : hasElement ys x) :
  union (x :: xs) ys = union xs ys

axiom union_step₂ (h : hasElement ys x → false) :
  union (x :: xs) ys = union xs (x :: ys)


lemma union_single : union [x] [x] = [x] :=
begin
  have h₁ :                    union []  [x] = [x]          := union_base [x],
  have h₂ : hasElement [x] x → union [x] [x] = union [] [x] := union_step₁,
  have h₃ :                    union [x] [x] = union [] [x] := h₂ hasElement.single,
  apply eq.trans h₃,
  exact h₁,
end

lemma union_single' : union [x] [x] = [x] :=
begin
  rw union_step₁,
  rw union_base,
  apply hasElement.single,
end

#print notation >>=

open tactic
meta def trace_all : tactic unit :=
   do n ← num_goals
    , trace "num_goals ="
    , trace n
    , trace_state
    , trace "---------------------------------------------"
    , trace_result

lemma union_single'' : union [x] [x] = [x] := by { 
  apply eq.trans (union_step₁ hasElement.single),
  trace_all,
  sorry
}

meta def test_tactic : tactic unit :=
do 
  define `x (expr.const `nat [])
, trace "-- after assert --"
, trace_state
, n ← get_local `n
, trace (infer_type n)

example (n : nat) : n = n := by { test_tactic, sorry }

example : (1 = 2) → (2 = 3) → (3 = 1) := begin
  assume h1 h2,
  apply eq.symm,
  apply eq.subst h2,
  apply eq.subst h1,
  apply eq.refl,
  trace_result,
  trace_call_stack,
end

example (a : nat) (b : bool) (c : int) : true := by {
  do 
    a ← get_local `a
  , b ← get_local `b
  , c ← get_local `c
  , infer_type a >>= trace
  , infer_type b >>= trace
  , infer_type c >>= trace
  , interactive.sorry
}

set_option trace.app_builder true
-- set_option pp.all true

example (a b c : ℕ) : true := by {
  do
    a ← get_local `a
  , x ← mk_app `nat.succ [a] -- x : expr
  , r ← to_expr ```(%%x + b * c + (λ n, n) 100) -- to_expr : pexpr → tactic expr
  , trace r -- a.succ + b * c + (λ (n : ℕ), n) 100
  , infer_type r >>= trace -- ℕ
  , interactive.trivial -- or exact_dec_trivial
}


example (a b c : nat) (H1 : a = b) (H2 : b = c) : a = c :=
by do
  --  refine ```(eq.trans H1 _),
   interactive.refine ```(eq.trans H1 _),
   trace_state,
   assumption

end lemmas



meta def solve (n : nat) (f : nat → nat) :=
match n, f with
| 0, f := 0
| _, _ := 1
end

-- solve n = [f 0, f 1, f 2, ... f (n-1)]
-- solve 0 = [[]]
-- solve 1 = [[0]]
-- solve 2 = [[0], [1]]
-- solve 3 = [[0], [1], [1]]
-- solve 4 = [[0], [1], [1], [1, 2]]
-- solve 5 = [[0], [1], [1], [1, 2], X], 
--    where X = (1 + [1, 2]) ∪ (1 + 1) = [2, 3] ∪ [2] = [2, 3]

#print add_lt_add_of_le_of_lt -- a ≤ b → c < d → a + c < b + d

#print add_pos_of_nonneg_of_pos -- 0 ≤ a → 0 < b → 0 < a + b
-- (ha : 0 ≤ a) (hb : 0 < b),
  -- zero_add 0 ▸ add_lt_add_of_le_of_lt ha hb

#print notation ▸ -- eq.subst #1 #0
#print notation + -- has_add.add #1 #0
#print eq.subst