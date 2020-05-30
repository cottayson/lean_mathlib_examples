set_option trace.simplify.rewrite true

namespace and_intro_example
-- {a b : Prop} : implicit arguments
-- (a b : Prop) : explicit arguments
theorem swap_conj₁ {a b : Prop} (h : a ∧ b) : b ∧ a := ⟨h.right, h.left⟩
theorem swap_conj₂ {a b : Prop} (h : a ∧ b) : b ∧ a := and.intro h.right h.left
#print notation ∘ 

constants a b : Prop
constants (h : a ∧ b)
-- #check ⟨h.left, h.right⟩ -- invalid constructor ⟨...⟩, expected type must be known
#check and.intro h.left h.right -- ⟨h.left, h.right⟩ : a ∧ b
#check and.intro h.right h.left -- ⟨h.right, h.left⟩ : b ∧ a
end and_intro_example

def even (k : nat) : bool := k % 2 = 0

lemma even.zero : even 0 := sorry
lemma even.add_two : ∀ k : nat, even k → even (k + 2) := sorry
lemma even.next_not_even : ∀ k : nat, even k → ¬ even (k + 1) := sorry

lemma seven_is_not_even: ¬ even 7 :=
begin
  -- automatic bakward proof
  try { apply even.next_not_even }, -- ⊢ ↥(even 6)
  repeat { apply even.add_two }, -- ⊢ ↥(even 0)
  exact even.zero, -- goals accomplished
end

lemma seven_is_not_even₂: ¬ even 7 :=
begin
  -- automatic forward proof
  simp only [even.zero, even.add_two, even.next_not_even, not_false_iff],
  -- [even.zero]: ↥(even 0) ==> true
  -- [even.next_not_even]: ↥(even 1) ==> false
  -- [even.zero]: ↥(even 0) ==> true
  -- [even.add_two]: ↥(even 2) ==> true
  -- [even.next_not_even]: ↥(even 3) ==> false
  -- [even.zero]: ↥(even 0) ==> true
  -- [even.next_not_even]: ↥(even 1) ==> false
  -- [even.zero]: ↥(even 0) ==> true
  -- [even.add_two]: ↥(even 2) ==> true
  -- [even.add_two]: ↥(even 4) ==> true
  -- [even.next_not_even]: ↥(even 5) ==> false
  -- [even.zero]: ↥(even 0) ==> true
  -- [even.next_not_even]: ↥(even 1) ==> false
  -- [even.zero]: ↥(even 0) ==> true
  -- [even.add_two]: ↥(even 2) ==> true
  -- [even.next_not_even]: ↥(even 3) ==> false
  -- [even.zero]: ↥(even 0) ==> true
  -- [even.next_not_even]: ↥(even 1) ==> false
  -- [even.zero]: ↥(even 0) ==> true
  -- [even.add_two]: ↥(even 2) ==> true
  -- [even.add_two]: ↥(even 4) ==> true
  -- [even.add_two]: ↥(even 6) ==> true
  -- [even.next_not_even]: ↥(even 7) ==> false
  -- [not_false_iff]: ¬false ==> true
end

lemma repeat_example :
  even 4 ∧ even 7 ∧ even 3 ∧ even 0 :=
begin
  repeat { apply and.intro },
  repeat { apply even.add_two },
  -- 4 goals ⊢ ↥(even 0) ⊢ ↥(even 1) ⊢ ↥(even 1) ⊢ ↥(even 0)
  all_goals { sorry, },
end

lemma repeat_orelse_example :
  even 4 ∧ even 7 ∧ even 3 ∧ even 0 :=
begin
  repeat { apply and.intro },
  repeat {
    apply even.add_two <|> apply even.zero,
  },
  -- 2 goals ⊢ ↥(even 1) ⊢ ↥(even 1)
  all_goals { sorry, },
end

lemma iterate_orelse_example :
  even 4 ∧ even 7 ∧ even 3 ∧ even 0 :=
begin
  repeat { apply and.intro },
  iterate {
    apply even.add_two <|> apply even.zero,
  },
  -- 3 goals ⊢ ↥(even 1) ⊢ ↥(even 3) ⊢ ↥(even 0)
  all_goals { sorry, },
end

-- ...

lemma repeat_not_example :
  ¬ even 1 :=
begin
  apply not.intro, -- <=> do nothing
  apply not.intro,
  apply not.intro,
  apply not.intro,
  -- ... 
  sorry,
end

-- tactic intro_and_even

-- meta def intro_and_even : tactic unit :=
-- do
--   tactic.repeat (tactic.applyc ``and.intro),
--   tactic.any_goals (tactic.solve1 (tactic.repeat
--     (tactic.applyc ``even.add_two <|> tactic.applyc ``even.zero)))

-- term
--   λ (_x : unit),
--     ((tactic.applyc (name.mk_string "add_two" (name.mk_string "even" name.anonymous))) <|>
--        (tactic.applyc (name.mk_string "zero" (name.mk_string "even" name.anonymous)))).repeat.solve1.any_goals
-- has type
--   unit → tactic (list (option unit))
-- but is expected to have type
--   unit → tactic unit

meta def hello : tactic unit :=
do
  tactic.trace ("Hello, " ++ "tactic")

meta def trace_goals : tactic unit :=
do
  tactic.trace "local context:",
  ctx ← tactic.local_context,
  tactic.trace ctx,
  tactic.trace "\ntarget:",
  P ← tactic.target,
  tactic.trace P,
  tactic.trace "\nall missing proofs:",
  Hs ← tactic.get_goals,
  tactic.trace Hs,
  τs ← list.mmap tactic.infer_type Hs,
  tactic.trace τs

/- Types of metafunctions:
  tactic.trace : α → tactic unit
  tactic.local_context : tactic (list expr)
  tactic.target : tactic expr
  tactic.get_goals : tactic (list expr)
  tactic.infer_type : expr → tactic expr
  list.mmap {α β : Type} : (α → m β) → list α → m (list β)
-/

-- tactic.assumption

lemma even_14 :
  even 14 :=
begin
  hello,
  have hfirst := even.zero,
  -- have hsecond := even.add_two 0 hfirst,
  trace_goals,
  -- simp at hsecond, -- [zero_add]: 0 + 2 ==> 2
  assumption,
end

-- Expressions

run_cmd do
  let e : expr := `(list.map (λn : ℕ, n + 1) [1, 2, 3]),
  tactic.trace e -- list.map (λ (n : ℕ), n + 1) [1, 2, 3]

run_cmd do
  let e1 : pexpr := ``(list.map (λn, n + 1) [1, 2, 3]),
  let e2 : pexpr := ``(list.map _ [1, 2, 3]),
  tactic.trace e1,
  tactic.trace e2

run_cmd tactic.trace `and.intro
run_cmd tactic.trace `intro_and_even
run_cmd tactic.trace `seattle.washington

run_cmd tactic.trace ``and.intro
run_cmd tactic.trace ``intro_and_even
-- run_cmd tactic.trace ``seattle.washington -- fails

-- get number of declarations
run_cmd do
  env ← tactic.get_env,
  tactic.trace (environment.fold env 0 (λdecl n, n + 1))

meta def destruct_and_helper : expr → tactic unit
| h :=
  do
    t ← tactic.infer_type h,
    match t with
    | `(%%a ∧ %%b) :=
      tactic.exact h
      <|>
      do {
        ha ← tactic.to_expr ``(and.elim_left %%h),
        destruct_and_helper ha
      } <|>
      do {
        hb ← tactic.to_expr ``(and.elim_right %%h),
        destruct_and_helper hb
      }
    | _     := tactic.exact h
    end

meta def destruct_and (_name : name) : tactic unit :=
do
  h ← tactic.get_local _name,
  destruct_and_helper h

lemma abc_a (a b c : Prop) (h : a ∧ b ∧ c) : a :=
begin
  trace_goals,
  trace_state,
  destruct_and `h, -- Unfortunately, we need to quote the name of the hypothesis with a backtick...
end

namespace my
end my
-- intro tactic:

-- TEST intro tactic



-- contrapose tactic:

-- TEST contrapose tactic:


-- contradiction tactic:
/--
The contradiction tactic attempts to find in the current local context a hypothesis that is equivalent to an empty inductive type (e.g. `false`), a hypothesis of the form `c_1 ... = c_2 ...` where `c_1` and `c_2` are distinct constructors, or two contradictory hypotheses.
-/


-- TEST contradiction tactic:



-- rewrite tactic:

-- TEST rewrite tactic:

