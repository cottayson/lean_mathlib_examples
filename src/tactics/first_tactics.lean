import data.matrix.notation
import tactic.suggest
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
  any_goals { apply even.zero },
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
    tactic.trace t,
    match t with
    | `(%%a ∧ %%b) :=
      tactic.exact h
      <|>
      do {
        tactic.trace "go_left",
        ha ← tactic.to_expr ``(and.elim_left %%h),
        destruct_and_helper ha
      } <|>
      do {
        tactic.trace "go_right",
        hb ← tactic.to_expr ``(and.elim_right %%h),
        destruct_and_helper hb
      }
    | _     := do {
      tactic.exact h,
      tactic.trace "Solved with: ", -- trace must be after applying tactic.exact
      tactic.trace t
    }
    end

meta def destruct_and (_name : name) : tactic unit :=
do
  h ← tactic.get_local _name,
  destruct_and_helper h

example (a b c : Prop) (h : a ∧ (b ∨ c)) : b ∨ c :=
begin
  destruct_and `h,
end

lemma abc_c (a b c : Prop) (h : a ∧ b ∧ c) : c :=
begin
  trace_goals,
  trace_state,
  destruct_and `h, -- Unfortunately, we need to quote the name of the hypothesis with a backtick...
end

#print abc_c

namespace my

constant f : ℕ → Prop
axiom f.zero : f 0 ↔ true
axiom f.step (n) : (f n ∧ ¬ f n.succ ∧ f n.succ.succ) ∨ (f n ∧ f n.succ ∧ ¬ f n.succ.succ)

-- axiom f.one_eq_two : f 1 ↔ f 2

axiom prop.A (a : Prop) : (a ↔ true) ∨ (a ↔ false)

axiom not.A : ¬ true ↔ false
axiom not.B : ¬ false ↔ true
lemma not.C (a : Prop) : ¬ ¬ a ↔ a := by {
  have h : (a ↔ true) ∨ (a ↔ false) := prop.A a,
  cases h; rw h,
  { rw [not.A, not.B] },
  { rw [not.B, not.A] },
}
lemma not.B' : ¬ false ↔ true := by {
  -- apply @eq.to_iff (¬ false) true,
  have h : ¬ ¬ true ↔ ¬ false,
    apply eq.to_iff,
    apply congr_arg, -- refine congr rfl _,
    exact not.A.to_eq, -- exact propext not.A, -- ← library_search [not.A],
  rw ←h,
  exact not.C true,
}

axiom or.A (a : Prop) : a ∨ true ↔ true
axiom or.B (a : Prop) : a ∨ false ↔ a
axiom or.C (a b : Prop) : a ∨ b ↔ b ∨ a

axiom and.A (a : Prop) : a ∧ true ↔ a
axiom and.B (a : Prop) : a ∧ false ↔ false
axiom and.C (a b : Prop) : a ∧ b ↔ b ∧ a
lemma and.S (a : Prop) : a ∧ a ↔ a := by { cases prop.A a; rw h, {rw and.A}, {rw and.B} } -- rw [and.A, and.B], -- not works
lemma and.contra (a : Prop) : a ∧ ¬a ↔ false := by {
  cases prop.A a; rw h,
  repeat { rw and.A <|> rw and.B <|> rw or.A <|> rw or.B <|>
     rw imp.S <|> rw imp.T <|> rw imp.F <|> rw not.A <|> rw not.B <|> trivial },
}

lemma iff.A : (true ↔ false) ↔ false := true_iff false
lemma iff.C (a b : Prop) : (a ↔ b) ↔ (b ↔ a) := iff.comm
lemma iff.S (a : Prop) : (a ↔ a) ↔ true := iff_self a
lemma iff.T (a : Prop) : (a ↔ true) ↔ a := sorry
lemma iff.F (a : Prop) : (a ↔ false) ↔ ¬ a := sorry

lemma iff.not_self (a : Prop) : (a ↔ ¬ a) ↔ false := by {
  cases prop.A a; rw h,
  { rw [ not.A, iff.A ], },
  { rw [ not.B, iff.C false, iff.A ], },
}

lemma imp.F (a : Prop) : (false → a) ↔ true := false_implies_iff a
lemma imp.T (a : Prop) : (true → a) ↔ a := true_implies_iff a
lemma imp.S (a : Prop) : (a → a) ↔ true := by {
  cases prop.A a; rw h,
  { rw imp.T, },
  { rw imp.F, },
}

lemma or.D (a b : Prop) : a ∨ b ↔ ¬ (¬ a ∧ ¬ b) := by {
  cases (prop.A a); rw [h, or.C, and.C], {
    rw [ or.A, not.A, and.B, not.B ],
  }, {
    -- simp only [or.C, or.A, or.B, and.C, and.B, and.A, not.A, not.B, prop.A, not.C],
    -- without or.C and.C:
    -- [false_or]: false ∨ b ==> b
    -- [my.not.B]: ¬false ==> true
    -- [true_and]: true ∧ ¬b ==> ¬b
    -- [my.not.C]: ¬¬b ==> b
    -- [iff_self]: b ↔ b ==> true
    -- with or.C and.C:
    -- [my.or.B]: b ∨ false ==> b
    -- [my.not.B]: ¬false ==> true
    -- [my.and.A]: ¬b ∧ true ==> ¬b
    -- [my.not.C]: ¬¬b ==> b
    rw [ or.B, not.B, and.A, not.C ],
  },
}

lemma iff.apply_not (a b : Prop) : (a ↔ b) ↔ (¬ a ↔ ¬ b) := by {
  cases prop.A a; rw h,
  {
    cases prop.A b; rw h_1,
      { rw [ iff.S, iff.S ] },
      { rw [ iff.A, not.A, iff.not_self ] },
  },
  {
    cases prop.A b; rw h_1,
      { rw [ iff.C false, iff.A, not.B, iff.not_self ] },
      { rw [ iff.S, iff.S ] },
  },
}

lemma and.D (a b : Prop) : a ∧ b ↔ ¬ (¬ a ∨ ¬ b) := by {
  set c := ¬ a with hc,
  set d := ¬ b with hd,
  have h₁ : ¬ c ↔ a := by rw [hc, not.C],
  have h₂ : ¬ d ↔ b := by rw [hd, not.C],
  rw [←h₁, ←h₂],
  rw [iff.apply_not, ←or.D, not.C],
}

-- sudoku weak link and strong link
constant weak : Prop → Prop → Prop
constant strong : Prop → Prop → Prop

axiom weak.def (a b : Prop) : weak a b ↔ ¬ (a ∧ b)
axiom strong.def (a b : Prop) : strong a b ↔ ¬ a ∧ b ∨ a ∧ ¬ b
lemma weak.C (a b : Prop) : weak a b ↔ weak b a := by rw [ weak.def, weak.def, and.C ]
lemma strong.C (a b : Prop) : strong a b ↔ strong b a := by rw [ strong.def, strong.def, or.C, and.C, and.C ¬a ]

local attribute [instance] classical.prop_decidable -- for working by_contra h_left

lemma wrong_eliminate_right : ∃ (a b c : Prop), ¬ ((a ∧ c → b ∧ c) → (a → b)) := by {
  existsi true, -- backtracking order from true to false, using binary bits: 0 = true, 1 = false, example [000, 001, 010, ..., 111]
  existsi false,
  existsi false,
  iterate 7 { rw and.A <|> rw and.B <|> rw or.A <|> rw or.B <|>
     rw imp.S <|> rw imp.T <|> rw imp.F <|> rw not.A <|> rw not.B <|> trivial },
  -- solutions of backtracking: [011] = [true, false, false] (one solution)
}

lemma eliminate_right : ∀ (a b c : Prop), (a ∧ c → b ∧ c) → (a ∧ c → b) := by {
  introv,
  cases prop.A c; try {rw h},
  repeat { rw and.A <|> rw and.B <|> rw or.A <|> rw or.B },
  { assume h₂ : a → b, exact h₂ }, -- c ↔ true
  { -- c ↔ false
    rw [ imp.S, imp.T, imp.F ],
    exact true.intro,
  }
}

lemma eliminate_right_backward : ∀ (a b c : Prop), (a ∧ c → b) → (a ∧ c → b ∧ c) := by {
  introv,
  cases prop.A c; try {rw h},
  repeat { rw and.A <|> rw and.B <|> rw or.A <|> rw or.B },
  { assume h₂ : a → b, exact h₂ }, -- c ↔ true
  { -- c ↔ false
    repeat { rw imp.F <|> rw imp.T <|> rw imp.S <|> trivial },
  }
}

-- weak-strong-weak-strong loop ↔ strong-strong-strong-strong
lemma sudoku_simplest_loop (a b c d : Prop) :
    weak a b ∧ strong b c ∧   weak c d ∧ strong d a → 
  strong a b ∧ strong b c ∧ strong c d ∧ strong d a := 
begin
  cases prop.A a; try {rw h, clear h},
  {
    -- if a = 1 then b = 0 by weak a b
    have h₁ : weak true b ↔ (b ↔ false) := by rw [ weak.def, and.C, and.A, iff.F ],
    rw h₁,
    assume h_left,
    rw h_left.1 at *,
    have h₃ : strong d true ↔ (d ↔ false) := by rw [ strong.def, and.A, not.A, and.B, or.B, iff.F ],
    rw h₃ at h_left,
    have b_false := h_left.1,
    have d_false := h_left.2.2.2,
    rw [b_false, d_false, iff.S, and.A, and.C, and.A] at h_left,
    have h₄ : weak c false := by { rw [weak.def, and.B, not.B], trivial },
    rw [(iff.T _).2 h₄, and.A] at h_left,
    have c_true : c ↔ true,
      by_contra h_contra,
      rw [iff.T, ←iff.F] at h_contra,
      rw h_contra at h_left,
      rw strong.def at h_left,
      rw [and.B, and.C, and.B, or.B] at h_left,
      exact h_left,
      -- rw strong.def at h_left,
      -- rw not.B at h_left,
      -- rw [and.C, and.C false] at h_left,
      -- rw [and.A, and.B] at h_left,
    rw c_true,
    rw [strong.C, strong.C true],
    rw ←and.assoc,
    repeat { rw and.S },
    rw [d_false, and.S],
    rw c_true at h_left,
    exact h_left,
    -- rw [strong.def, not.A, and.B, not.B, and.A, or.A, and.C, and.A],
    -- repeat { apply and.intro },
    -- rw [strong.def, not.A, not.B, and.A, and.B, or.A], trivial,
    -- have h₂ : strong b c := h_left.2.1,
    -- rw ←b_false,
    -- exact h₂,
    

  },
  {
    iterate 2 { rw [weak.def] },
    iterate 4 { rw [strong.def] },
    repeat {
      rw not.A <|> rw not.B <|> rw and.A <|> rw and.B <|> rw and.C false
      <|> rw and.C true <|> rw or.C false <|> rw or.A <|> rw or.B,
    },
    rw ←and.assoc,
    rw ←and.assoc,
    rw ←and.assoc,
    apply eliminate_right_backward _ _ d,
    cases prop.A d ; rw h,
    repeat {
      rw not.A <|> rw not.B <|> rw and.A <|> rw and.B <|> rw or.B <|> rw or.C false <|> rw imp.F <|> trivial,
    },
    rename h d_true,
    cases prop.A b; rw h,
    repeat {
      rw not.A <|> rw not.B <|> rw and.A <|> rw and.B <|> rw or.B <|> rw or.C false 
      <|> rw and.C false <|> rw and.C true <|> rw and.S <|> rw imp.F <|> rw imp.S <|> trivial,
    },
    type_check (and.contra c).1, -- c ∧ ¬c → false
    have h₂ : c ∧ ¬c → false := (and.contra c).1,
    apply h₂,
  }
end


example : f 0 := by { rw [f.zero], exact true.intro, }
example : f 1 := by {
  -- simp [f.step, f.zero, f.one_eq_two] {fail_if_unchanged := ff},
  have h₀ := f.step 0,
  rw f.zero at h₀,
  have h_and : ∀ a, true ∧ a ↔ a, {
    assume a,
    rw and.C,
    exact and.A a,
  },
  rw h_and at h₀,
  rw h_and at h₀,
  cases (prop.A (f 1)); rw h, {
    exact true.intro,
  },
  {
    rw h at h₀,
    rw not.B at h₀,
    rw h_and at h₀,
    rw and.C at h₀,
    rw and.B at h₀,
    rw or.B at h₀, -- f 2 must be false for successing proof => (f 2 = false => f 1 = true)
    sorry, -- not provable?
  },
}

example : ¬ f 1 := by {
  have h₀ := f.step 0,
  rw f.zero at h₀,
  have h_and : ∀ a, true ∧ a ↔ a, {
    assume a,
    rw and.C,
    exact and.A a,
  },
  rw h_and at h₀,
  rw h_and at h₀,
  cases (prop.A (f 1)); rw h, {
    rw not.A,
    rw h at h₀,
    rw not.A at h₀,
    rw h_and at h₀,
    rw and.C at h₀,
    rw and.B at h₀,
    rw or.C at h₀,
    rw or.B at h₀,
    sorry,
  },
  {
    rw not.B,
    exact true.intro,
  },
}

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

