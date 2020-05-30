-- import tactic
/-
Step 1:
example (p q r : Prop) : p → (q ∧ r) → p ∧ q :=
assume (h₁ : p)(h₂ : q ∧ r),
_

p q r : Prop,
h₁ : p,
h₂ : q ∧ r
⊢ p ∧ q

Step 2:
example (p q r : Prop) : p → (q ∧ r) → p ∧ q :=
assume (h₁ : p)(h₂ : q ∧ r),
have h₃ : q, from and.left h₂,
_

p q r : Prop,
h₁ : p,
h₂ : q ∧ r,
h₃ : q
⊢ p ∧ q

Step 3:
example (p q r : Prop) : p → (q ∧ r) → p ∧ q :=
assume (h₁ : p)(h₂ : q ∧ r),
have h₃ : q, from and.left h₂,
show _, from and.intro _ _

p q r : Prop,
h₁ : p,
h₂ : q ∧ r,
h₃ : q
⊢ p <=> h₁
⊢ q <=> h₃

-/

example (p q r : Prop) : p → (q ∧ r) → p ∧ q :=
assume (h₁ : p)(h₂ : q ∧ r),
have h₃ : q, from and.left h₂,
show p ∧ q, from and.intro h₁ h₃

example (p q r : Prop) : p → (q ∧ r) → p ∧ q :=
assume : p,
assume : (q ∧ r),
have q, from and.left this,
show p ∧ q, from and.intro ‹p› this -- ‹ = \f, › = \frq

/-
example (p q r : Prop) : p → (q ∧ r) → p ∧ q :=
assume (h₁ : p) (h₂ : q ∧ r),
suffices h₃ : q, from _

p q r : Prop,
h₁ : p,
h₂ : q ∧ r,
h₃ : q
⊢ p ∧ q

example (p q r : Prop) : p → (q ∧ r) → p ∧ q :=
assume (h₁ : p) (h₂ : q ∧ r),
suffices h₃ : q, from and.intro h₁ h₃,
_

p q r : Prop,
h₁ : p,
h₂ : q ∧ r
⊢ q <=> h₂.left
-/

example (p q r : Prop) : p → (q ∧ r) → p ∧ q :=
assume (h₁ : p) (h₂ : q ∧ r),
suffices h₃ : q, from and.intro h₁ h₃,
show q, from h₂.left

/- 
Lean also supports calculational environment, which is
introduced with the keyword calc. The syntax is as follows:
calc
  <expr>_0 'op_1' <expr>_1 ':' <proof>_1
     '...' 'op_2' <expr>_2 ':' <proof>_2
     ...
     '...' 'op_n' <expr>_n ':' <proof>_n
-/

variables (a b c d e : ℕ)
variable h1 : a = b
axiom h2 : b = c + 1
variable h3 : c = d
variable h4 : e = 1 + d

/-
Step 1:
theorem T : a = e :=
calc
  a   = b     : _ -- ⊢ a = b
  ... = c + 1 : _ -- ⊢ b = c + 1
  ... = d + 1 : _ -- ⊢ c + 1 = d + 1
  ... = 1 + d : _ -- ⊢ d + 1 = 1 + d
  ... = e     : _ -- ⊢ 1 + d = e

Step 2:
-/

theorem T : a = e :=
calc
  a   = b     : h1 -- ⊢ a = b
  ... = c + 1 : begin exact h2 b c, end -- ⊢ b = c + 1
  ... = d + 1 : congr_arg nat.succ h3 -- ⊢ c + 1 = d + 1
  ... = 1 + d : by exact add_comm d _ -- ⊢ d + 1 = 1 + d, _ <=> (1 : ℕ)
  ... = e     : h4.symm -- ⊢ 1 + d = e

-- congr_arg : ∀ {α β : Type} {a₁ a₂ : α}
--   (f : α → β), a₁ = a₂ → f a₁ = f a₂

-- add_comm : ∀ {α : Type} [_inst_1 : add_comm_semigroup α]
--   (a b : α), a + b = b + a

-- eq.symm : ∀ {α : Type} {a b : α},
--   a = b → b = a
/-
meta def f : ℕ → bool
| 0 :=  bor (f 1) (f 2)
| (nat.succ n) := f n
-/

constant f : nat → bool

-- Lean: invalid definition, it uses untrusted declaration 'f'
axiom f₀ : f 0 = bor (f 1) (f 2)
axiom f_ind : ∀ n, n > 0 → f (n + 1) = f n

-- let f 0 = false => f 1 ∨ f 2 = false => f 1 = false, f 2 = false
-- ∀ n, n > 0 → f (n + 1) = f n => f 3 = f 2 = false, f 4 = f 3 = false, ... , f (n : nat, n > 0) = false = f 0

-- let f 0 = true => f 1 ∨ f 2 = true
-- ∀ n, n > 0 → f (n + 1) = f n => f 2 = f 1 => f 1 ∨ f 1 = true => f 1 = true => f 2 = true => ... => f (n : nat, n > 0) = true = f 0

-- => lemma ∀ n, n > 0 → f n = f 0

set_option trace.simplify.rewrite true

lemma fn_eq_f0 : ∀ n, n > 0 → f n = f 0 :=
begin
  intros n n_gt_0,
  have h : n > 0 → n = 1 ∨ n > 1 := sorry,
  cases (h n_gt_0) with h_n_eq_1 n_gt_1,
  rw h_n_eq_1,
  have h₀ : f 0 = tt ∨ f 0 = ff := sorry,
  cases h₀,
  rw f₀,
  suffices f₂_true : f 2 = tt,
  rw f₂_true,
  -- simp, -- [simplify.rewrite] [bor_tt]: f 1 || tt ==> tt
  rw bor_tt,
  by_contradiction H,
  -- simp at H, -- [simplify.rewrite] [eq_ff_eq_not_eq_tt]: ¬f 1 = tt ==> f 1 = ff
  rw eq_ff_eq_not_eq_tt at H,
  have ind₁ := f_ind 1,
  change 1 > _ → f 2 = f 1 at ind₁,
  have one_gt_zero : 1 > 0 := sorry,
  have f₁_eq_f₂ := ind₁ one_gt_zero, clear ind₁,
  rw f₁_eq_f₂ at f₂_true,
  rw f₂_true at H,
  contradiction,

  all_goals { sorry, },
end

/-
kernel failed to type check declaration 'fn_eq_f0' this is usually due to a buggy tactic or a bug in the builtin elaborator
elaborated type:
  ∀ (n : ℕ), n > 0 → f n = f 0
elaborated value:
  λ (n : ℕ) (n_gt_0 : n > 0), sorry
nested exception message:
invalid definition, it uses untrusted declaration 'f'
-/
-- ************************************************************************************************************************************
-- axiom f₀ : f 0 = bor (f 1) (f 2)
-- axiom f_ind : ∀ n, n > 0 → f (n + 1) = f n

-- let f 0 = false => f 1 ∨ f 2 = false => f 1 = false, f 2 = false
-- ∀ n, n > 0 → f (n + 1) = f n => f 3 = f 2 = false, f 4 = f 3 = false, ... , f (n : nat, n > 0) = false = f 0

-- let f 0 = true => f 1 ∨ f 2 = true
-- ∀ n, n > 0 → f (n + 1) = f n => f 2 = f 1 => f 1 ∨ f 1 = true => f 1 = true => f 2 = true => ... => f (n : nat, n > 0) = true = f 0

-- => lemma ∀ n, n > 0 → f n = f 0
-- ************************************************************************************************************************************

-- ih : n > 0 → f n = f 0
-- ⊢ n.succ > 0 → f n.succ = f 0
lemma induction_lemma_false_case (f₀_false : f 0 = ff) (f₁_false : f 1 = ff) 
  (n : ℕ): (n > 0 → f n = f 0) → n.succ > 0 → f n.succ = f 0 := sorry

lemma fn_eq_f0'' : ∀ n, n > 0 → f n = f 0 :=
begin
  intro n,
  have bool_f₀ : f 0 = ff ∨ f 0 = tt, from sorry,
  cases bool_f₀ with f₀_false f₀_true,
  { -- f₀_false : f 0 = ff
    have H : bor (f 1) (f 2) = ff, {
      rw <-f₀_false,
      apply f₀.symm,
    },
    have bool_lemma : ∀ (a b : bool), a || b = ff = (a = ff ∧ b = ff), {
      intros a b,
      -- simp, -- [bor_eq_false_eq_eq_ff_and_eq_ff]: a || b = ff ==> a = ff ∧ b = ff
      rw bor_eq_false_eq_eq_ff_and_eq_ff,
      -- library_search, -- not return a result, still calculating...
    },
    have h2 := bool_lemma (f 1) (f 2),
    rw h2 at H,
    type_check H.1, -- f 1 = ff
    type_check H.2, -- f 2 = ff
    have f₁_false := H.1, have f₂_false := H.2, clear H h2 bool_lemma,

    induction n with n ih,
    have h := eq.refl (f 0),
    -- have false_imp : ∀ (a : Prop),  false → a, {
    --   intro a,
    --   rw false_implies_iff, trivial,
    -- },
    have zero_ge_zero_is_false : 0 > 0 = false, {
      -- apply _,
      sorry,
    },
    rw zero_ge_zero_is_false,
    intro, exfalso, exact a,
    exact induction_lemma_false_case f₀_false f₁_false n ih,
  },
  { -- f₀_true : f 0 = tt
    sorry,
  },
end

lemma fn_eq_f0' : ∀ n, n > 0 → f n = f 0 :=
begin
  intro n,
  induction n with n ih,
  case nat.zero {
    -- ⊢ 0 > 0 → f 0 = f 0
    simp,
    -- [nat.nat_zero_eq_zero]: 0 ==> 0
    -- [eq_self_iff_true]: f 0 = f 0 ==> true
    -- [implies_true_iff]: 0 > 0 → true ==> true
  },
  case nat.succ {
    -- ⊢ n.succ > 0 → f n.succ = f 0
    have bool_f₀ : f 0 = tt ∨ f 0 = ff, from sorry,
    cases bool_f₀ with f₀_true f₀_false,
    case or.inl {
      rw f₀_true,
      rw f₀_true at ih,
      sorry,
    },
    case or.inr {
      -- rw f₀_false,
      rw f₀_false at ih,
      intro h_nsucc,
      -- have H: f n = ff → f n.succ = ff, sorry,
      have H := f_ind n,
      change n > 0 → f n.succ = f n at H,
      have h_gt_nat : n = 0 ∨ n > 0, sorry,
      cases h_gt_nat,
      case or.inl {
        rw h_gt_nat,
        sorry,
      },
      case or.inr {
        sorry,
      },
    },
  },
end
