import tactic.push_neg
import tactic.suggest

example (a : Prop) : a ∨ true :=
begin
  suggest,
  -- exact or.inr trivial,
  -- exact (or_true a).mpr trivial,
  exact or.intro_right a trivial,
end

example (a : Prop) : ¬(a ↔ ¬a) := (iff_not_self a).1

example (a b : Prop) : a ∧ b → a ∨ b :=
begin
  intro h,
    -- 3 lines below doing nothing
    refine or.imp_left _ _,
    exact a,
    exact id,
  sorry,
end

example : 0 < 2 :=
begin
  refine nat.lt.step _,
  exact nat.lt.base 0,
end

example : 0 < 5 :=
begin
  exact (int.coe_nat_lt_coe_nat_iff 0 5).mp trivial, -- why this works?
end

example (n : nat) : n < n + 2 :=
begin
  -- refine n.lt_add_left 2 n _,
  -- ⊢ n < 2 is not provable
  refine nat.lt.step _,
  -- exact nat.lt.base n, OK
  -- exact nat.lt_succ_self n, OK
  -- refine nat.lt.step _, -- ⊢ n < n is not provable
  -- refine nat.lt_succ_of_lt _, -- same result
  -- refine lt_iff_le_not_le.mpr _, -- ???

  -- refine nat.lt_trans _ _,
  -- exact n, -- ⊢ n < n not provable

  have h : n < n + 1, sorry,
  suggest, -- Try this: exact h
  exact nat.lt.base n,
end

example (n) : n*n ≠ 1 → n ≠ 1 := by {
  contrapose,
  -- refine mt _, -- undo contrapose
  rw [not_not, not_not],
  assume h : n = 1,
  rw [h],
  have h₂ := one_mul 1,
  suggest, -- Try this: exact rfl, but expected h₂
  exact h₂,
}

example {a b c d: nat} (h₁ : a < c) (h₂ : b < d) : max (c + d) (a + b) = (c + d) :=
begin
  suggest 50 [add_lt_add], -- Says: `exact max_eq_left_of_lt (add_lt_add h₁ h₂)`
  exact max_eq_left_of_lt (add_lt_add h₁ h₂),
end

namespace example2

constant lt : ℕ → ℕ → Prop
axiom lt.base {n} : lt n n.succ
axiom lt.base_false {n} : ¬ lt n n
axiom lt.step {n m} : lt n m → lt n m.succ

variables {a b c d : ℕ}

example : lt 0 1 := lt.base
example : lt 0 2 := lt.step lt.base
example : lt 0 3 := lt.step (lt.step lt.base)

example : lt 0 3 := 
begin
  suggest 2, -- Try this: refine lt.step _
  refine lt.step _,
  suggest 2, -- Try this: refine lt.step _
  refine lt.step _,
  suggest 1, -- Try this: refine lt.step _
  suggest 2, -- Try this: exact lt.base
  exact lt.base,
end

example : ¬ lt 1 0 :=
begin
  refine not.intro _,
  intro h,
  have h₂ : ¬ lt 1 1, suggest 22, exact lt.base_false, 
  -- 22 is minimum number which produce exact word
  have contraposed : ∀ (n m : ℕ), ¬ lt n m.succ → ¬ lt n m,
  {
    intros n m hyp,
    suggest [lt.step, lt.base_false, lt.base],
    -- Try this: exact id (λ (a : lt n m), false.rec false h.step.base_false)
    exact id (λ (a : lt n m), false.rec false h.step.base_false),
  },
  suggest, -- Try this: exact contraposed 1 0 h₂ h
  exact contraposed 1 0 h₂ h,
end

lemma lt.not_one_zero : ¬ lt 1 0 :=
begin
  suggest [lt.step, lt.base_false, lt.base],
  exact mt lt.step lt.base_false,
  -- exact classical.not_imp_not.mpr lt.step lt.base_false
end

lemma lt.not_two_one : ¬ lt 2 1 := mt lt.step lt.base_false

example : ¬ lt 2 0 :=
begin
  suggest 100 [lt.step, lt.base_false, lt.base, lt.not_one_zero, lt.not_two_one],
  -- one of found terms: refine mt _ _
  refine mt lt.step _, -- try to fill first hole manually
  suggest 100 [lt.not_one_zero, lt.step, lt.base_false, lt.base],
  -- exact mt lt.step lt.base_false
  -- exact classical.not_imp_not.mpr lt.step lt.base_false
  exact lt.not_two_one,
end

lemma lt.succ_not_less (n : ℕ) : ¬ lt n.succ n :=
begin
  suggest 100 [lt.step, lt.base_false, lt.base, lt.not_one_zero, lt.not_two_one],
  -- Try this: exact mt lt.step lt.base_false
  -- Try this: exact classical.not_imp_not.mpr lt.step lt.base_false
  exact mt lt.step lt.base_false,
end

example : ¬ lt 5 4 :=
begin
  suggest 23, -- Try this: exact lt.succ_not_less 4
  exact lt.succ_not_less 4,
end

example (a : Prop): false → a :=
begin
  suggest 22,
  exact false.elim,
  -- exact false.rec a
  -- exact false.drec (λ (n : false), a)
  -- exact false.elim
  -- exact false.rec_on a
end



example : ¬ lt 0 0 :=
begin
  -- refine imp_false.mp _,
  refine (false_iff (lt 0 0)).mp _,
  refine eq.to_iff _,
  refine ((λ {α : Type} {x₁ x₂ y₁ y₂ : α} (h₁ : x₁ = y₁) (h₂ : x₂ = y₂), (h₁.congr h₂).mp) _ _ _).symm,
  all_goals { sorry },
end

end example2