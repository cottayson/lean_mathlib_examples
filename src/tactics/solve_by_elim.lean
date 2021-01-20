import tactic.solve_by_elim
import tactic.nth_rewrite
import tactic.show_term
import tactic.suggest

-- solve_by_elim find shortest proof using given lemmas?

open tactic

lemma ex1 (x y z : ℕ) : x + y + z = x + z + y :=
begin
  show_term { nth_rewrite 0 add_assoc, },
  -- nth_rewrite 0 add_assoc,
  -- show_term {solve_by_elim [add_comm, add_assoc, eq.mpr, eq.rec],},
  -- solve_by_elim try to depth first search and it's not optimal and long time search
  sorry,
end

example (n) : n < 1 → n = 0 := nat.sub_eq_zero_of_le

axiom lt_base (n : ℕ) : nat.lt n n.succ
axiom lt_branch (n m : ℕ) : n < m.succ → n < m ∨ n = m


example (n) : n < 2 → n = 0 ∨ n = 1 :=
begin
  assume h,
  have h₂ := (lt_branch n 1) h,
  cases h₂,
  swap,
  right; assumption,
  left,
  -- have h₃ := nat.sub_eq_zero_of_le h₂,
  -- exact h₃,
  show_term {
    solve_by_elim [nat.sub_eq_zero_of_le h₂] {max_depth := 1},
  },
end

example (n) : n < 2 → n = 0 ∨ n = 1 :=
begin
  assume h,
  have h₂ := (lt_branch n 1) h,
  cases h₂,
  swap,
  solve_by_elim [nat.sub_eq_zero_of_le, lt_base, lt_branch, or.inr],
  clear h,
  left,
  have h₃ : n < 1 → n = 0 := nat.sub_eq_zero_of_le,
  show_term {solve_by_elim [nat.sub_eq_zero_of_le, lt_base, lt_branch, or.inr, or.inl],} -- h₃ h₂
  -- nat.sub_eq_zero_of_le not works in solve_by_elim
  -- h₃ h₂
end

example (a b : Prop) : a → b → a :=
begin
  -- solve_by_elim, -- fails
  show_term { intros a b, exact a, },
end

example (a b : Prop) : a → b → a :=
begin
  -- source: tactics/equiv_rw.lean
  -- exact function.const b, -- OK
  -- exact imp_intro, -- OK
  solve_by_elim [function.const, imp_intro] {pre_apply := tactic.intros >> skip},
  -- solve_by_elim {pre_apply := try tactic.intros >> skip},
end

#print ex1

#print pnat

