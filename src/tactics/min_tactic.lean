universe u

namespace hidden

definition min {α : Type u} [decidable_linear_order α] (a b : α) : α := if a ≤ b then a else b
definition max {α : Type u} [decidable_linear_order α] (a b : α) : α := if a ≤ b then b else a
definition abs {α : Type u} [decidable_linear_ordered_add_comm_group α] (a : α) : α := max a (-a)

section
open decidable tactic
variables {α : Type u} [decidable_linear_order α]

private meta def min_tac_step : tactic unit :=
solve1 $ intros
>> `[unfold min max]
>> try `[simp [*, if_pos, if_neg]]
>> try `[apply le_refl]
>> try `[apply le_of_not_le, assumption]

meta def tactic.interactive.min_tac (a b : interactive.parse lean.parser.pexpr) : tactic unit :=
interactive.by_cases (none, ``(%%a ≤ %%b)); min_tac_step

lemma min_le_left (a b : α) : min a b ≤ a :=
by min_tac a b

#print min_le_left -- very long proof

set_option trace.simplify.rewrite true

lemma min_le_left' (a b : α) : min a b ≤ a :=
begin
  -- unfold min max,
  rw min.equations._eqn_1,
  by_cases (a ≤ b),
  
  type_check @if_pos,
  type_check @if_neg,
  rw if_pos h,
  rw if_neg h,
  apply le_of_not_le,
  exact h,
end

#print min_le_left'

lemma min_le_right (a b : α) : min a b ≤ b :=
by min_tac a b

lemma le_min {a b c : α} (h₁ : c ≤ a) (h₂ : c ≤ b) : c ≤ min a b :=
by min_tac a b

lemma le_max_left (a b : α) : a ≤ max a b :=
by min_tac a b

lemma le_max_right (a b : α) : b ≤ max a b :=
by min_tac a b

lemma max_le {a b c : α} (h₁ : a ≤ c) (h₂ : b ≤ c) : max a b ≤ c :=
by min_tac a b

lemma eq_min {a b c : α} (h₁ : c ≤ a) (h₂ : c ≤ b) (h₃ : ∀{d}, d ≤ a → d ≤ b → d ≤ c) :  c = min a b :=
le_antisymm (le_min h₁ h₂) (h₃ (min_le_left a b) (min_le_right a b))

lemma min_comm (a b : α) : min a b = min b a :=
eq_min (min_le_right a b) (min_le_left a b) (λ c h₁ h₂, le_min h₂ h₁)

lemma min_assoc (a b c : α) : min (min a b) c = min a (min b c) :=
begin
  apply eq_min,
  { apply le_trans, apply min_le_left, apply min_le_left },
  { apply le_min, apply le_trans, apply min_le_left, apply min_le_right, apply min_le_right },
  { intros d h₁ h₂, apply le_min, apply le_min h₁, apply le_trans h₂, apply min_le_left,
    apply le_trans h₂, apply min_le_right }
end

end hidden