import tactic.suggest
import tactic.solve_by_elim
import tactic.show_term
-- https://github.com/Sterrs/leaning/blob/lean-3.4.2/src/principia/mygroup/basic.lean
namespace hidden

set_option trace.simplify.rewrite true

class mygroup (α : Type)
extends has_mul α, has_inv α :=
(e : α)
(mul_assoc (a b c : α) : a * b * c = a * (b * c))
(mul_id (a : α) : a * e = a)
(mul_inv (a : α) : a * a⁻¹ = e)

namespace mygroup
variables {α : Type} [mygroup α]
variables {a b c : α}

theorem mul_right (c : α) : a = b → a * c = b * c :=
  begin
    assume h,
    type_check congr_arg (λ d, d * c⁻¹) h, -- (λ (d : α), d * c⁻¹) a = (λ (d : α), d * c⁻¹) b
    have h2 := congr_arg (λ d, d * c) h,
    dsimp only [] at h2,
    exact h2,
  end

theorem mul_by_right : a = b → a * c = b * c := mul_right c
theorem mul_left (c : α) : a = b → c * a = c * b :=
  begin
    assume h,
    congr,
    exact h,
  end

theorem inv_mul (a : α) : a⁻¹ * a = e :=
  begin
    rw ←mul_inv a,
    rw ←mul_id (a⁻¹ * a),
    rw ←mul_inv a⁻¹,
    rw ←mul_assoc (a⁻¹ * a) a⁻¹ a⁻¹⁻¹,
    -- simp only [mul_assoc, mul_id, mul_inv],
    rw mul_assoc a⁻¹,
    rw mul_inv a,
    rw mul_id a⁻¹,
    rw mul_inv a⁻¹,
    -- [hidden.mygroup.mul_assoc]: a⁻¹ * a * a⁻¹ ==> a⁻¹ * (a * a⁻¹)
    -- [hidden.mygroup.mul_inv]: a * a⁻¹ ==> e
    -- [hidden.mygroup.mul_id]: a⁻¹ * e ==> a⁻¹
    -- [hidden.mygroup.mul_inv]: a⁻¹ * a⁻¹⁻¹ ==> e
  end

theorem id_mul (a : α) : e * a = a :=
  begin
    rw ←mul_inv a,
    rw mul_assoc,
    rw inv_mul,
    rw mul_id,
    -- simp only [←mul_inv a, mul_assoc, inv_mul, mul_id],
    -- [[←mul_inv]]: e ==> a * a⁻¹
    -- [hidden.mygroup.mul_assoc]: a * a⁻¹ * a ==> a * (a⁻¹ * a)
    -- [hidden.mygroup.inv_mul]: a⁻¹ * a ==> e
    -- [[anonymous]]: e ==> a * a⁻¹

    -- anonymous <=> ←mul_inv
  end

theorem id_unique (a b : α) : a * b = a ↔ b = e :=
  begin
    split; assume h,
      have H := (mul_left a⁻¹) h,
      clear h,
      rw ←mul_assoc at H,
      rw inv_mul at H,
      rw id_mul at H,
      exact H,
    subst h,
    exact mul_id a,
    -- second way, but not works: https://github.com/Sterrs/leaning/blob/c0f3c5ee190184762ae7b926c999095f8ec9a9ac/src/principia/mygroup/basic.lean#L67-L70
    -- split; assume h,
    --   rwa [mul_left a, mul_id],
    -- subst h,
    -- from mul_id a,
  end

theorem inv_unique (a b : α) : a * b = e ↔ b = a⁻¹ :=
  begin
    split; assume h,
      have H := (mul_left a⁻¹) h,
      clear h,
      rw ←mul_assoc at H,
      rw inv_mul at H,
      rw [id_mul, mul_id] at H,
      exact H,
    subst h,
    exact mul_inv a,
  end

lemma inv_inv (a : α) : a⁻¹⁻¹ = a :=
  begin
    have h := inv_mul a⁻¹, -- ↔ @inv_mul α _inst_1 a⁻¹
    have H := mul_right a h,
    clear h,
    rw mul_assoc at H,
    rw inv_mul at H,
    rw [id_mul, mul_id] at H,
    exact H,
  end
--- 
attribute [simp] mul_right mul_left inv_mul id_mul mul_id id_unique inv_unique inv_inv mul_assoc mul_inv
namespace hidden2
lemma inv_four : a⁻¹⁻¹⁻¹⁻¹ = a :=
  begin
    have h := inv_inv a,
    have h2 := inv_inv a⁻¹⁻¹,
    exact eq.trans h2 h,
  end

lemma inv_four' : a⁻¹⁻¹⁻¹⁻¹ = a :=
  begin
    calc a⁻¹⁻¹⁻¹⁻¹ = a⁻¹⁻¹ : inv_inv a⁻¹⁻¹
               ... = a     : inv_inv a
  end

lemma inv_four'' : a⁻¹⁻¹⁻¹⁻¹ = a :=
  by calc a⁻¹⁻¹⁻¹⁻¹ = a⁻¹⁻¹ : inv_inv _
                ... = a     : inv_inv _

-- equals each other
#print inv_four 
#print inv_four'
#print inv_four''

theorem id_mul' : e * a = a :=
  begin
    -- infinite loop:
    -- simp only [mul_assoc, inv_mul, mul_id, mul_inv a, ←mul_inv, ←mul_assoc, ←mul_id, ←mul_inv a, ←inv_mul],
    sorry,
  end
end hidden2

end mygroup

variables {α : Type} [mygroup α]
example (a : α) : a⁻¹⁻¹⁻¹⁻¹ = a := eq.trans (mygroup.inv_inv a⁻¹⁻¹) (mygroup.inv_inv a)

example (a : α) : a⁻¹⁻¹⁻¹⁻¹⁻¹⁻¹⁻¹⁻¹ = a := by simp
example (a : α) : a⁻¹⁻¹⁻¹⁻¹⁻¹⁻¹⁻¹ = a⁻¹ := by simp
example (a b c : α) : c⁻¹ * a⁻¹ * a * b = c⁻¹ * b := by simp

example (a : α) : a⁻¹⁻¹⁻¹⁻¹⁻¹⁻¹⁻¹⁻¹ = a :=
begin
  repeat {
    apply eq.trans,
    apply mygroup.inv_inv,
  }
  refl,
end

example (a : α) : a⁻¹⁻¹⁻¹ = a⁻¹ :=
begin
  repeat {
    apply eq.trans,
    apply mygroup.inv_inv,
    try { refl },
  },
end

example (a : α) : a⁻¹ = a⁻¹⁻¹⁻¹ :=
begin
  apply eq.symm,
  repeat {
    apply eq.trans,
    apply mygroup.inv_inv,
    try { refl },
  },
end

open int

example (n x a : ℤ) : abs x = a → x = a ∨ x = -a :=
begin
  intros h_abs,
  have helper : ∀ (k : ℤ), k < 0 ↔ ¬ k ≥ 0, sorry,
  by_cases (a < 0), {
    have h_pos : abs x >= 0, sorry,
    rw h_abs at h_pos,
    type_check iff.elim_left (helper a),
    type_check (helper a).elim_left,
    type_check (helper a).1,
    have H2 := iff.elim_left (helper a) h,
    contradiction,
  }, {
    rw helper _ at h,
    -- simp at h, -- not works
    -- change (a ≥ 0 → false) → false at h,
    have notnot : ∀ (p : Prop), p ↔ ¬¬p, from sorry, -- dec_trivial, simp, change not works
    type_check (notnot (a ≥ 0)).2 h,
    have new_h := (notnot (a ≥ 0)).2 h, clear h, rename new_h h,
    clear helper notnot,
    induction a,
    case int.of_nat {
      sorry,
    },
    case int.neg_succ_of_nat {
      sorry,
    },
  },

end

end hidden