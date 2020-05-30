namespace weekday_example

inductive weekday
| sunday | monday | tuesday | wednesday
| thursday | friday | saturday

open weekday

def next : weekday → weekday
| sunday := monday
| monday := tuesday
| tuesday := wednesday
| wednesday := thursday
| thursday := friday
| friday := saturday
| saturday := sunday

lemma next_sunday_is_monday : next sunday = monday := rfl

end weekday_example

namespace list_example

universe u

inductive list (α : Type u)
| nil {} : list
| cons (a : α) (l : list) : list

@[pattern]
def list.nil' (α : Type u) : list α := list.nil

def length {α : Type u} : list α → ℕ
| (list.nil' .(α)) := 0
| (list.cons a l) := 1 + length l

def cs {α : Type} (l : list α) := list.cons l

#check cs 3 (cs 4 (cs 5 list.nil))
#check [3, 4, 5]

end list_example

namespace nat_example

inductive nat
| zero
| succ (n : nat) : nat

constants (α : Sort)

#check nat
#check nat.rec -- ?M_1 nat.zero → (Π (n : nat), ?M_1 n → ?M_1 n.succ) → Π (n : nat), ?M_1 n
#check nat.rec _ _ -- Π (n : nat), ?M_1 n
#check nat.zero -- nat
#check nat.succ -- nat

#check nat.rec_on -- Π (n : nat), ?M_1 nat.zero → (Π (n : nat), ?M_1 n → ?M_1 n.succ) → ?M_1 n
#check nat.cases_on -- Π (n : nat), ?M_1 nat.zero → (Π (n : nat), ?M_1 n.succ) → ?M_1 n
#check nat.no_confusion_type -- Sort u_1 → nat → nat → Sort u_1
#check @nat.no_confusion -- Π {P : Sort u_1} {v1 v2 : nat}, v1 = v2 → nat.no_confusion_type P v1 v2
#check nat.brec_on -- Π (n : nat), (Π (n : nat), nat.below ?M_1 n → ?M_1 n) → ?M_1 n
#check nat.below -- (nat → Sort u_1) → nat → Sort (max 1 u_1)
#check nat.ibelow -- (nat → Prop) → nat → Prop
#check nat.sizeof -- nat → ℕ

end nat_example

namespace equation_compiler

open nat

def sub2 : ℕ → ℕ
| zero            := 0
| (succ zero)     := 0
| (succ (succ a)) := a

set_option trace.simplify.rewrite true

lemma helper : ∀ n k : nat, n < k.succ → n < k ∨ n = k
| 0 0 := begin -- example of backward proof
    have H : ∀ a : Prop, a → (true → a), {
      intro a,
      rw true_implies_iff a,
      sorry,
    },
    have zero_less_one : 0 < 1, sorry,
    simp only [zero_less_one],
    apply H, -- example of one step backward (changing goal)
    --   goal changed from 
    --   ⊢ true → 0 < 0 ∨ 0 = 0 to
    --   ⊢ 0 < 0 ∨ 0 = 0     <<<<<<< move backward from (true → a) to (a)
    --   using ∀ a : Prop, a → (true → a)
    right,
    refl,
    -- simp, 
    -- [eq_self_iff_true]: 0 = 0 ==> true
    -- [or_true]: 0 < 0 ∨ true ==> true
    -- [implies_true_iff]: 0 < 1 → true ==> true
  end
| n k := begin sorry, end

lemma helper₂ (n : ℕ) : ¬ n < 0 :=
match n with
| 0 := 
  begin
    have h : 0 < 0 → false, {
      sorry,
    },
    sorry,
  end
| (nat.succ n) := sorry
end

lemma property₁ : ∀ n : ℕ, n < 2 → sub2 n = 0 :=
begin
  intros n h,
  type_check helper n 1,
  have H_helper := helper n 1,
  have h_or : n < 1 ∨ n = 1 := H_helper h,
  clear H_helper h,
  cases h_or with n_lt_1 n_eq_1,
  { -- n < 1 => n < 0 ∨ n = 0
    type_check helper n 0 n_lt_1, -- n < 0 ∨ n = 0
    have h_or := helper n 0 n_lt_1,
    clear n_lt_1,
    cases h_or with n_lt_0 n_eq_0,
    { -- n < 0 => contradiction
      type_check lt.base 0,
      type_check lt.step (nat.lt.base 0),
      exfalso,
      have not_n_less_0 := helper₂ n,
      apply not_n_less_0,
      assumption, -- exact n_lt_0,
    },
    { -- n = 0
      rw n_eq_0,
      refl,
    },
  },
  { -- n = 1
    rw n_eq_1,
    refl,
  }
end

#print property₁


end equation_compiler