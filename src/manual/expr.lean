open nat

inductive Expr
| zero : Expr
| one  : Expr
| add  : Expr → Expr → Expr

namespace Expr

inductive direct_subterm : Expr → Expr → Prop
| add_1 : ∀ e₁ e₂ : Expr, direct_subterm _ (add _ _)
| add_2 : ∀ e₁ e₂ : Expr, direct_subterm _ (add _ _)

theorem direct_subterm_wf : well_founded direct_subterm :=
begin
  constructor,
  intro e,
  induction e,
  all_goals { constructor },
  all_goals { sorry }
end

def subterm := tc direct_subterm

#check @tc -- tc : Π {α : Sort u_1}, (α → α → Prop) → α → α → Prop

theorem subterm_wf : well_founded subterm := tc.wf direct_subterm_wf

local infix `+` := Expr.add

set_option pp.notation false

def ev : Expr → nat
| zero := 0
| one := 1
| ((a : Expr) + b) := has_add.add (ev a) (ev b)

def foo : Expr := add zero (add one one)

example : ev foo = 2 := rfl

end Expr