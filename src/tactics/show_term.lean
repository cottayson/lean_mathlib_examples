import tactic.show_term
import tactic.tauto

open tactic

lemma ex1 {P Q R : Prop} (h₁ : Q → P) (h₂ : R) (h₃ : R → Q) : P ∧ R :=
by show_term { tauto }

#print ex1

example (x y : ℕ) (hx : x = 0) (hy : y = 1) : x + y = 1 :=
begin
  show_term { rw hx, }, -- (id ((eq.refl (x + y = 1)).rec hx)).mpr ?m_1
  show_term { rw hy, },
end

example (x y z : ℕ) : x + y + z = x + z + y :=
begin
  show_term { simp [add_comm], },
  sorry,
end