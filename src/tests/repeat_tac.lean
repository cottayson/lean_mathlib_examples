example (p q r s : Prop) :
  p → q → r → s → (p ∧ q) ∧ (r ∧ s ∧ p) ∧ (p ∧ r ∧ q) :=
begin
  intros; repeat { constructor }; assumption
end