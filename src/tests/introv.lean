example : ∀ a b : nat, a = b → b = a :=
begin
  introv h,
  exact h.symm,
end

example : ∀ a b : nat, a = b → ∀ c, b = c → a = c :=
begin
  introv h₁ h₂,
  exact h₁.trans h₂,
end

example : ∀ a b : nat, a = b → b = a :=
begin
-- intros introduce a = b, but we want only variables, without hypotheses
  introv, 
  intro h,
  exact h.symm,
end