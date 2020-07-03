namespace hidden

-- what is absurd keyword?
-- absurd a ¬a = a → ¬a → any
-- We can't have a and ¬a, that would be absurd!
lemma neq_of_not_iff {a b : Prop} : ¬(a ↔ b) → a ≠ b :=
λ h₁ h₂,
have a ↔ b, from eq.subst h₂ (iff.refl a),
absurd this h₁

lemma neq_of_not_iff₂ {a b : Prop} : ¬(a ↔ b) → a ≠ b :=
begin
  intros h₁ h₂,
  have : a ↔ b, from eq.subst h₂ (iff.refl a),
  -- exact absurd h₁ (not_not_intro this), -- another way
  exact absurd this h₁,
end

-- also works if change ¬(a ↔ b) → a = b → false to ¬(a ↔ b) → a = b → c
lemma neq_of_not_iff₃ {a b c: Prop} : ¬(a ↔ b) → a = b → c :=
  assume h₁ h₂,
  have a ↔ b, from eq.subst h₂ (iff.refl a),
  absurd this h₁

end hidden