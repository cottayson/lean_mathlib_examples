import tactic.hint

-- @[simp] theorem exists_prop {p q : Prop} : (∃ h : p, q) ↔ p ∧ q :=
-- ⟨λ ⟨h₁, h₂⟩, ⟨h₁, h₂⟩, λ ⟨h₁, h₂⟩, ⟨h₁, h₂⟩⟩

lemma ex1 (N : ℕ) : ∃ (n : ℕ) (H : n ≥ N), n ≥ N :=
begin
  refine ⟨N, _⟩,
  rw exists_prop,
  rw and_self,
  apply nat.less_than_or_equal.refl,
end

#print ex1

theorem mwe {P Q : nat → Prop} : ∀ (x : nat), ¬ (P x → Q x):=
begin
    -- rw classical.not_implies_iff,
    hint,
    intros,
    simp,
    sorry,
end
