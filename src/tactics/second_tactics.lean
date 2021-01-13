namespace hidden

inductive nat
| zero : nat
| succ : nat → nat
| pred : nat → nat

notation 0 := nat.zero
notation `S` := nat.succ
notation `P` := nat.pred
notation 1 := S 0
axiom succ_pred : ∀ n : nat, S (P n) = n

example : S (P 0) = 0 := succ_pred _ -- <=> succ_pred 0

lemma pred_succ_zero : P (S 0) = 0 :=
begin
  have h := λ(n m : nat)(f : nat → nat), n = m → f n = f m,
  type_check (h 0 0 (λ n, S n)), -- Prop
  have h2 : ∀ (n m : nat)(f : nat → nat), n = m → f n = f m := sorry,
  type_check h2 0 1 (λ n, n),

  have h3 := h2 0 0 (λ n, n),
  simp at h3,
  clear h3,
end

end hidden

example : true := true.intro

lemma test : (1 : hidden.nat) = 1 ∧ 2 = 2 :=
begin
  -- apply and.intro,
  -- exact eq.refl 1,
  -- exact eq.refl 2,

  -- apply ⟨eq.refl _, _⟩, -- invalid constructor ⟨...⟩
  refine ⟨eq.refl _, _⟩, -- 1 goal ⊢ 2 = 2
   -- rfl <=> eq.refl _, but with imlicit types: @rfl type value
  exact @rfl nat 2,
end

#print test

#check nat.succ


