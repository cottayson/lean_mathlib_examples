namespace integer_numbers

set_option trace.simplify.rewrite true

inductive myint
| zero : myint
| succ : myint → myint
| pred : myint → myint


local notation `P` := myint.pred
local notation `S` := myint.succ

axiom succ_pred {n : myint} : S (P n) = n
axiom pred_succ {n : myint} : P (S n) = n

attribute [simp] succ_pred pred_succ

lemma sspp (n : myint) : S (S (P (P n))) = n :=
begin
  -- S (S (P (P n))) = n
  -- use congr
  -- P (S (S (P (P n)))) = P n
  -- use pred_succ
  -- S (P (P n)) = P n
  -- use pred_succ
  -- P (P n) = P (P n)

  -- try to substitute S (P n) → n
  -- apply eq.subst (succ_pred.symm),
  rw succ_pred,
  exact succ_pred,
end

#print sspp

-- λ (n : myint), (id ((eq.refl (S (S (P (P n))) = n)).rec succ_pred)).mpr succ_pred

lemma sspp₂ (n : myint) : S (S (P (P n))) = n :=
begin
  apply (eq.mpr _ succ_pred),
  exact n,
  have h := (eq.rec succ_pred),
  type_check (h succ_pred), -- S (P (S (P ?m_1))) = ?m_1
  all_goals { sorry },
end

lemma ppss (n : myint) : P (P (S (S n))) = n :=
  by rw [pred_succ, pred_succ]

lemma comm_succ_pred (n : myint) : S (P n) = P (S n) :=
  by rw [succ_pred, pred_succ]

#print comm_succ_pred

example : S (P myint.zero) = myint.zero := succ_pred

constant pos : nat → myint
-- | 0            := myint.zero
-- | (nat.succ n) := myint.succ (pos n)

axiom pos.zero : pos 0 = myint.zero
axiom pos.step {n : ℕ} : pos (nat.succ n) = myint.succ (pos n)

constant neg : nat → myint
-- | 0            := myint.zero
-- | (nat.succ n) := myint.pred (neg n)
axiom neg.zero : neg 0 = myint.zero
axiom neg.step {n : ℕ} : neg (nat.succ n) = myint.pred (neg n)

attribute [simp] pos.zero pos.step neg.zero neg.step

example : pos 0 = myint.zero := pos.zero
lemma pos_one : pos 1 = S myint.zero := by rw [pos.step, pos.zero]
lemma neg_one : neg 1 = P myint.zero := by rw [neg.step, neg.zero]

example : (neg 1).succ.succ = pos 1 :=
  by { rw [neg_one, pos_one], congr, exact succ_pred }
-- apply myint.pred.inj, add .pred into both sides of equation

example : S (S (neg 1)) = pos 1 :=
  by rw [neg_one, succ_pred, pos_one]
-- "exact pos_one" works when def keyword used

constant add : myint → myint → myint
-- | myint.zero n     := n
-- | (myint.succ m) n := myint.succ (add m n)
-- | (myint.pred m) n := myint.pred (add m n)

axiom add.zero_id : add myint.zero = id
axiom add.succ {m n : myint} : add (S m) n = S (add m n)
axiom add.pred {m n : myint} : add (P m) n = P (add m n)

instance : has_zero myint := ⟨myint.zero⟩
instance : has_one myint := ⟨myint.succ myint.zero⟩
noncomputable instance : has_add myint := ⟨add⟩

-- def myint.one := myint.succ 0
-- def myint.neg_one := myint.succ 0
-- attribute [pattern] myint.one
-- @[refl]
lemma add.zero {n : myint} : add myint.zero n = n := by {
  rw add.zero_id,
  exact id.def n, -- refl,
}

@[simp]
lemma myint.zero_def : 0 = myint.zero := rfl

@[simp]
lemma myint.one_def : 1 = S 0 := rfl

-- test reflexivity attribute
-- lemma x1_proof : add 0 10 = 10 := add.zero
-- example : x1_proof = add.zero := rfl -- demonstrate that proof is add_zero?

-- test reflexivity attribute
lemma x1_proof : S 10 = S 10 := by refl
example : x1_proof = eq.refl (S _) := rfl

example : (0 : myint) + 0 = 0 := @add.zero 0
example : (0 : myint) + 1 = 1 := @add.zero 1

example : add (S 0) 0 = (1 : myint) := by {
  rw add.succ,
  rw myint.zero_def,
  rw add.zero,
  refl,
  -- exact myint.one_def,
}

example : (1 : myint) + 0 = 1 := by { simp [(+)], rw [add.succ, add.zero] }
example : (1 : myint) + 1 = pos 2 := by {
  rw pos.step,
  rw pos.step,
  rw pos.zero,
  simp [(+)],
  rw add.succ,
  rw add.zero,
}

-- lemma myint.one_def : 1 = myint.one := rfl
-- attribute [simp] myint.one_def

example : add myint.zero 1 = S 0 :=
begin
  rw add.zero,
  refl,
  -- rw myint.one_def,
end

example : neg 1 + 1 = 0 :=
begin
  simp only [(+)],
  rw neg_one,
  rw add.pred,
  rw add.zero,
  rw myint.one_def,
  exact pred_succ,
end

lemma zero_add (n : myint) : add 0 n = n := add.zero
lemma add_zero (n : myint) : add n 0 = n :=
begin
  induction n with n ih n ih, 
  { exact add.zero },
  { 
    -- rw [add.succ, ih]
    apply eq.trans (@add.succ n 0),
    congr,
    exact ih,
  },
  { 
    -- rw [add.pred, ih],
    type_check @add.pred n 0,
    apply eq.trans (@add.pred n 0),
    congr,
    exact ih,
  },
end

#print add_zero

lemma add_zero_one : add 0 1 = 1 ∧ add 1 0 = 1 := by simp [add.succ, add.zero]
lemma some (a b : Prop) {ha : a} {hb : b} : a ∧ b := by split; assumption
example : and.intro add_zero_one.left add_zero_one.right = add_zero_one := rfl
example : add_zero_one.left = add_zero_one.1 ∧ add_zero_one.right = add_zero_one.2 :=
  ⟨rfl, rfl⟩

end integer_numbers

namespace halfnumbers

inductive nat
| zero : nat
| succ : nat → nat
| halfpred : nat → nat

notation 0 := nat.zero
def S := nat.succ
def P := nat.halfpred
notation 1 := S 0
axiom succ_pred_2 : ∀ n : nat, S (P (P n)) = n
axiom pred_2_succ : ∀ n : nat, P (P (S n)) = n
-- We dont need this type of numbers because:
--   If substitute [P (P n) → P² n] in all theorems than halfnumbers becomes
-- integer numbers with successor S and predecessor P².

-- But if P has additional properties rather than P²?

end halfnumbers