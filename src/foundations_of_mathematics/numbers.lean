namespace integer_numbers

set_option trace.simplify.rewrite true

inductive myint
| zero : myint
| succ : myint → myint
| pred : myint → myint

def P := myint.pred
def S := myint.succ

axiom succ_pred {n : myint} : S (P n) = n
axiom pred_succ {n : myint} : P (S n) = n

attribute [simp] succ_pred pred_succ

lemma sspp (n : myint) : S (S (P (P n))) = n :=
begin
  -- S (S (P (P n))) = n
  -- P (S (S (P (P n)))) = P n
  -- use pred_succ
  -- S (P (P n)) = P n
  -- use pred_succ
  -- P (P n) = P (P n)
  -- rw succ_pred,

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
  sorry,
end

lemma ppss (n : myint) : P (P (S (S n))) = n :=
  by rw [pred_succ, pred_succ]

lemma comm_succ_pred (n : myint) : S (P n) = P (S n) :=
  by rw [succ_pred, pred_succ]

#print comm_succ_pred

example : S (P myint.zero) = myint.zero := succ_pred

def pos : nat → myint
| 0            := myint.zero
| (nat.succ n) := myint.succ (pos n)

def neg : nat → myint
| 0            := myint.zero
| (nat.succ n) := myint.pred (neg n)

lemma pos_zero : pos 0 = myint.zero := rfl
lemma pos_one : pos 1 = S myint.zero := rfl
lemma neg_one : neg 1 = P myint.zero := rfl

example : (neg 1).succ.succ = pos 1 :=
begin
  rw neg_one,
  rw pos_one,
  sorry,
end

example : S (S (neg 1)) = pos 1 :=
begin
  rw neg_one,
  rw succ_pred,
  exact pos_one,
end

def add : myint → myint → myint
| myint.zero n     := n
| (myint.succ m) n := myint.succ (add m n)
| (myint.pred m) n := myint.pred (add m n)

instance : has_zero myint := ⟨myint.zero⟩
instance : has_one myint := ⟨myint.succ myint.zero⟩
instance : has_add myint := ⟨add⟩

def myint.one := myint.succ 0
def myint.neg_one := myint.succ 0
-- attribute [pattern] myint.one


example : 0 + 0 = myint.zero := rfl
example : 0 + 1 = myint.one := rfl

lemma myint.one_def : 1 = myint.one := rfl
attribute [simp] myint.one_def

example : neg 1 + 1 = 0 :=
begin
  -- simp only [(+)],
  -- rw [neg, neg, add, add],
  -- rw myint.one_def,
  -- rw myint.one,
  exact pred_succ,
end

lemma zero_add (n : myint) : add 0 n = n := rfl
lemma add_zero (n : myint) : add n 0 = n :=
begin
  induction n with n ih n ih,
  { refl },
  sorry,
end

lemma add_zero_one : add 0 1 = 1 ∧ add 1 0 = 1 := by split; refl
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