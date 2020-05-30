namespace integer_numbers

inductive int
| zero : int
| succ : int → int
| pred : int → int

def P := int.pred
def S := int.succ

axiom succ_pred : ∀n : int, S (P n) = n
axiom pred_succ : ∀n : int, P (S n) = n


lemma sspp : ∀ n : int, S (S (P (P n))) = n :=
begin
  -- S (S (P (P n))) = n
  -- P (S (S (P (P n)))) = P n
  -- use pred_succ
  -- S (P (P n)) = P n
  -- use pred_succ
  -- P (P n) = P (P n)
  use pred_succ,
end

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

end halfnumbers