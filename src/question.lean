/-
how to use only exact to prove 0 + n = n:
-/
inductive mynat : Type
| zero : mynat
| succ : mynat → mynat

#print nat.add

open mynat
-- def add' : mynat → mynat → mynat
-- | a  zero     := a
-- | a  (succ b) := succ (add' a b)
constant add' : mynat → mynat → mynat

notation 0 := mynat.zero
-- notation a` + `b := add' a b

axiom add_zero' (a : mynat) : add' a 0 = a
axiom add_succ' (a b : mynat) : add' a (succ b) = succ(add' a b)

lemma zero_add'(n : mynat) : add' 0 n = n :=
begin
  induction n with d hd,
  rw add_zero',
  /-
  λ (n : mynat),
  mynat.rec ((id ((eq.refl (add' 0 0 = 0)).rec (add_zero' 0))).mpr (eq.refl 0))
    (λ (d : mynat) (hd : add' 0 d = d), sorry) n
  -/
  rw [add_succ', hd],
  /-
  λ (n : mynat),
  mynat.rec ((id ((eq.refl (add' 0 0 = 0)).rec (add_zero' 0))).mpr (eq.refl 0))
    (λ (d : mynat) (hd : add' 0 d = d),
       (id ((eq.refl (add' 0 d.succ = d.succ)).rec (add_succ' 0 d))).mpr
         ((id ((eq.refl ((add' 0 d).succ = d.succ)).rec hd)).mpr (eq.refl d.succ)))
    n  
  -/
end
#print zero_add'

notation a ++ b := add' a b

lemma add_assoc' (a b c : mynat) : (a ++ b) ++ c = a ++ (b ++ c) :=
begin
induction c with c hc,
rw add_zero',
rw add_zero',
rw add_succ',
rw add_succ',
rw add_succ',
rw hc,
end

lemma add_right_comm (a b c : mynat) : a + b + c = a + c + b :=
begin
  -- a + b + c
  rw add_assoc, 
  rw add_comm,
  -- <=> rotate permutation (231)
  -- b + c + a
  rw add_assoc,
  rw add_comm,
  -- c + a + b
  rw add_assoc,
  rw add_comm,
  -- a + b + c
end

/-

lemma succ_add (a b : mynat) : succ a + b = succ (a + b) :=
begin
  induction b with b hb,
  repeat {rw add_zero, },
  rw add_succ,
  rw add_succ,
  rw hb,
  refl,

-- n the set of natural numbers, addition is commutative. 
-- In other words, for all natural numbers a and b, we have a + b = b + a
lemma add_comm (a b : mynat) : a + b = b + a :=
begin
  induction a with a ha,
  rw [zero_add, add_zero],
  refl,
  rw add_succ,
  rw succ_add,
  rw ha,
  refl,
end

theorem succ_eq_add_one (n : mynat) : succ n = n + 1 :=
begin
  induction n with n hn,
  rw one_eq_succ_zero,
  rw zero_add, refl,
  rw succ_add,
end

lemma add_right_comm (a b c : mynat) : a + b + c = a + c + b :=
begin
  rw add_assoc,
  rw add_comm,
  apply eq.symm,
  rw add_comm,
  rw add_assoc,
  have : a + c = c + a, from add_comm a c,
  rw this, refl,
end


-/