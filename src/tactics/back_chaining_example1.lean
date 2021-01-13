import tactic.suggest

open tactic

set_option back_chaining.max_depth 10
set_option trace.tactic.back_chaining true

namespace ex1

constant f : ℕ → ℕ
constant g : ℕ → ℕ

axiom A : f 0 + f 1 = 5
axiom B : f 1 + f 2 = 3
axiom C : f 2 = 0

axiom add_zero (n : ℕ) : n + 0 = n
axiom add_comm (n m : ℕ) : n + m = m + n

example : f 0 = 2 :=
begin
  have h₁ := B,
  have h₂ := C,
  rw h₂ at h₁,
  rw add_zero at h₁,
  have h₃ := A,
  rw h₁ at h₃,
  exact add_right_cancel h₃,
end

end ex1

namespace ex2

constant α : Type
constant reverse_core : list α → list α → list α
constant reverse : list α → list α
constant concat : list α → list α → list α

axiom reverse_core.base (l : list α) : reverse_core [] l = l
axiom reverse_core.step (x : α) (xs l : list α) :
  reverse_core (x :: xs) l = reverse_core xs (x :: l)

axiom reverse.def (xs : list α) : reverse xs = reverse_core xs []

axiom concat.base (l : list α) : concat [] l = l
axiom concat.step (x : α) (xs l : list α) :
  concat (x :: xs) l = x :: concat xs l

lemma reverse.single (x : α) : reverse [x] = [x] :=
begin
  rw reverse.def,
  rw reverse_core.step,
  rw reverse_core.base,
end

#print reverse.single

attribute [intro] reverse_core.step reverse_core.base reverse.def

lemma reverse.single₂ (x : α) : reverse [x] = [x] :=
begin
  -- back_chaining, -- use apply but i expect that one use rewrite :(
    sorry,
end

end ex2

namespace ex3
constants a b c d : Prop

constant ab : a → b
constant bc : b → c
constant cd : c → d

attribute [intro] ab bc cd

lemma example₁ (h : a) : d :=
begin
  apply cd,
  apply bc,
  apply ab,
  exact h,
end

lemma example₂ (h : a) : d :=
begin
  back_chaining,
end

constants x y z : Prop

lemma example₃ (h : a) (ax : a → x) : x :=
begin
  success_if_fail { back_chaining,},
  suggest, -- exact ax h
  exact ax h,
end

#print example₁
#print example₂

end ex3
