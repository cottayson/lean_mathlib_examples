constant ax : nat
noncomputable def test : nat → nat
| 0     := ax
| (n+1) := test n

---

constant f : nat → nat
noncomputable def test' : nat → nat
| 0     := ax
| (n+1) := f (test' n)

#reduce test' 0 -- ax
#reduce test' 1 -- f ax
#reduce test' 2 -- f (f ax)
#reduce test' 3 -- f (f (f ax))

constant h : ∀ n, ax = n → f (f ax) = n 

example : test' 3 = f (f (f ax)) := rfl

set_option trace.simplify.rewrite true

lemma ex1 : test' 2 = ax :=
begin
  simp [test'],
-- [test'.equations._eqn_2]: test' 2 ==> f (test' 1)
-- [test'.equations._eqn_2]: test' 1 ==> f (test' 0)
-- [test'.equations._eqn_1]: test' 0 ==> ax  
  apply (h ax),
  refl,
end

lemma ex2 : test' 2 = ax :=
begin
  simp [test', h ax],
-- [test'.equations._eqn_2]: test' 2 ==> f (test' 1)
-- [test'.equations._eqn_2]: test' 1 ==> f (test' 0)
-- [test'.equations._eqn_1]: test' 0 ==> ax
-- [eq_self_iff_true]: ax = ax ==> true
-- [[h ax]]: f (f ax) ==> ax
-- [eq_self_iff_true]: ax = ax ==> true
end

lemma ex3 : test' 3 = f ax :=
begin
  simp [test', h ax],
-- [test'.equations._eqn_2]: test' 3 ==> f (test' 2)
-- [test'.equations._eqn_2]: test' 2 ==> f (test' 1)
-- [test'.equations._eqn_2]: test' 1 ==> f (test' 0)
-- [test'.equations._eqn_1]: test' 0 ==> ax
-- [eq_self_iff_true]: ax = ax ==> true
-- [[h ax]]: f (f ax) ==> ax
-- [eq_self_iff_true]: f ax = f ax ==> true
end