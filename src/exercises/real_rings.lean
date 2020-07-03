-- Exercise 6
variables (real : Type) [ordered_ring real]
variables (log exp : real → real)
variable  log_exp_eq : ∀ x, log (exp x) = x
variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
variable  exp_pos    : ∀ x, exp x > 0
variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

-- this ensures the assumptions are available in tactic proofs
include log_exp_eq exp_log_eq exp_pos exp_add

example (x y z : real) :
    exp (x + y + z) = exp x * exp y * exp z :=
by rw [exp_add, exp_add]

example (y : real) (h : y > 0)  : exp (log y) = y :=
exp_log_eq h

theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
    log (x * y) = log x + log y :=
begin
    have z : exp (log (x * y)) = exp (log x + log y) :=
        calc
        exp (log (x * y)) = x * y : by rw exp_log_eq (mul_pos hx hy) 
        ... = exp (log x) * exp (log y) : by rw [exp_log_eq hx, exp_log_eq hy]
        ... = exp (log x + log y) : by rw exp_add,

    have pf : log (exp (log (x * y))) = log (exp (log x + log y)) :=
    congr_arg log z,

    have lhs := calc
        log (exp (log (x * y))) = log (x * y) : by rw log_exp_eq,

    have rhs := calc
        log (exp (log x + log y)) = log x + log y : by rw log_exp_eq,

    show log (x * y) = log x + log y, from calc
        log (x * y) = log x + log y : by rw [eq.symm(lhs), pf, rhs],
end


-- Exercise 7
-- Prove the theorem below, using only the 
-- ring properties of ℤ enumerated in Section 4.2 and the theorem sub_self.
#check sub_self

example (x : ℤ) : x * 0 = 0 :=
calc
    x * 0 = x * (x - x) : by rw sub_self
    ... = x * x - x * x : by rw mul_sub
    ... = 0 : by rw sub_self

set_option trace.simplify.rewrite true

example (x : ℤ) : x * 0 = 0 :=
calc
    x * 0 = 0 : by simp
    -- [mul_zero]: x * 0 ==> 0
    -- [eq_self_iff_true]: 0 = 0 ==> true