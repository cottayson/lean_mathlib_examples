import data.real.basic
import algebra.pi_instances

notation `|`x`|` := abs x

/-
In this file we manipulate the elementary definition of limits of
sequences of real numbers. 
mathlib has a much more general definition of limits, but here
we want to practice using the logical operators and relations
covered in the previous files.
A sequence u is a function from ℕ to ℝ, hence Lean says
u : ℕ → ℝ
The definition we'll be using is:
-- Definition of « u tends to l »
def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε
Note the use of `∀ ε > 0, ...` which is an abbreviation of
`∀ ε, ε > 0 → ... `
In particular, a statement like `h : ∀ ε > 0, ...`
can be specialized to a given ε₀ by
  `specialize h ε₀ hε₀`
where hε₀ is a proof of ε₀ > 0.
Also recall that, wherever Lean expects some proof term, we can
start a tactic mode proof using the keyword `by` (followed by curly braces
if you need more than one tactic invocation).
For instance, if the local context contains:
δ : ℝ
δ_pos : δ > 0
h : ∀ ε > 0, ...
then we can specialize h to the real number δ/2 using:
  `specialize h (δ/2) (by linarith)`
where `by linarith` will provide the proof of `δ/2 > 0` expected by Lean.
We'll take this opportunity to use two new tactics:
`norm_num` will perform numerical normalization on the goal and `norm_num at h` 
will do the same in assumption `h`. This will get rid of trivial calculations on numbers,
like replacing |l - l| by zero in the next exercise.
`congr'` will try to prove equalities between applications of functions by recursively 
proving the arguments are the same. 
For instance, if the goal is `f x + g y = f z + g t` then congr will replace it by
two goals: `x = z` and `y = t`.
You can limit the recursion depth by specifying a natural number after `congr'`. 
For instance, in the above example, `congr' 1` will give new goals
`f x = f z` and `g y = g t`, which only inspect arguments of the addition and not deeper.
-/

variables (u v w : ℕ → ℝ) (l l' : ℝ)

-- If u is constant with value l then u tends to l
example : (∀ n, u n = 1) → seq_limit u l :=
begin
  sorry,
end