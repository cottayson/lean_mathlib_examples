-- https://github.com/leanprover-community/mathlib/issues/2794
import data.nat.prime
open nat
@[simp] lemma min_fac_eq_one_iff (n : ℕ) : min_fac n = 1 ↔ n = 1 := sorry
lemma min_fac_eq_two_iff (n : ℕ) : min_fac n = 2 ↔ 2 ∣ n :=
begin
  split,
  { sorry },
  { intro h,
    have ub := min_fac_le_of_dvd (le_refl 2) h,
    have lb := min_fac_pos n,
    -- If `interval_cases` and `norm_num` were already available here,
    -- this would be easy and pleasant.
    -- But they aren't, so it isn't.
    cases h : n.min_fac with m,
    { sorry },
    { cases m with m,
      { simp at h, subst h, rcases? h, /- goals accomplished -/
      /- Try this: rcases h with ⟨_ | _ | _ | _ | h_w, rfl⟩ -/
       },
      { cases m with m,
        { refl, },
        { rw h at ub,
          rcases? ub, /- goals accomplished -/
          /- Try this: rcases ub with _ | _ -/ } } } }
end
/-
tactic failed, result contains meta-variables
state:
no goals
-/