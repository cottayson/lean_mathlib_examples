import tactic.hint
import tactic

lemma ex1 {P Q : Prop} (p : P) (h : P → Q) : Q :=
begin
  hint,
  /- the following tactics make progress:
     ----
     Try this: solve_by_elim
     Try this: finish
     Try this: tauto
  -/
  -- solve_by_elim, -- Give proof: h p
  -- tauto, -- Give proof: h p
  finish, -- Give proof:   (id
  --   (propext
  --     (iff_true_intro
  --         (id
  --           (((imp_congr_eq (propext (iff_true_intro p)) (eq.refl Q)).trans
  --               (propext (forall_prop_of_true true.intro))).mp
  --               h))))).mpr
  -- (classical.by_contradiction
  --     (λ (a : ¬true),
  --       (λ (P Q : Prop) (p : P) (h : Q) (a : ¬true), false.rec false (false_of_true_eq_false (eq_false_intro a))) P
  --         Q
  --         p
  --         (((imp_congr_eq (propext (iff_true_intro p)) (eq.refl Q)).trans
  --             (propext (forall_prop_of_true true.intro))).mp
  --             h)
  --         a))
end