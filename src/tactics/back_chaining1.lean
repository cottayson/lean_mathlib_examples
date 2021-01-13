-- Backward chaining with tagged rules
constants {P Q R S T U : Prop} (Hpq : P → Q) (Hqr : Q → R) (Hrs : R → S) (Hst : S → T)
constants (Huq : U → Q) (Hur : U → R) (Hus : U → S) (Hut : U → T)
attribute [intro] Hpq Hqr Hrs Hst
attribute [intro] Huq Hur Hus Hut

open tactic

set_option back_chaining.max_depth 1
set_option trace.tactic.back_chaining true

definition lemma1 (p : P) : Q := by back_chaining
definition lemma2 (p : P) : R := by back_chaining
definition lemma3 (p : P) : S := by back_chaining
definition lemma4 (p : P) : T := by back_chaining

#print lemma1 -- λ (p : P), Hpq p
#print lemma2 -- λ (p : P), Hqr (Hpq p)
#print lemma3 -- λ (p : P), Hrs (Hqr (Hpq p))
#print lemma4 -- λ (p : P), Hst (Hrs (Hqr (Hpq p)))