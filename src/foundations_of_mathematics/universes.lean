#check @and.intro -- and.intro : ∀ {a b : Prop}, a → b → a ∧ b

lemma proof_irrelevance {a : Prop} (h₁ h₂ : a) :
  h₁ = h₂ := rfl

/-
  In Lean, this equality is a syntactic equality up to computation, allowing us to use
the refl tactic. When viewing a proposition as a type and a proof as an element
of that type, proof irrelevance means that a proposition is either an empty type or
has exactly one inhabitant. If it is empty, it is false. If it has exactly one inhabitant,
it is true. Proof irrelevance is very helpful when reasoning about dependent types.


  An unfortunate consequence of proof irrelevance is that it prevents us from
performing rule induction by pattern matching. Induction by pattern matching 
relies on a “measure”—a function to N that assigns a size to the arguments. 
Without large elimination, the measure cannot be defined meaningfully.
This explains why we always use the induction tactic for rule induction.
-/