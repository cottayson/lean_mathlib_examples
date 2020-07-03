constant α : Type
constant empty_set : set α
constant full_set : set α
axiom empty.branch {A : set α} : A = empty_set ∨ A ≠ empty_set

constant element : α → set α → Prop
local notation a ` ∈ ` b := element a b
reserve infix ` ∈ `: 50

-- Subset
constant subset : set α → set α → Prop
axiom subset.empty_some {A : set α} : subset empty_set A
lemma subset.not_some_empty {A : set α} (h : A ≠ empty_set) :
  ¬ subset A empty_set := sorry

lemma subset.empty_empty : subset empty_set empty_set := subset.empty_some

-- Inverse
constant inverse : set α → set α
axiom inverse.empty : inverse empty_set = full_set
lemma full_set.def : full_set = inverse empty_set := inverse.empty.symm

-- Intersection
constant intersect : set α → set α → set α
axiom intersect.empty {A : set α} : intersect A empty_set = empty_set
axiom intersect.full_set {A : set α} : intersect A full_set = A

axiom intersect.subset {A B : set α} (h : subset A B) : intersect A B = A

lemma intersect.empty_empty : intersect empty_set empty_set = empty_set :=
  @intersect.empty empty_set

lemma intersect.full_full : intersect full_set full_set = full_set :=
  @intersect.full_set full_set

lemma intersect.def {x : α} {A B : set α} : (x ∈ intersect A B) ↔ (x ∈ A ∧ x ∈ B) := sorry

-- Subtraction
constant subtract : set α → set α → set α
axiom subtract.def (A B : set α) : subtract A B = intersect A (inverse B)

-- Union
constant union : set α → set α → set α

axiom union.empty {A : set α} : union A empty_set = A
axiom union.step {A B C : set α} (h : subset C B) : 
  union A B = union C (union A (subtract B C))

lemma union.def {x : α} {A B : set α} : (x ∈ union A B) ↔ (x ∈ A ∨ x ∈ B) := sorry

lemma union.comm {A B : set α} : union A B = union B A := sorry

#print union.def
#print union.empty

lemma empty_union (A : set α) : union empty_set A = A :=
begin
  rw union.comm,
  apply union.empty,
  -- give shorter proof:
  -- =>> λ (A : set α), (id ((eq.refl (union empty_set A = A)).rec 
  --    (union.comm empty_set A))).mpr (union.empty A)
  -- than rewrite tactic:
  -- rw union.empty,
  -- =>> λ (A : set α),
  --   (id ((eq.refl (union empty_set A = A)).rec (union.comm empty_set A))).mpr
  --     ((id ((eq.refl (union A empty_set = A)).rec (union.empty A))).mpr (eq.refl A))  
end

constant is_empty : set α → Prop
axiom is_empty.base : is_empty empty_set

constant singleton_set : α → set α

constant set.without : set α → α → set α
axiom set.without.base (x : α) : set.without empty_set x = empty_set
-- Singleton ≈ set that contains only one element
lemma set.without.singleton (x : α) (A : set α) :
  (singleton_set x).without x = empty_set := sorry

constant size_of_set : set α → ℕ
axiom size_of_set.base : size_of_set empty_set = 0
axiom size_of_set.step (x : α) (A : set α) :
  element x A → size_of_set A = size_of_set (A.without x)

-- Definition of branching by assumption
constant subset_from_prop : (α → Prop) → set α → set α

axiom subset_from_prop.def (property : α → Prop) (A : set α) :
  subset_from_prop (λ _, true) A =
  union
    (subset_from_prop             property    A)
    (subset_from_prop (λ x : α, ¬ property x) A)
  ∧ subset (subset_from_prop             property    A) A
  ∧ subset (subset_from_prop (λ x : α, ¬ property x) A) A

  
-- lemma not_empty_imp_has_element (A : set α) :
--   A 

/--
  if A ≠ ∅ we have: 
      ⊢ A ≠ ∅ → union A A = A
    => by: ∀ A : set, union A A = ∅ → A = ∅
    | union A A ≠ ∅
    => by: ∀ A : set α, A ≠ ∅ → ∃ (x : α), x ∈ A
    | (∃ x, x ∈ A)
    ...
    (x ∈ union A A) ↔ (x ∈ A ∨ x ∈ A)
    ...
  otherwise A = ∅:
      ⊢ union ∅ ∅ = ∅
    by: union.empty: ∀ A : set, union A ∅ = A
    | union ∅ ∅ = ∅
    Qed.


  -/
lemma union.self₁ (A : set α) : union A A = A :=
begin
  
  sorry,
end

lemma union.self₂ (x : α) (A : set α) : element x (union A A) = element x A :=
begin
  have h := @union.def x A A,
  have h2 := or_self (element x A),
  rw ←h2,
  exact h.to_eq,
end

