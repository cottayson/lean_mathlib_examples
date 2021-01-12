import data.real.basic
-- import data.set.basic
-- import tactic.ring

universe u

-- test for reals
example (x : ℝ) : (1 - x) + x = 1 := by ring

-- test for set theory
example {α : Type} (A B : set α) : A ∪ B = B ∪ A := set.union_comm A B
-- example {α : Type} (A B : set α) : A ∪ B = B ∪ A := by finish

constant α : Type u
notation `S` := set.univ

#check @set.subset_empty_iff
example : ∀ (A : set α), A ∪ -A = set.univ := set.union_compl_self
example : ∀ (A : set α), A ⊆ ∅ ↔ A = ∅ := λ s, set.subset_empty_iff
example : ∀ (A B : set α), A ⊆ B → A ∪ B \ A = B := λ a b, set.union_diff_cancel

#check set.inter_compl_self

lemma s.union_comm : ∀ {A B : set α}, A ∪ B = B ∪ A := set.union_comm
lemma s.union_with_complement : ∀ {A : set α}, A ∪ -A = set.univ := set.union_compl_self
lemma s.intersection_with_complement : ∀ {A : set α}, A ∩ -A = ∅ := set.inter_compl_self
lemma s.union_empty : ∀ (A : set α), A ∪ ∅ = A := set.union_empty
lemma s.inter_empty : ∀ (A : set α), A ∩ ∅ = ∅ := set.inter_empty
lemma s.inter_univ : ∀ (A : set α), A ∩ S = A := set.inter_univ
lemma s.diff_eq : ∀ (A B : set α), A \ B = A ∩ -B := set.diff_eq
lemma s.not_univ : -@set.univ α = ∅ := sorry
lemma s.inter_distrib : ∀ (A B C : set α), A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := sorry
-- A = A ∩ -B ∪ A ∩ B = A ∩ (-B ∪ B) = A ∩ S = A

#check set.union_empty
#check @set.union_diff_cancel


namespace prob
constant P : set α → ℝ
-- ********** axioms of probability **********
axiom a1 : ∀ A : set α, P A ≥ 0
axiom a2 : P set.univ = 1
axiom a3 : ∀ A B : set α, A ∩ B = ∅ → P (A ∪ B) = P A + P B
-- axiom a2_2 : P ∅ = 0
-- ********** axioms of probability **********

theorem t1 (A : set α) : P (-A) = 1 - P A :=
begin
  have h₁ : P (A ∪ -A) = P A + P (-A) := a3 A (-A) s.intersection_with_complement,
  rw [s.union_with_complement, a2] at h₁,
  rw h₁,
  exact eq.symm (add_sub_cancel' (P A) (P (-A))),
end

theorem t2 : ∀ A : set α, P A ≤ 1 :=
begin
  sorry,
end

theorem t3 : P ∅ = 0 :=
begin
  have h₁ := t1 S,
  rw s.not_univ at h₁,
  rw [h₁, a2],
  exact sub_self 1,
end

lemma lemma1 (A B : set α) : P (A ∪ B) = P (A \ B) + P (A ∩ B) + P (B \ A) := sorry

lemma lemma2 (A B : set α) : P A = P (A \ B) + P (A ∩ B) :=
begin
  have h₀ : (A \ B) ∩ (A ∩ B) = ∅ := by {
  calc (A \ B) ∩ (A ∩ B) = (A ∩ -B) ∩ (A ∩ B) : by rw s.diff_eq
                     ... = (A ∩ -B) ∩ (B ∩ A) : by rw set.inter_comm A B
                     ... = A ∩ -B ∩ B ∩ A     : by rw ←set.inter_assoc
                     ... = A ∩ (-B ∩ B) ∩ A   : by rw set.inter_assoc A
                     ... = A ∩ (B ∩ -B) ∩ A   : by rw set.inter_comm _ B
                     ... = A ∩ ∅ ∩ A          : by rw s.intersection_with_complement
                     ... = A ∩ (∅ ∩ A)        : by rw set.inter_assoc
                     ... = ∅ ∩ A ∩ A          : by rw set.inter_comm
                     ... = ∅ ∩ (A ∩ A)        : by rw set.inter_assoc
                     ... = A ∩ A ∩ ∅          : by rw set.inter_comm
                     ... = ∅                  : s.inter_empty (A ∩ A)
  },
  have h₀ : (A \ B) ∩ (A ∩ B) = ∅ := by {
    rw s.diff_eq,
    rw set.inter_comm A B,
    rw ←set.inter_assoc,
    rw set.inter_assoc A,
    rw set.inter_comm _ B,             -- A ∩ (B ∩ -B) ∩ A = ∅
    rw s.intersection_with_complement, -- A ∩ ∅ ∩ A = ∅
    rw set.inter_assoc,                -- A ∩ (∅ ∩ A) = ∅
    rw set.inter_comm,                 -- ∅ ∩ A ∩ A = ∅
    rw set.inter_assoc,                -- ∅ ∩ (A ∩ A) = ∅
    rw set.inter_comm,                 -- A ∩ A ∩ ∅ = ∅
    exact s.inter_empty _,             -- ∅ = ∅
  },
  -- A = A ∩ -B ∪ A ∩ B = A ∩ (-B ∪ B) = A ∩ S = A
  have h𝔸 : A = A \ B ∪ A ∩ B := by {
    rw s.diff_eq,
    rw ←s.inter_distrib,
    rw s.union_comm,
    rw s.union_with_complement,
    rw s.inter_univ,
  },
  have h₁ := a3 (A \ B) (A ∩ B) h₀,
  rw ←h𝔸 at h₁,
  exact h₁,
end

theorem t4 (A B : set α) : P (A ∪ B) = P A + P B - P (A ∩ B) :=
begin
  have h₁ : P A = P (A \ B) + P (A ∩ B) := lemma2 A B,
  have h₂ : P B = P (B \ A) + P (B ∩ A) := lemma2 B A,
  rw set.inter_comm at h₂,
  rw [h₁, h₂],
  ring, -- simplify expression using P (A ∩ B) - P (A ∩ B) = 0, 
        -- idea: make config of computable object (in beginning of proof) to auto-check this
        -- use relational-tactic-keywords instead of one-way tactic methods
  rw ←add_assoc,
  exact lemma1 A B,
end

theorem t5 (A B : set α) : A ⊆ B → P A ≤ P B :=
begin
  have h₁ : P (B \ A) ≥ 0 := sorry -- use a1
  have h₂ : 
end


end prob
