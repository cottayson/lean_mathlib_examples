import tactic

-- set_option trace.simp_lemmas true
set_option trace.simplify.rewrite true

inductive sorted : list ℕ → Prop
| nil : sorted []
| single {x : ℕ} : sorted [x]
| two_or_more {x y : ℕ} {zs : list ℕ} (hle : x ≤ y)
    (hsorted : sorted (y :: zs)) :
  sorted (x :: y :: zs)

lemma sorted_3_5 :
  sorted [3, 5] :=
begin
  apply sorted.two_or_more, -- give us two goals:
  -- ⊢ 3 ≤ 5
  exact dec_trivial,
  -- ⊢ sorted [5]
  exact sorted.single,
end

lemma sorted_3_5₂ :
  sorted [3, 5] :=
sorted.two_or_more dec_trivial sorted.single
-- of_as_true : ∀ {c : Prop} [h₁ : decidable c], as_true c → c

lemma sorted_3_5₃ :
  sorted [3, 5] :=
sorted.two_or_more (of_as_true trivial) sorted.single

-- Some strange tries:

-- example : dec_trivial = of_as_true trivial := lean doesn't support that kind of proving?

-- example : sorted_3_5 ↔ sorted_3_5₂ := wrong
-- example (h1 : sorted_3_5) (h2 : sorted_3_5₂): h1 ↔ h2 := wrong

lemma sorted_7_9_9_11:
  sorted [7, 9, 9, 11] :=
sorted.two_or_more dec_trivial
  (
    sorted.two_or_more dec_trivial
    (
      sorted.two_or_more dec_trivial sorted.single
    )
  )

lemma sorted_7_9_9_11₂:
  sorted [7, 9, 9, 11] :=
begin
  -- backward_chaining, -- unknown identifier 'backward_chaining'
  repeat { constructor, exact dec_trivial, },
  exact sorted.single,
    -- simp [sorted.two_or_more, sorted.single],
  /-
  simp see only that rules:
    list.nil_subset
    list.subset.refl
    list.subset_cons
    list.subset_append_left
    list.subset_append_right
  -/
end

namespace helper
lemma sorted_nil : sorted [] := sorry
lemma sorted_single (n : ℕ): sorted [n] := sorry
lemma sorted_two_or_more
  (n m : ℕ) (ls : list ℕ) 
  (hsorted : sorted (m :: ls)) :
    sorted (n :: m :: ls) := sorry
end helper

lemma ex1 : sorted [] :=
begin
  exact helper.sorted_nil,
end

#print ex1

lemma ex2 : sorted [] :=
begin
  simp only [helper.sorted_nil],
  -- [helper.sorted_nil]: sorted list.nil ==> true
  -- (id (propext (iff_true_intro helper.sorted_nil))).mpr trivial
end
#print ex2

lemma ex2' : sorted [] :=
begin
  simp only [sorted.nil],
  -- [sorted.nil]: sorted list.nil ==> true
  -- (id (propext (iff_true_intro sorted.nil))).mpr trivial
end
#print ex2'

lemma ex3 : sorted [1] ∧ sorted [] :=
begin
  simp only [sorted.nil, sorted.single, and_self],
end
#print ex3

lemma ex4 : sorted [1, 2] :=
begin
  -- library_search [sorted.two_or_more], not works
  -- have H : sorted [1],
  --   exact sorted.single,
  repeat {
    constructor,
    linarith,
    simp only [sorted.nil, sorted.single],
  },
end
#print ex4 -- proof is too long :( >> sorted.two_or_more (of_as_true trivial) sorted.single

lemma ex4' : sorted [1, 2] :=
  sorted.two_or_more dec_trivial sorted.single

#print ex4' -- sorted.two_or_more (of_as_true trivial) sorted.single

lemma ex5 : sorted [40, 70] :=
begin
  -- library_search [sorted.two_or_more], not works
  -- have H : sorted [1],
  --   exact sorted.single,
  repeat {
    constructor,
    linarith,
    simp only [sorted.single],
  },
end

lemma ex6 : sorted [1, 2, 3] :=
begin
  constructor,
  simp,
  constructor,
  simp,
  exact sorted.single,
end
#print ex6
/-
sorted_lists.lean:132:0: information print result
theorem ex6 : sorted [1, 2, 3] :=
sorted.two_or_more
  ((id ((propext nat.one_le_bit0_iff).trans (propext (λ {n : ℕ}, iff_true_intro nat.succ_pos')))).mpr trivial)
  (sorted.two_or_more ((id (propext nat.bit0_le_bit1_iff)).mpr (le_refl 1)) sorted.single)
-/

lemma ex7 : sorted [1, 2, 3, 4, 5] :=
begin
  repeat {constructor, simp, },
  exact sorted.single,
end
#print ex7
-- GIVE:
/-
sorted.two_or_more
  ((id ((propext nat.one_le_bit0_iff).trans (propext (λ {n : ℕ}, iff_true_intro nat.succ_pos')))).mpr trivial)
  (sorted.two_or_more ((id (propext nat.bit0_le_bit1_iff)).mpr (le_refl 1))
     (sorted.two_or_more ((id ((propext nat.bit1_le_bit0_iff).trans (propext nat.one_lt_bit0_iff))).mpr (le_refl 1))
        (sorted.two_or_more ((id ((propext nat.bit0_le_bit1_iff).trans (propext bit0_le_bit0))).mpr (le_refl 1))
           sorted.single)))
-/
-- EXPECTED:
/-
sorted.two_or_more (of_as_true trivial)
  (sorted.two_or_more (of_as_true trivial)
     (sorted.two_or_more (of_as_true trivial) 
        (sorted.two_or_more (of_as_true trivial) 
          sorted.single)))
-/

lemma ex7' : sorted [1, 2, 3, 3, 5] :=
begin
  -- constructor_matching _ <=> constructor 
  repeat { constructor, exact dec_trivial, },
  exact sorted.single,
end
#print ex7'
/-
theorem ex7' : sorted [1, 2, 3, 3, 5] :=
sorted.two_or_more (of_as_true trivial)
  (sorted.two_or_more (of_as_true trivial)
     (sorted.two_or_more (of_as_true trivial) 
        (sorted.two_or_more (of_as_true trivial) 
            sorted.single)))
-/
lemma not_sorted_17_13 : ¬ sorted [2, 1] :=
begin
  assume h : sorted [2, 1],
  have h2: 2 ≤ 1 :=
    match h with
    | sorted.two_or_more hle _ := hle
    end,
  have h3: ¬ 2 ≤ 1 :=
    dec_trivial,
  -- contradiction, <=>
  show false, from by cc,
end
#print not_sorted_17_13
/-
sorted_lists.lean:202:0: information print result
theorem not_sorted_17_13 : ¬sorted [2, 1] :=
id
  (λ (h : sorted [2, 1]),
     (false_of_true_eq_false
        ((eq_true_intro
            ((λ (_a : sorted [2, 1]),
                _a.dcases_on (λ (H_1 : [2, 1] = list.nil), list.no_confusion H_1)
                  (λ {x : ℕ} (H_1 : [2, 1] = [x]),
                     list.no_confusion H_1
                       (λ (a : (1.add 0).succ = x), eq.rec (λ (tl_eq : [1] = list.nil), list.no_confusion tl_eq) a))
                  (λ {x y : ℕ} {zs : list ℕ} (hle : x ≤ y) (hsorted : sorted (y :: zs))
                   (H_1 : [2, 1] = x :: y :: zs),
                     list.no_confusion H_1
                       (λ (a : (1.add 0).succ = x),
                          eq.rec
                            (λ (hle : (1.add 0).succ ≤ y) (tl_eq : [1] = y :: zs),
                               list.no_confusion tl_eq
                                 (λ (a : 1 = y),
                                    eq.rec
                                      (λ (hsorted : sorted (1 :: zs)) (hle : (1.add 0).succ ≤ 1)
                                       (tl_eq : list.nil = zs),
                                         eq.rec
                                           (λ (hsorted : sorted [1]) (H_2 : _a == sorted.two_or_more hle hsorted),
                                              id_rhs ((1.add 0).succ ≤ 1) hle)
                                           tl_eq
                                           hsorted)
                                      a
                                      hsorted
                                      hle))
                            a
                            hle))
                  (eq.refl [2, 1])
                  (heq.refl _a))
               h)).symm.trans
           (eq_false_intro (of_as_true trivial)))).elim)
-/
