namespace hidden

variables {a b c d : Prop}

lemma neq_of_not_iff {a b : Prop} : ¬(a ↔ b) → a ≠ b :=
λ h₁ h₂,
have a ↔ b, from eq.subst h₂ (iff.refl a),
absurd this h₁

lemma not_iff_not_of_iff (h₁ : a ↔ b) : ¬a ↔ ¬b :=
iff.intro
 (assume (hna : ¬ a) (hb : b), hna (iff.elim_right h₁ hb))
 (assume (hnb : ¬ b) (ha : a), hnb (iff.elim_left h₁ ha))

lemma of_iff_true (h : a ↔ true) : a :=
iff.elim_left (iff.symm h) trivial

example (h : a) (h2 : b): (a ↔ a) ∨ b :=
begin
  apply or.elim (λ h3, _) _,
end

@[symm]
lemma iff.symm (h : a ↔ b) : b ↔ a :=
iff.intro (iff.elim_right h) (iff.elim_left h)

example : a ↔ a := iff.intro id id

example : id a = a := id.def a
example : id a = a := rfl
example : id a = a := @rfl Prop a

example (n : ℤ): abs n = abs n :=
begin
  apply abs_by_cases,
  apply abs_neg n,
end

#check @abs_neg

lemma iff.comm : (a ↔ b) ↔ (b ↔ a) :=
iff.intro iff.symm iff.symm

set_option trace.simplify.rewrite true

lemma of_iff_true' (h : a ↔ true) : a :=
begin
  have step1 := h.symm,
  have step2 := iff.mp step1,
  show a, from step2 trivial,
    -- rw true_implies_iff at step2,
    -- exact step2,
end

#print of_iff_true'
-- λ {a : Prop} (h : a ↔ true), 
-- eq.mp ( (eq.refl (true → a)).rec (propext (true_implies_iff a)) ) h.symm.mp

lemma true_imp : (true → a) → a :=
begin
  rw true_implies_iff,
  exact id,
end

#print true_imp
-- λ {a : Prop}, 
-- (id ((eq.refl ((true → a) → a)).rec (propext (true_implies_iff a)))).mpr id

lemma true_imp' : (true → a) → a :=
begin
  type_check propext true_implies_iff,
  assume h,
  rw true_implies_iff at h,
  exact h,
end

#print true_imp'
-- λ {a : Prop} 
-- (h : true → a), eq.mp ((eq.refl (true → a)).rec (propext (true_implies_iff a))) h
@[simp] theorem true_implies_iff' (α : Prop) : (true → α) ↔ α :=
iff.intro (λ h, h trivial) (λ h h', h)

lemma true_imp'' : (true → a) → a :=
begin
  assume h,
  apply h,
  exact true.intro,
end

#print true_imp'' -- λ {a : Prop} (h : true → a), h true.intro


lemma not_of_iff_false : (a ↔ false) → ¬a := λ h, iff.mp h -- ~ iff.mp

lemma iff_true_intro (h : a) : a ↔ true :=
iff.intro
  (λ hl, trivial)
  (λ hr, h)

lemma iff_true_intro' (h : a) : a ↔ true := by {
  apply iff.intro,
    assume hl : a, trivial,
    assume _, exact h,
}

example : ∀ (h : a), a ↔ true := iff_true_intro -- λ h, iff_true_intro h
example : ∀ (a : Prop), a → (a ↔ true) := λ _, iff_true_intro -- λ a h, iff_true_intro h

lemma ex1 : a → (a ↔ true ↔ true ↔ true ↔ true ↔ true) :=
begin
  assume ha,
  repeat { apply iff_true_intro },
  exact ha,
end

#print ex1

lemma ex1' : a → (a ↔ true ↔ true ↔ true ↔ true ↔ true) :=
  λ ha, by {repeat {apply iff_true_intro}, exact ha}

#print ex1'

end hidden