import topology.basic
import data.nat.prime
#check topological_space

open nat

-- clear id*

-- clear h₁ ... hₙ tries to clear each hypothesis hᵢ from the local context.

lemma two_is_prime : prime 2 :=
begin
  unfold prime,
  have h_two_le_two : 2 <= 2, from dec_trivial,
  -- have h0: ∀ (x: Prop), true ∧ x, from begin

  -- end
  trace_simp_set  only [h_two_le_two],
  -- simplification rules for iff
  -- [h_two_le_two] #0, 2 ≤ 2 ↦ true
  simp only [h_two_le_two],
  -- simp only [and.elim_right],
  type_check h_two_le_two, -- 2 <= 2
  trace_simp_set [h_two_le_two],
  trace (2+5), -- 7
  simp,
  introv h_m_mod_2_is_0,
  simp [(∣)] at h_m_mod_2_is_0,
  admit,
end

#print two_is_prime

lemma eq_2 : ∀ (m : ℕ), m = 2 → prime m :=
begin
  intros,
  rw a,
  exact two_is_prime,
end

#print eq_2
-- theorem eq_2 : ∀ (m : ℕ), m = 2 → m.prime :=
-- λ (m : ℕ) (a : m = 2), 
--   (id ((eq.refl m.prime).rec a)).mpr two_is_prime