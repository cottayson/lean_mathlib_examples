namespace hidden

/-
bᵢ is Elementary braid, it is a crossing of two ropes i_th rope and (i+1)_th rope:
  bᵢ is counterclockwise crossing (if look from up (begining) to down (ending of braid))
  bᵢ⁻¹ is clockwise crossing

Properties of braid group:
G1. Associativity: ∀ a b c, a ∘ (b ∘ c) = (a ∘ b) ∘ c
G2. Identity: ∃! e, ∀ a, a ∘ e = e ∘ a = e
G3: Inverse: ∀ a, ∃! x, a ∘ x = x ∘ a = e
1. Trivial: bᵢ⁻¹ bᵢ = bᵢ bᵢ⁻¹ = e
2. Distant commutativity: if |i-j| > 2 then bᵢ bⱼ = bⱼ bᵢ
3. Relation of Artin: bᵢ bᵢ₊₁ bᵢ = bᵢ₊₁ bᵢ bᵢ₊₁

Example:
b₃⁻¹ (b₂ b₃ b₂) b₃⁻¹ =
[by Artin relation]
(b₃⁻¹ b₃) b₂ (b₃ b₃⁻¹) =
[by Trivial]
e b₂ e =
[by id: λ x, e x = x]
b₂
-/



constant β : Type
constant b : ℤ → (β → β)
constant e : β → β
constant zero : β

namespace braid

-- we have assoc from assoc of functions β → β
axiom id (x : β) : e x = x
axiom b_zero : b 0 = e
axiom trivial (i : ℤ) (x : β) : b (-i) (b i x) = e x
axiom dist_comm (i j : ℤ) (x : β) :
  abs (i - j) >= 2 → b i (b j x) = b j (b i x)

attribute [simp] id trivial
variable x : β

example : (b (-2)) (b 2 x) = e x :=
begin
  
end

end braid




end hidden


