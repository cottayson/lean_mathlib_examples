
namespace inequality_example
-- http://wwwf.imperial.ac.uk/~buzzard/xena/natural_number_game/?world=9&level=1
theorem mul_pos (a b : nat) : a ≠ 0 → b ≠ 0 → a * b ≠ 0 :=
begin
  intros ha hb,
  simp at ha hb,
  -- letσ name this goal state with state_A
  by_cases b = 0,
    { contradiction, },
    { 
      clear h, 
      -- goal state is state_A => wrong way to prove
      sorry,
    },
  /-
    ha : a ≠ 0
    hb : b ≠ 0

    (let a = 0 => a * b = 0 * b = 0 => contradiction with a * b ≠ 0) => a ≠ 0
    analogically for b:
    let's define some function:
      define proof a b = let a = 0 => a * b = 0 * b = 0 => contradiction with a * b ≠ 0
    proof b a => b ≠ 0
    
  -/
end

end inequality_example