/-
Source: https://primes.utm.edu/notes/proofs/infinite/euclids.html
Theorem.
  There are more primes than found in any finite list of primes
Proof.
  Call the primes in our finite list p_1, p_2, ..., p_r.
    Let P be any common multiple of these primes plus one 
  (for example P = p_1 * p_2 * ... * p_r + 1).
  Now P is either prime or it is not. If it is prime,
  then P is a prime that was not in out list.
  If P is not prime, then it is divisible by some prime, call it p.
  Notice p can not be any of p_1, p_2, ..., p_r, otherwise
  p would divide 1, which is impossible. 
    So this prime p is some prime that was not in our original list.
  Either way, the original list was incomplete.
-/

def prime' 