import Mth299Lean


-- Rewrite tactic
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]


-- Rewrite exercises
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a]
  rw [mul_comm c a]


example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc a b]
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- Tactic exercises with no arguments
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [← mul_comm]
  rw [← mul_assoc]


-- Tactic exercises with one argument
example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [mul_comm a]
  rw [mul_comm a]
  rw [mul_assoc b]

-- Local context exercises
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a b c]
  rw [h]
  rw [← mul_assoc a e f]


example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [hyp']
  rw [mul_comm]
  rw [sub_self]
