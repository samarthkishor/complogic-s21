import ..semigroup.semigroup

/-
A monoid is a semigroup 
with an element 1 
such that 1 * a = a * 1 = a.
-/

universe u

@[class]
structure monoid (M : Type u) extends (semigroup M), (has_one M) : Type u :=
-- mul          -- from semigroup
-- mul_assoc    -- from semigroup
-- one          -- from has_one
(one_mul : ∀ (a : M), mul one a = a)    -- extended data
(mul_one : ∀ (a : M), mul a one = a)    -- extended data


