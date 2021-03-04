import algebra.group.basic

/-
@[class]
structure has_mul (α : Type u) := 
(mul:  α → α → α)
-/


#check [has_mul nat]
#check [has_mul bool]

#check has_mul
#check has_mul nat
#check has_mul bool



namespace hidden

universe u 

class has_mul (α : Type u) := (mul : α → α → α)



/-
A monoid is a semigroup 
with an element 1 
such that 1 * a = a * 1 = a.

@[class]
structure monoid (M : Type u) : Type u :=
(mul : M → M → M)
(mul_assoc : ∀ (a b c_1 : M), (a * b) * c_1 = a * b * c_1)
(one : M)
(one_mul : ∀ (a : M), 1 * a = a)
(mul_one : ∀ (a : M), a * 1 = a)
-/