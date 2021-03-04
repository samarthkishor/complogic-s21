#check @semigroup

universe u

@[class]
structure semigroup' (G : Type u) : Type u :=
(mul : G → G → G)
(mul_assoc : ∀ (a b c_1 : G), (a * b) * c_1 = a * b * c_1)

-- A semigroup is a type with an associative (*).

#check semigroup

