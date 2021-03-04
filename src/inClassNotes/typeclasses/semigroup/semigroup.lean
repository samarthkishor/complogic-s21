universe u

/-
A semigroup is a set G with an associative multiplication operator, 
mul. Many differet sets G can be treated as semigroups, as long as
it comes with an associative binary multiplication operator, mul. 
-/

@[class]
structure semigroup (G : Type u) extends has_mul G : Type u :=
(mul_assoc : ∀ (a b c_1 : G), mul (mul a b) c_1 = mul a (mul b c_1))


#check semigroup

