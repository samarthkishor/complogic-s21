universe u

@[class]  
structure has_mul_ident (α : Type u): Type (u+1) := 
(mul : α → α → α)

/-
Syntactic alternative:
class has_mul (α : Type u) := (mul : α → α → α)
-/


