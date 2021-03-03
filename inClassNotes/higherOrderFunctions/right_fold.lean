-- NB: For in class notes, see right_fold_test.lean

universes u₁ u₂ u₃

def foldr 
  {α : Type u₁} 
  {β : Type u₂} 
  :
  β →             
  (α → β → β) →       
  (list α → β)
| b f list.nil := b
| b f (h::t) := f h (foldr b f t)

def mk_reducer
  {α : Type u₁} 
  {β : Type u₃} :
  (α → β) → 
  (β → β → β) → 
  (α → β → β)
| hr rr := λ b, rr (hr b)
