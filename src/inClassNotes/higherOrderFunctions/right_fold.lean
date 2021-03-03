
universes u₁ u₂ 

/-
The foldr function reduces a list α to a 
β value by applying a reducer function f
to (1) the (list head : α), and (2) the 
(result : β) of reducing the rest of the 
list to a result. 
-/
def foldr 
  {α : Type u₁} 
  {β : Type u₂} 
  :
  β →             
  (α → β → β) →       
  (list α → β)
| b f list.nil := b
| b f (h::t) := f h (foldr b f t) -- combine list head and reduction of rest

/-
The foldr function below takes a reducer
function as an argument. The function we
are currently considering, mk_reducer, 
builds these reducer functions from easy
to understand parts: (1) a function that
will convert the list head to a value that
will then be combined by (2) a function
that combines the converted value from the 
list head with the answer for the rest of
the list.
-/
def mk_reducer
{α : Type u₁} 
{β : Type u₂} :
(α → β) →       -- list head converter
(β → β → β) →   -- results combiner
(α → β → β)     -- reducer function
| hr rr := 
λ b, rr (hr b)