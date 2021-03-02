import ..type_library.option

namespace hidden

-- concrete example
def map_option_nat_nat :
  (nat → nat) → 
  (option nat) → 
  option nat 
-- by case analysis on the option
| f option.none := option.none
| f (option.some v) := option.some (f v) 

-- almost the most general case

universes u₁ u₂

#check option

def map_option  
  {α : Type u₁}  
  {β : Type u₂} : 
  (α → β) → 
  (option α) → 
  option β 
| f option.none := option.none
| f (option.some v) := option.some (f v)

end hidden
