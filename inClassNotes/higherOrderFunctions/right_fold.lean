/-
The following examples have much in common

- Reducing a list of strings to a bool that indicates whether all of them have a given property
- Reducing a list of strings to a natural number that indicates the sum of all of their lengths

These are examples of the generalized concept of a right fold. Here are two simpler examples.

- Reduce a list of natural numbers to a natural number, by (1) applying a give binary operator
between the head of the list and the reduction (recursively) of the rest of the list; or in the
case where the list is empty, returning the identity for the given binary reduction operator.
- Reduce list of strings to a single string by "appending them all together", where that means
applying the binary append operation between each pair of elements, inserting the identity at 
the end of the list.

-/


/-

rfold string.append "" [ "Hello", ", ", "Lean", "!"] reduces to "Hello, Lean!" Here's how:

- rfold (++) "" [ "Hello", ", ", "Lean", "!"] 
- "Hello" ++ (rfold ++ "" [", ", "Lean", "!"]
- "Hello" ++ (", " ++ (rfold ++ "" ["Lean", "!"])
= "Hello" ++ (", " ++ ("Lean" ++ (rfold ++ "" ["!"])))
-/



/-
Return a result for the empty list otherwise apply head-map-and-combine-with-tail-reduction.
-/


universes u₁ u₂ u₃
def foldr 
  {α : Type u₁} 
  {β : Type u₃} 
  :
  β →             -- overall answer for list.nil
  (α → β → β) →   -- answer for head and tail reduced        
  (list α → β)    -- returns a list reducer
| b f list.nil := b
| b f (h::t) := f h (foldr b f t)


def blist := [tt, tt, ff, ff, tt, tt, tt, tt, ff]

#eval foldr tt band blist   -- bool → bool → bool
#eval foldr ff bor blist    --   α  →   β  → φ 


-- reduce list of strings to bool indicating whether any string is of even length
-- reduce list of strings to bool indicating whether all strings are of even length

-- used this to reduce string at head of list to a bool
def ev : string → bool := fun s, s.length % 2 = 0

/-
finally this function combines the rest of applying even to the string at the head 
of the list with the reduced value obtained recursively for the rest of the lsit. It
is from here the "rightness" of foldr comes. For empty, return identity. Otherwise
reduce head to a value and combine that value with the fold of the rest of the list.
-/

def all_even : string → bool → bool 
| h r := band (ev h) r  -- conjoin answer for head with answer for rest of list

def some_even : string → bool → bool 
| h t := bor (ev h) t

#eval foldr tt all_even ["Hello,", " Lean!"]

def mk_reducer
{α : Type u₁} 
{β : Type u₃} :
(α → β) → 
(β → β → β) → 
(α → β → β)
| hr rr := 
λ b, rr (hr b)


#eval foldr tt (mk_reducer ev band) ["Hello,", "Lean"]
#eval foldr ff (mk_reducer ev bor) ["Hello", "Lean!"]

def has_even_string : list string → bool :=
fun (l : list string), foldr ff (mk_reducer ev bor) l

def all_even_string : list string → bool :=
fun (l : list string), foldr tt (mk_reducer ev band) l

#eval has_even_string ["Hello,", "Lean!"]
#eval all_even_string ["Hello,", "Lean!"]

def append_all : list string → string :=
fun l, foldr "" string.append l

#eval append_all ["Hello,", "Lean!"]

/-
A PROBLEM REARS
-/

def all_even_string_bad : list string → bool :=
fun (l : list string), foldr ff (mk_reducer ev band) l
-- EXERCISE: What's the bug here? There is one.

