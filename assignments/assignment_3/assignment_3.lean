/-
HIGHER-ORDER FUNCTION WARMUP
-/

/-
1. Write a function, double, that takes
a natural number and returns its double.
Write it using the following recursive
definition:
- double 0 = 0
- double (n' + 1) = double n' + 2
-/


-- ANSWER HERE

def double : ℕ → ℕ
| nat.zero := nat.zero
| (nat.succ n) :=  (double n) + 2

#eval double 0 --> 0
#eval double 5 --> 5

/-
2. Write a function, map_list_nat, that
takes as its arguments (1) a list, l, of
natural numbers, and (2) a function, f,
from nat to nat, and that returns a new
list of natural numbers constructed by
applying f to each element of l. Make f
the first argument and l the second. The
function will work by case analysis and
recursion on l.
-/

-- ANSWER HERE

def map : Π { α : Type } { β : Type }, (α → β) → list α → list β
| _ _ _ [] := []
| _ _ f (x :: xs) := (f x) :: (map f xs)

def map_list_nat' : list ℕ → (ℕ → ℕ) → list ℕ :=
  λ lst, λ f, map f lst

def map_list_nat : list ℕ → (ℕ → ℕ) → list ℕ
| [] _ := []
| (x :: xs) f := (f x) :: (map_list_nat xs f)

#eval map_list_nat [1, 2, 3] nat.succ
#eval map_list_nat' [1, 2, 3] nat.succ

/-
3. Test your map_list_nat function by
applying it to several lists, both empty
and not, passing double as the function
value. Include [], [2], and [1,2,3] in
your set of test inputs and use comments
to document the expected return values.
-/

#eval map_list_nat [] double --> []
#eval map_list_nat [2] double --> [4]
#eval map_list_nat [1, 2, 3] double --> [2, 4, 6]

/-
4. In Lean, repr is an "overloaded"
function. When applied to a value of a
type for which it's defined (we'll see
later  how that happens) it returns a
string representation of the value. It
is defined for the nat type, and so
when applied to a nat value it returns
a corresponding string. It's "toString"
for Lean. Here's an example.
-/

#eval repr 5

/-
Write a function map_list_nat_string
that takes a list of nat values and
returns a list of strings in which
each nat in the given list has been
converted to a string using repr.
-/

-- ANSWER HERE

def map_list_nat_string : list ℕ → list string
| lst := map repr lst

#eval map_list_nat_string [1, 2, 3] --> ["1", "2", "3"]

/-
5. Write a function, filterZeros,
that takes a list of natural numbers
and returns the same list but with any
and all zero values removed. Given
[0], for example, it should return
[]; given [1,2,0,3,4,0, 0, 5] it
should return [1,2,3,4,5].
-/

-- ANSWER HERE

def filter : Π { α : Type }, (α → bool) → list α → list α
| _ _ [] := []
| _ f (x :: xs) :=
  if f x then
    filter f xs
  else
    x :: (filter f xs)

def filterZeros : list ℕ → list ℕ
| lst := filter (= 0) lst

#eval filterZeros [0] --> []
#eval filterZeros [1, 2, 0, 3, 4, 0, 0, 5] --> [1, 2, 3, 4, 5]

/-
6. Write a function, isEqN, that
takes a natural number, n, and returns
a function that takes a natural number,
m, and returns true (tt) if m = n and
that returns false (ff) otherwise. Be
sure to test your function.
-/

-- ANSWER HERE

def isEqN : ℕ → (ℕ → bool)
| n := λ m, m = n

#eval (isEqN 1) 2 --> ff
#eval (isEqN 1) 1 --> tt


/-
7.
Write a function filterNs that takes
a function, pred, from nat to bool
and a list, l, of natural numbers, and
that returns a list like l but with all
the numbers that satisfy the predicate
function removed. Test your function
using isEqN to produce a few predicate
functions (functions that for a given
argument return true or false).
-/

-- ANSWER HERE

def filterNs : (ℕ → bool) → list ℕ → list ℕ
| f lst := filter f lst

#eval filterNs (= 1) [0, 1, 1, 2, 1, 3] --> [0, 2, 3]
#eval filterNs (isEqN 1) [0, 1, 1, 2, 1, 3] --> [0, 2, 3]

/-
8. Write a function, iterate, that
takes as its arguments (1) a function,
f, of type nat → nat, and (2) a natural
number, n, and that returns a function
that takes an argument, (m : nat), and
that returns the result of applying f
to m n times. For example, if n = 3, it
should return f (f (f m)). The result
of applying f zero times is just m.
Hint: use case analysis on n, and
recursion. Test your function using
nat.succ, your double function, and
(nat.add 4) as function arguments.
-/

-- ANSWER HERE

def iterate : (ℕ → ℕ) → ℕ → (ℕ → ℕ)
| _ 0 := λ m, m
| f 1 := λ m, f m
| f (nat.succ n) := λ m, f (iterate f n m)

#eval (iterate nat.succ 0) 2    --> 2
#eval (iterate nat.succ 3) 2    --> succ (succ (succ 2)) --> 5
#eval (iterate double 2) 3      --> double (double 3) --> 12
#eval (iterate (nat.add 4) 1) 3 --> nat.add 4 3 --> 7
#eval (iterate (nat.add 4) 2) 1 --> (nat.add 4 ((nat.add 4) 1)) --> 9


/-
9. Write a function, list_add, that takes
a list of natural numbers and returns the
sum of all the numbers in the list.
-/

-- ANSWER HERE

def reduce : Π { α : Type }, (α → α → α) → α → list α → α
| _ f init [] := init
| _ f init (x :: xs) := f x (reduce f init xs)

#eval reduce (+) 0 [1, 2, 3, 4] --> 10

def list_add : list ℕ → ℕ := reduce (+) 0

#eval list_add [1, 2, 3, 4] --> 10

/-
10. Write a function, list_mul, that takes
a list of natural numbers and returns the
product of all the numbers in the list.
-/

def list_mul : list ℕ → ℕ := reduce (*) 1

#eval list_mul [1, 2, 3, 4] --> 24


/-
11. Write a function, list_has_zero, that
takes a list of natural numbers and returns
tt if the list contains any zero values and
that returns false otherwise. Use isEqN in
your solution. Test your solution on both
empty and non-empty lists including lists
that both have and don't have zero values.
-/

-- ANSWER HERE

def list_has_zero : list ℕ → bool :=
  λ lst,
    reduce (||) bool.ff (map (isEqN 0) lst)

#eval list_has_zero [1, 1, 1] --> ff
#eval list_has_zero [1, 0, 1] --> tt
#eval list_has_zero [0, 0, 0] --> tt


/-
12. Write a function, compose_nat_nat,
that takes two functions, f : ℕ → ℕ,
and g : ℕ → ℕ, and that returns a
function that takes a nat, n, and that
returns g (f n). Test your function
using at least nat.succ and double as
argument values.
-/

-- ANSWER HERE

def compose_nat_nat : (ℕ → ℕ) → (ℕ → ℕ) → (ℕ → ℕ)
| f g := λ n, g (f n)

#eval (compose_nat_nat nat.succ double) 2 --> (double (nat.succ 2)) --> 6
#eval (compose_nat_nat double nat.succ) 2 --> (nat.succ (double 2)) --> 5


/-
13. Write a polymorphic map_box function
of type

Π (α β : Type u),
  (α → β) → box α → box β

that takes a function, f, of type
(α → β), and a box, b, containing a
value of type α and that returns a
box containing that value transformed
by the application of f.
-/

-- ANSWER HERE
universe u
structure box (α : Type u) : Type u :=
(val : α)

def map_box : Π (α β : Type u), (α → β) → box α → box β
| _ _ f (box.mk expr) := box.mk (f expr)

#reduce map_box ℕ ℕ nat.succ (box.mk 1) --> box 2

/-
14.
Write a function, map_option, that
takes a function, f, of type α → β
and an option α and that transforms
it into an option β, where none goes
to none, and some (a : α) goes to
some b, where b is a transformed by
f.
-/

-- ANSWER HERE
def map_option : Π (α β : Type u), (α → β) → option α → option β
| _ _ _ option.none := option.none
| _ _ f (option.some a) := option.some (f a)

#eval map_option ℕ ℕ nat.succ option.none --> none
#eval map_option ℕ string repr (option.some 1) --> some "1"


/-
15. Write three functions, default_nat,
default_bool, and default_list α, each
taking no arguments (other than a type,
argument, α, in the third case), and
each returning a default value of the
given type: a nat, a bool, and a list.
Don't overthink this: Yes, a function
that takes no arguments is basically
a constant. You'll need to declare a
universe variable for the list problem.
-/

-- ANSWER HERE

def default_nat : ℕ := nat.zero
def default_bool : bool := bool.tt
def default_list : Π (α : Type u), list α
| _ := []
