import algebra.group.basic

namespace hidden

universe u

/-
Our next topic is that of ad hoc polymorphism,
leading into generalized algebraic structures.
-/

/-
Let's start by discussing arithmetic addition
in a language such as C or Java. The salient
point here is that we can write expressions,
such as the follow, both of which use the +
operator, but that have different types.

1   + 1
1.0 + 1.0

The first plus really means "the plus function
defined for int values, while the second means
the plus function defined for floating points."

Yes, there really are two completely different
functions behind those two instances of the +
operator.

This example illustrates what we call ad hoc
polymorphism, specifically in this case what
we call "operator overloading". The term means
that the same operator name or symbol (here +)
is bound to different meanings depending on 
the types of the argument(s) to which it is
applied. The determination of which value to
bind it to is made statically (e.g., by a C++
compiler).

Overloading in this sense involves associating
a value (here a function value) with each of one
or more types (here int and floating point). In
our example, a floating_point_add function is
associated with the float type and integer_add
is associated with the int type. Now when the
compiler (or the "elaborator" in Lean) sees an
application of the overloaded operator, +, to 
arguments, it determines the type of argument 
and then *looks up the associated function value
and uses it in place of the overloaded operator.*
-/

/-
As a particularly simple example, suppose that
we want a unary operator, ident, to return a 
multiplicative identity value for any type for
which the operator is overloaded. For example, 
suppose we want this behavior:

#eval ident nat    -- expect 0
#eval ident bool   -- expect ff
eval ident string  -- expect ""
-/

/-
We could start simply by using what we now know
about dependent typing to get started. Here's a
structure, an instance of which will hold a type 
and a value *of that type*. We will then create 
one *instance* of this type for each of our three
cases above.
-/

structure has_mul_ident'' : Type (u+1) := 
(type : Type u)
(value : type)

def ident_bool'' : has_mul_ident'' := ⟨ bool, tt ⟩ 
def ident_nat'' : has_mul_ident'' := ⟨ nat, 0 ⟩

def getMeABool := ident_bool''.value
def getMeANat := ident_nat''.value

/-
Another way to write essentially the same definition
is by making the type *field* into a type *argument*.
-/

structure has_mul_ident' {type : Type u} : Type (u+1) := 
(value : type)

/-
Note that Lean is now inferring α, now an implicit argument 
-/
def has_mul_ident_bool' : has_mul_ident' := ⟨ tt ⟩ 
def has_mul_ident_nat' : has_mul_ident' := ⟨  0 ⟩

/-
Now when I need the system-wide default value for 
bools, I can access ident_bool.value. The 
same strategy goes for default values of the other
types for which the ident unary operator is 
overloaded/implemented).
-/

def getMeABool' := has_mul_ident_bool'.value
def getMeANat' := has_mul_ident_nat'.value

/-
This isn't bad, but wouldn't it be nice if I could
just say this instead?

def getMeABool := ident bool
def getMeAString := ident string
def getMeANat := ident nat

Now ident really does look like an overloaded
operator: given a "supported" type argument it returns
a corresponding value. The same operator/function symbol,
here ident, will have different implementations
depending on the type to which it is applied.

This is what typeclasses give us. We define a special
"class" structure just like the structure above, and
for each type to which the operator applies, just as
before, we define an instance of this structure. But
now, Lean will keep a database of these instances and
will look them up and return them to us whenever they
are needed to resolve overloaded operator applications.
-/


@[class]  -- annotate structure as typeclass
structure has_mul_ident (α : Type u): Type (u+1) := 
(value : α)

instance ident_bool : has_mul_ident bool := ⟨ tt ⟩ 
instance ident_nat : has_mul_ident nat := ⟨ 1 ⟩

/-
Lean now stores these definitions in a database and can 
recover them for us when we need them. And not only that
but it can do so implicitly! You can also therefore think
of typeclasses as supporting "implicit values". 
-/

--                    !instance query! 
def and_tt_with_ident [b : has_mul_ident bool] : bool :=
  band tt b.value

#eval and_tt_with_ident

/-
Viola: Typeclasses.

A typeclass is a polymorpic structure (type) builder. It is 
good to see it as taking a type argument, α, and then having
some additional data to go along with it. The type of the data
can of course depend on the type, α. That's just parametric
polymorphism. In our example, the type of value is the value
of the "type" field/argument.

A typeclass instance is a value of such a structure type. 
In our example, ident_nat, for example, is an instance
in which the value of the (lower case) type field/argument
is nat and the value of the value field is 0.

Typeclass inference is the process that Lean uses to find
a typeclass instance when needed. As a mathematician using
Lean, you will typically want it to do lookups implicitly.

such as ident, that defines an overloaded operator. The
instances of such a typeclass provide implementations 
of such an operator for different types of argument to
which it can be applied.  

In our simple example, the ident "operator" returns
a default value
-/
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



class has_mul (α : Type u) := (mul : α → α → α)

end hidden 


/-
class has_mul (α : Type u) := (mul : α → α → α)
-/


/-
@[protect_proj, ancestor has_mul] class semigroup (G : Type u) extends has_mul G :=
(mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
-/

#check @semigroup

universe u

@[class]
structure semigroup' (G : Type u) : Type u :=
(mul : G → G → G)
(mul_assoc : ∀ (a b c_1 : G), (a * b) * c_1 = a * b * c_1)

-- A semigroup is a type with an associative (*).

#check semigroup

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

axiom ev : nat → bool

inductive evdp : Σ (n : ℕ ), ev n → Type
| evdp_base : evdp ⟨ 0, ev 0 ⟩
| evdp_ind {n: ℕ} (evdpn : evdp n) : evdp ⟨ n+2, ev n+2 ⟩
