---
title: Dependent types
---

```agda
{-# OPTIONS --allow-unsolved-metas #-}
module notes.DependentTypes where

open import solutions.Prelude hiding (Σ)
```

Dependent types are types that can refer to --- or *depend on* ---
parts of a program. With dependent types, it is possible to write much
more precise types than in other non-dependent type systems. In
particular, dependent types can be used to encode invariants of our
programs directly into their types, so the type checker can ensure
that they are never broken. In this section we will look into how we
can use dependent types in Agda and why they can be useful.

## Vectors: lists that know their length

The prototypical example of a dependent type is the type of
*vectors* `Vec A n`. This type contains lists of exactly n
elements of type A. For example:

```agda
data Vec (A : Set) : Nat → Set where
  []    : Vec A 0
  _::_  : {n : Nat} → A → Vec A n → Vec A (suc n)

infixr 5 _::_

myVec1 : Vec Nat 5
myVec1 = 1 :: 2 :: 3 :: 4 :: 5 :: []

myVec2 : Vec (Bool → Bool) 2
myVec2 = not :: (λ x → x) :: []

myVec3 : Vec Nat 0
myVec3 = []
```

> **Overloading of constructors.**  Agda allows us to use
> the same name for the constructors of different datatypes, for example
> `[]` can be a constructor of both `List` and `Vec`.

In fact, the length n does not have to be a literal number, but it
can be any expression of type `Nat`. So we might as well have written
`Vec Nat (2 + 3)` instead of `Vec Nat 5`.

In a dependently typed language, the return type of a function is
allowed to depend on the inputs of the function. For example, we can
implement a function `zeroes` that takes as input a number n,
and produces a vector of zeroes of length n:

```agda
zeroes : (n : Nat) → Vec Nat n
zeroes zero     = []
zeroes (suc n)  = 0 :: zeroes n
```

The type `(n : Nat) → Vec Nat n` is called a *dependent
  function type* (a.k.a. a Π type) because the type of the output
depends on the input. Note that the type of the result changes
depending on which clause of the definition we are in: in the first
clause, the input is `zero` so the output must have type
`Vec Nat zero`, while in the second clause the input is `suc n`
so the output must have type `Vec Nat (suc n)`.

> **Exercise.** Implement the function
>   `downFrom : (n : Nat) → Vec Nat n` that, given a number
>   n, produces the vector
>   `(n-1) :: (n-2) :: … :: 0 :: []`. (You'll need to copy
>   the definition of the `Vec` type below to test if your definition
>   typechecks.)

```agda
downFrom : (n : Nat) → Vec Nat n
downFrom n = {!!}
```

We can also define functions where the type of one of the arguments
depends on a previous input. For example:

```agda
prepend : (n : Nat) → Bool
        → Vec Bool n → Vec Bool (suc n)
prepend n b bs = b :: bs
```

In fact, this is just a special case of the dependent function type,
thanks to currying: the type of `prepend` can equivalently be
written as `(n : Nat) → (Bool → Vec Bool n → Vec Bool (suc n))`.

If an argument to a function appears in the type of a later argument,
we can make it implicit by using curly braces ``:

```text
prepend : {n : Nat} → Bool
        → Vec Bool n → Vec Bool (suc n)
prepend b bs = b :: bs
```

This allows us for example to write
`prepend true (false :: [])` instead of
`prepend 1 true (false :: [])`. Here Agda infers
automatically from the length of the vector `false :: []` that
n must be `1`.

Note that dependent function types use the same syntax as polymorphic
function types. This is no coincidence: in Agda, polymorphic functions
are just a special case of dependent functions where the argument is
of type `Set`.

Let us now take a closer look at the `Vec` type[^1]
itself. It is defined as follows:

```text
data Vec (A : Set) : Nat → Set where
  []    : Vec A 0
  _::_  : {n : Nat} → A → Vec A n → Vec A (suc n)
infixr 5 _::_
```

> **Parameters vs. indices.**
> You might wonder why the argument `(A : Set)` appears *before*
> the colon in the definition of `Vec`, while the argument type `Nat`
> appears after it. The reason for this is that A is a
> *parameter*, while the argument of type `Nat` is an *index*
> of the datatype. The main difference is that a parameter is bound once
> for the whole definition and must occur uniformly in the return types
> of the constructors --- i.e. the return type of each constructor must
> be of the form `Vec A …` --- while each constructor determines
> the value of the index individually.

Just like `List`, `Vec` has two constructors `[]` and
`_::_`. The main difference lies in the *type of the
datatype*: it is no longer `Set` but instead `Nat → Set`,
indicating that it takes one additional argument of type `Nat`. This
argument is called an *index*, and correspondingly `Vec` is
called an *indexed datatype*. This is reflected in the types of
the constructors: `[]` constructs a vector of length `0`, while
`_::_` takes arguments of type A and `Vec A n` and
constructs a vector of length `suc n`, where n is an implicit
argument of the constructor.

We can define functions on `Vec` just like we did for `List`, by
pattern matching on the constructors. For example, we can define
concatenation of vectors as follows:

```agda
_++Vec_ : {A : Set} {m n : Nat}
        → Vec A m → Vec A n → Vec A (m + n)
[]         ++Vec ys  = ys
(x :: xs)  ++Vec ys  = x :: (xs ++Vec ys)
```

Pay close attention to the return type `Vec A (m + n)` of this
function: it depends on both m and n!

So far the length index of `Vec` has allowed us to make the types of
operations on lists more precise, but it hasn't really done anything
we couldn't have done in Haskell. So let's try something a bit more
ambitious and implement a function `head` that *only*
accepts arguments of length at least one.

```agda
head : {A : Set}{n : Nat} → Vec A (suc n) → A
head (x :: xs) = x
```

Note that this definition does not include a case for the empty vector
`[]`. Yet it is still accepted by the coverage checker of Agda! This
is a good thing: the empty vector `[]` does not have type
`Vec A (suc n)`, so any clause of the form `head [] = …` would be ill-typed. By restricting the type of the input, we
have avoided the need to define a case for `[]`, while in Haskell we
would either end up with an incomplete definition or be forced to use
`error` or `undefined`.

> **Exercise.** Implement the function `tail : {A : Set} {n : Nat} → Vec A (suc n) → Vec A n`.

```agda
tail : {A : Set} {n : Nat} → Vec A (suc n) → Vec A n
tail xs = {!!}
```

> **Exercise.** Implement the function `dotProduct : { n : Nat } → Vec Nat n → Vec Nat n → Nat` that calculates
> the "dot product" (or scalar product) of two vectors. Note that the
> type of the function enforces the two vectors to have the same length!

```agda
dotProduct : {n : Nat} → Vec Nat n → Vec Nat n → Nat
dotProduct xs ys = {!!}
```

## Looking up elements of a vector with the `Fin` type

One important operation on lists is looking up the element at a given
position. In Haskell, this is implemented by the function
`(!!) :: [a] -> Int -> a`. However, this is a partial function:
if the position[^2] is too big (or
negative) the function will throw an error. Since throwing errors is
not allowed in Agda, we are forced to give it the type
`{A : Set} → List A → Nat → Maybe A`, and return
`nothing` in case the position is out of range. However, we can do
better by using `Vec` instead of `List` and requiring the position to
be in range of the vector. To make this work, we introduce a new type
`Fin n` of *finite sets*. This type consists of all natural
numbers less than n, i.e. the numbers `0,1,2,…,(n-1)`.

As an example, the type `Fin 3` contains three elements:

```agda
data Fin : Nat → Set where
  zero  : {n : Nat} → Fin (suc n)
  suc   : {n : Nat} → Fin n → Fin (suc n)

zero3 : Fin 3
zero3 = zero

one3 : Fin 3
one3   = suc zero

two3 : Fin 3
two3   = suc (suc zero)
```

However, if we try to define `three3 : Fin 3` as
`suc (suc (suc zero))`, we get an error:

```text
(suc _n_112) != zero of type Nat
when checking that the expression zero has type Fin 0
```

Without immediately going into the full details of this error message,
we can already infer that Agda does not allow us to
define `suc (suc (suc zero))` as an element of `Fin 3`.

The type `Fin 0` in particular
contains *zero* arguments: it is an *empty type*.
This makes sense as we want to use `Fin n` as a position
in a vector of length n, and there are no valid positions
in a vector of length `0`. Empty types will take an important role once
we start using Agda as a proof assistant in the next section.

Recall the definition of `Fin` given above.

The constructor `zero` constructs
an element of type `Fin (suc n)` for any n,
while `suc` constructs a new element of type `Fin (suc n)` for each element of type `Fin n`.
In particular, there is no way
to construct an element of type `Fin 0`.
For type `Fin 1` the only possible constructor is `zero`, since
using `suc` would require us to give an element of type `Fin 0`.

```text
                                                                suc (suc (suc zero))
                                                suc (suc zero)  suc (suc zero)
                                suc zero        suc zero        suc zero
                zero            zero            zero            zero
Fin 0           Fin 1           Fin 2           Fin 3           Fin 4
```

*We can visualize the family of `Fin` types as an (infinite) triangle,
where each type other than `Fin 0` has an element `zero`, and each type also
has all elements of the form `suc x` where x belongs to the *previous*
type in the family.*

For now, let us define a safe variant of the `lookup` function
using `Vec` and `Fin`. Here is the type signature:

```agda
lookupVec : {A : Set} {n : Nat} → Vec A n → Fin n → A
lookupVec xs i = {!!}
```

Notice that the length n of the vector is also used as the upper
bound for the position: this way we enforce that the position really is in
range of the vector. We then split on the vector `xs` using `Ctrl+c Ctrl+c`.

Something interesting has happened: there is only a case for
`x :: xs`, but not for `[]`. Agda has noticed
based on the type of the `lookupVec` function that the function
can never be called with argument `[]`, so the case can safely
be skipped.[^3]

We can now split on the position i.

Since the length of the vector `x :: xs` is `suc n`,
we get cases for both constructors of `Fin`.
Finally, we can complete the definition of `lookupVec` by
filling in the remaining two holes the same way as we would have done
for the unsafe lookup function in Haskell.

Thanks to the power of dependent types, we have managed to implement a
*safe* and *total* version of the lookup function, without
having to change the return type in any way.

> **Exercise.** Implement a function `putVec : { A : Set } { n : Nat } → Fin n → A → Vec A n → Vec A n` that
> sets the value at the given position in the vector to the given value,
> and leaves the rest of the vector unchanged.

```agda
putVec : {A : Set} {n : Nat} → Fin n → A → Vec A n → Vec A n
putVec i x xs = {!!}
```

## The dependent pair type

Another important type for programming with dependent types is called
the Σ type or the *dependent pair
type*. It can be seen as a generalization of the normal pair type
`A × B` where the type of the second component can be different
depending on the value of the first component. For example, the type
`Σ Nat (Vec Bool)` (or equivalently,
`Σ Nat (λ n → Vec Bool n)`) contains the
elements `2 , (true :: false :: [])` and
`0 , []` but not `2 , []` (since `[]` does not
have type `Vec Bool 2`). In general, this type consists of pairs
`m , xs` where `m : Nat` and `xs : Vec Bool m`. [^4]

We can define the type `Σ` of dependent pairs as follows: [^5]

```agda
data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B
```

Note that the second parameter of `Σ` is not just a type in
`Set` but a *function* of type `A → Set`, i.e. a dependent type.

We can see that `Σ` is indeed a generalization of the normal
pair type where the type of the second component ignores its input: [^6]

```agda
_×'_ : (A B : Set) → Set
A ×' B = Σ A (λ _ → B)
```

> **Exercise.** Implement functions converting back and forth
> between `A × B` and `A ×' B`.

We have the following functions for getting the individual components
of a dependent pair:

```agda
fstΣ : {A : Set}{B : A → Set} → Σ A B → A
fstΣ (x , y) = x

sndΣ : {A : Set}{B : A → Set} → (z : Σ A B) → B (fstΣ z)
sndΣ (x , y) = y
```

Note that return type of `sndΣ` depends on the result of the
first component `fstΣ`.

An important use of the `Σ` type is to *hide* some of
the information in a type when it is not relevant. For example, we can
hide the length of a vector by pairing it up with its length:

```agda
List' : (A : Set) → Set
List' A = Σ Nat (Vec A)
```

> **Exercise.** Implement functions converting back and forth
> between `List A` and `List' A`.
> **Hint.** First define the functions `[]' : {A : Set} → List' A` and `_::'_ : {A : Set} → A → List' A → List' A`.

## Section summary

-  A dependent type is a family of types that is indexed over
values of a base type. For example, `Vec A n` is a dependent type
indexed over natural numbers `n : Nat`.
-  A dependent function is a function where the type of the
output depends on the value of the input. For example, `zeroes : (n : Nat) → Vec Nat n` is a dependent function.
-  We can define new dependent types as *indexed datatypes*,
which are datatypes of type `I → Set`. Each constructor of an
indexed datatype must determine what index it targets. For example,
the constructor `[]` targets the type `Vec A 0` with
index `0`.
-  When pattern matching on an indexed datatype, it is allowed to
omit constructors that can be determined to be impossible based on
their type. For example, the function `head` takes an argument
of type `Vec A (suc n)` so it does not require a case for
the empty vector `[]`.
-  When a type has no possible constructors, we can (often)
  safely skip cases that take an argument of this type. For example,
  we can skip the case for `[]` in `lookupVec` since `Fin zero`
  is empty.
-  The dependent pair type `Σ A B` consists of pairs
`(x,y)` where `x : A` and `y : B x`.

[^1]: Technically, `Vec` is not a type but a *family* of types `Vec A n`. This is also the case for other indexed datatypes we will see later.
[^2]: The position in a vector is often called an index, but we will refrain from calling it that to avoid confusion with the concept of an index for an indexed datatype.
[^3]: More precisely, the way Agda figures this out is as follows: in order for the input to be `[]`, the number `n` has to be `zero`. But if `n` is `zero`, then `i` has type `Fin zero`. Agda then checks all constructors of the `Fin` type, and sees that none of them can be used to construct an element of type `Fin zero`. Hence the case where the input vector is `[]` is really impossible.
[^4]: The dependent pair type is also called the Σ type because it can be seen as a *sum* (or disjoint union) of all the types `B x`, where we view the first component as a label indicating which type of the family the second component belongs to.
[^5]: To write Σ, type `\Sigma`.
[^6]: This definition defines `A ×' B` to be a *type alias* for `Σ A (λ_ → B)`.
