---
title: Coinductive programming
---

Coinduction might sound like a scary thing involving lots of symbols and
proofs, but it is not necessary to go deep into the theoretical basis to use
it. From a practical perspective, coinduction is just a principled way to
program with infinite or cyclic structures such as streams and graphs in a
total language like Agda. Agda does allow you to define infinite lists, but you
have to be honest about their inclusion when defining the type. Coinduction is
precisely the way you can express that honesty.

This tutorial is divided into three parts:

1. Coinductive programming (this chapter)
2. Coinductive proving
3. Case studies and applications

We assume you already know the basics of how to use Agda, which you can learn
from the chapter *An introduction to Agda for Haskell programmers*.

```agda
{-# OPTIONS --guardedness #-}
module coinduction.Programming where

open import prelude.Prelude using
  (Nat; zero; suc; _+_; _*_; List; []; _::_; _×_; _,_; _≡_)

variable
  A B C : Set
  x y z : A
  f g h : A → B
  s s1 s2 : A
```

```agda
half : Nat → Nat
half zero          = zero
half (suc zero)    = zero
half (suc (suc n)) = suc (half n)

_∘_ : (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)
```

## Record types and copattern matching

Before we explain coinduction in Agda proper, we first need to understand the
foundations that it is built upon, which are record types and copattern
matching. First off, [record
types](https://agda.readthedocs.io/en/v2.8.0/language/record-types.html) in
Agda are just like we would expect from other languages: a type bundling a
number of *fields* into a single type. Apart from its fields, a record type can
also optionally be given a constructor.

For example, we define a type of rectangles with fields for the height and the
width:

```agda
record Rect : Set where
  constructor rect -- optional
  field
    height : Nat
    width  : Nat
```

To construct a value of a record type, we either use the `record { ... }` syntax
with named fields or use the constructor directly (if we declared one):

```agda
square : Nat → Rect
square x = record { height = x ; width = x }

square' : Nat → Rect
square' x = rect x x
```

We can access the fields of a record value by using the **projections**
`Rect.height` and `Rect.width`:

```agda
area : Rect → Nat
area r = Rect.height r + Rect.width r
```

To avoid having to write the name of the record type in front of each
projection, we *open* the record to bring projections into scope:

```agda
open Rect

perimeter : Rect → Nat
perimeter r = (2 * height r) + (2 * width r)
```

We can also use projections in *postfix* notation by starting their name with a
`.`:

```agda
rotate : Rect → Rect
rotate r = rect (r .width) (r .height)
```

Postfix notation is especially useful when working with nested record types
since we can stack them without any parentheses. Postfix notation is also
required when using the projection as a copattern in a pattern lambda (see
below).

One way to think about record types is as a single-constructor data type with
some syntactic sugar for the projections. However, there is a deeper and more
fruitful way of looking at record types as being dual to data types. Where data
types are defined by all the different ways of *constructing* an element, record
types are defined by all the possible *observations* we can make of an element.
To define a function that has a *data type* as an *input*, we should define it
for each of the *constructors* of the data type (this is *pattern matching*).
Dually, to define a function that has a *record type* as its *output*, we should
define it for each of the *projections* of the record type. This is called
[*copattern
matching*](https://agda.readthedocs.io/en/v2.8.0/language/copatterns.html).

Concretely, to define a function by copattern matching we just define what
should be the value of each of the projections applied to it. For example,
below we define `squash r` by the values of its projections `height (squash r)`
and `width (squash r)`:

```agda
squash : Rect → Rect
height (squash r) = half (height r)
width  (squash r) = 2 * width r
```

Copattern matching can also be used together with postfix projections:

```agda
squeeze : Rect → Rect
squeeze r  .height  = 2 * (r .height)
squeeze r  .width   = half (r .width)
```

Finally, copattern matching can also be used in a [pattern-matching
lambda](https://agda.readthedocs.io/en/v2.8.0/language/lambda-abstraction.html#pattern-lambda):

```agda
expand : Rect → Rect
expand r = λ where
  .height → 2 * r .height
  .width  → 2 * r .width
```

Since the lambda function itself is anonymous, there is nothing that the
projection can be syntactically applied to, so the use of postfix notation in
pattern lambdas is mandatory.

If the copattern notation does not yet make sense 100%, do not worry. There
will be many more examples once we define some coinductive record types.

## Coinductive record types

The simplest example of a [coinductive
type](https://agda.readthedocs.io/en/v2.8.0/language/coinduction.html) is the
type of *streams*, i.e. infinite lists of values of a given type. Concretely,
in Agda we define streams as a record type that consists of a **head** element
of type `A` and a **tail** which is another stream. Since the type `Stream`
occurs recursively in its own definition, we have to indicate to Agda whether we
want the type to only include finite values (`inductive`) or also infinite
values (`coinductive`). In this case, we want to include infinite streams, since
otherwise we would end up with an empty type.

```agda
module GuardedCoinduction where

  record Stream (A : Set) : Set where
    coinductive
    field
      head  : A
      tail  : Stream A
  open Stream
```

We use the projections to define functions on streams:

```agda
  firstTwo : Stream A → A × A
  firstTwo s = s .head , s .tail .head

  take : Nat → Stream A → List A
  take zero    s = []
  take (suc n) s = s .head :: take n (s .tail)

  drop : Nat → Stream A → Stream A
  drop zero     s  = s
  drop (suc n)  s  = drop n (s .tail)
```

If we have an existing stream we can use it to build new streams using the
`record` syntax:

```agda
  _::S_ : A → Stream A → Stream A
  x ::S xs = record { head = x ; tail = xs }

  _++_ : List A → Stream A → Stream A
  []       ++ ys = ys
  (x :: xs) ++ ys = x ::S (xs ++ ys)
```

However, if we try to define a new stream with a record constructor, Agda's
termination check fails:

```agda
  module BadZeroes where
    {-# NON_TERMINATING #-}
    zeroes : Stream Nat
    zeroes = record { head = 0 ; tail = zeroes }
```

There is actually a good reason why Agda rejects this definition: with it,
normalizing the expression `zeroes` will go into an infinite loop. Since Agda
needs to reduce terms during type checking, this would mean that Agda's type
checker could loop forever as well, which we would like to avoid.

To define a new stream, we have to use copatterns instead:

```agda
  zeroes : Stream Nat
  zeroes .head = 0
  zeroes .tail = zeroes
```

The expression `zeroes` only reduces when projections are applied to it, thus
there is no infinite loops created by this definition. The key point is that to
compute each consecutive value in the stream `zeroes`, we need an additional
application of `tail`. Hence Agda will only compute the stream for as far as we
have asked for.

We generalize the definition of `zeroes` to `repeat` a given value:

```agda
  repeat : A → Stream A
  repeat x .head = x
  repeat x .tail = repeat x
```

> **Exercise.** Define the `lookup` function on streams and prove that looking
> up any value in `repeat x` returns `x`:

```agda
  lookup : Stream A → Nat → A
  lookup xs n = {!!}

  lookup-repeat : (x : A) (n : Nat) → lookup (repeat x) n ≡ x
  lookup-repeat x n = {!!}
```

Just using copatterns is not sufficient to define a sensible stream, however.
For example, computing the second element of the stream `ones` defined below
loops forever:

```agda
  module BadOnes where
    {-# NON_TERMINATING #-}
    ones : Stream Nat
    ones .head = 1
    ones .tail = ones .tail
```

To avoid bad definitions such as this one, Agda requires that coinductive values
should be **productive**: applying any (finite) number of projections to them
should terminate. This is enforced by the **guardedness criterion**: every
(co)recursive call needs to appear

* in a clause with a copattern, *and*
* either at the top level or as the argument to one or more constructors.

(Side note: the Agda user manual does not have a proper specification of the
guardedness criterion, so this description may not be 100% correct.)

To use the guardedness criterion for productivity, we need to enable it
explicitly by using the `--guardedness` flag (e.g. by putting `{-# OPTIONS
--guardedness #-}` at the top of the file). The reason we have to enable it
explicitly is because Agda also provides an alternative way to check
productivity, namely *sized types*, that we discuss in the chapter *Sized
types*.

As another example, we define a `map` function on streams:

```agda
  map : (A → B) → Stream A → Stream B
  map f xs .head  = f (xs .head)
  map f xs .tail  = map f (xs .tail)
```

A counterexample to the guardedness criterion is the following definition of the
stream of natural numbers:

```agda
  module FailingNats where
    {-# TERMINATING #-}
    nats : Stream Nat
    nats .head = 0
    nats .tail = map suc nats
```

The recursive call to `nats` appears in an argument to the function `map` which
is not a constructor, so it fails the guardedness check. The problem with this
definition is that the guardedness checker does not look at the definition of
`map` so for all it knows it might not produce a value "in time" for the `nats`
definition to be productive. For example, if we used the following definition of
`map`, then `nats` would cease to be productive.

```agda
  map' : (A → B) → Stream A → Stream B
  map' f xs .head = f (xs .tail .head)
  map' f xs .tail = map f (xs .tail .tail)
```

We can assist the productivity checker by first defining the more general
`natsFrom` stream:

```agda
  natsFrom : Nat → Stream Nat
  natsFrom n .head = n
  natsFrom n .tail = natsFrom (suc n)

  nats : Stream Nat
  nats = natsFrom 0
```

Alternatively, we can use *sized types* to provide Agda with more information
about `map` (see the chapter *Sized types*).

> **Exercise.** Prove that the `lookup` function commutes with `map`:

```agda
  lookup-map : (i : Nat) → lookup (map f s) i ≡ f (lookup s i)
  lookup-map i = {!!}
```

> **Exercise.** When defining the stream of Fibonacci numbers, we run into a
> similar problem as with defining `nats`:

```agda
  zipWith : (f : A → B → C)
          → Stream A → Stream B → Stream C
  zipWith f xs ys .head = f (xs .head) (ys .head)
  zipWith f xs ys .tail = zipWith f (xs .tail) (ys .tail)

  module FailingFibonacci where
    {-# TERMINATING #-}
    fibonacci : Stream Nat
    fibonacci .head = 0
    fibonacci .tail .head = 1
    fibonacci .tail .tail =
      zipWith _+_ fibonacci (fibonacci .tail)
```

> A more general way to work around the limitations of syntactic guardedness is
> to use the `tabulate` function, which is the inverse to `lookup`. Implement
> `tabulate` and use it to define `fibonacci`.

```agda
  tabulate : (Nat → A) → Stream A
  tabulate f = {!!}

  fibonacci : Stream Nat
  fibonacci = {!!}
```

> **Exercise.** A stream can contain elements of any type, including the type of
> streams itself. We can think of a stream of streams as a two-dimensional
> matrix that is infinite in both directions. It is a fun exercise to implement
> a `transpose` function for infinite matrices and prove its defining property.
> You probably need the `lookup-map` property you used before. It might also be
> useful to use the equational reasoning syntax introduced in the chapter
> *Equational reasoning in Agda*.

```agda
  transpose : Stream (Stream A) → Stream (Stream A)
  transpose xss = {!!}

  transpose-flips-lookup
    : (xss : Stream (Stream A)) (i j : Nat)
    → lookup (lookup (transpose xss) i) j
      ≡ lookup (lookup xss j) i
  transpose-flips-lookup xss i j = {!!}
```

## Mixing induction and coinduction

Streams are a nice first example of a coinductive type, but they are also a bit
boring because they all have exactly the same structure, the only difference is
in the values. To define more interesting types with potentially infinite
values, we can mix induction and coinduction by mutually defining a data type
and a coinductive record type. For example, we define a type of potentially
infinite lists or *colists*:

```agda
  mutual
    data Colist (A : Set) : Set where
      []   : Colist A
      _::_  : A → Colist' A → Colist A

    record Colist' (A : Set) : Set where
      coinductive
      field
        force : Colist A
  open Colist' public
```

This pattern of defining a datatype together with a coinductive record with a
single field called `force` is quite common when defining coinductive types in
Agda.

We convert a list to a (finite) colist:

```agda
  fromList : List A → Colist A
  fromList []       = []
  fromList (x :: xs) = x :: record { force = fromList xs }
```

Despite the fact that `fromList` produces a colist, the reason why it passes the
Agda termination checker is because it is structurally recursive on the input
list. In other words, this function is defined by *induction*, not coinduction.

In contrast, converting a stream to an (infinite) colist needs to use a
copattern to make it pass the guardedness check:

```agda
  fromStream : Stream A → Colist A
  fromStream {A} xs = xs .head :: rest
    where
      rest : Colist' A
      rest .force = fromStream (xs .tail)
```

To make the definition a bit less verbose, we inline the definition of `rest` by
using a [**(co)pattern
lambda**](https://agda.readthedocs.io/en/v2.8.0/language/lambda-abstraction.html#pattern-lambda):

```agda
  fromStream' : Stream A → Colist A
  fromStream' {A} xs = xs .head ::
    (λ where .force → fromStream' (xs .tail))
```

Unfortunately, the syntactic noise of `λ where .force →` is not avoidable
because the guardedness criterion requires a copattern to appear syntactically
in the definition.

Another example of a mixed induction/coinduction is the type of co-natural
numbers, which is the type of regular Peano numbers plus infinity `∞`:

```agda
  mutual
    data Coℕ : Set where
      zero  : Coℕ
      suc   : Coℕ' → Coℕ

    record Coℕ' : Set where
      coinductive
      field force : Coℕ
  open Coℕ' public

  ∞ : Coℕ
  ∞ = suc λ where .force → ∞
```

> **Exercise.** Define the following functions:

```agda
  fromℕ : Nat → Coℕ
  fromℕ n = {!!}

  colength : Colist A → Coℕ
  colength xs = {!!}
```

A more substantial example of mixing induction and coinduction is the type of
streams of bits `Zero` and `One` that have infinitely many zeroes:

```agda
  data ZeroOne : Set
  record ZeroOne' : Set

  data ZeroOne where
    Zero_ : ZeroOne' → ZeroOne
    One_  : ZeroOne  → ZeroOne

  record ZeroOne' where
    coinductive
    field force : ZeroOne
  open ZeroOne' public
```

Since the recursive argument of the `One` constructor has type `ZeroOne` rather
than `ZeroOne'`, the constructor is considered to be inductive and hence it can
only be applied a finite number of times before we get another `Zero`
constructor.

## References

- Capretta (2013): *Wander types: A formalization of coinduction-recursion.*
- Kidney & Wu (2025): *Formalising Graph Algorithms with Coinduction.*
