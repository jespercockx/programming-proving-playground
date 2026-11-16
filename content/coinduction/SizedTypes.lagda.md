---
title: Sized types
---

```agda
{-# OPTIONS --sized-types #-}
module coinduction.SizedTypes where

open import prelude.Prelude using (Nat; zero; suc; List; []; _::_)

variable A B C : Set
```

The guardedness criterion has the advantage of being fairly simple and easy to
check, but we have also seen that it can be annoying and rule out natural
definitions of coinductive values. [**Sized
types**](https://agda.readthedocs.io/en/v2.8.0/language/sized-types.html) are an
alternative to the syntactic guardedness checker that annotates the size of
expressions in their types. They are enabled by putting `{-# OPTIONS
--sized-types #-}` at the top of our file (using `--guardedness` and
`--sized-types` together is inconsistent, see [issue
#1209](https://github.com/agda/agda/issues/1209) on the Agda bug tracker).

To use sized types, we should import the builtin module `Size` (or
`Agda.Builtin.Size` if you are not using the standard library):

```agda
module SizedCoinduction where
  open import Agda.Builtin.Size using (Size; Size<_; ∞)
  variable i : Size
```

The module `Size` provides:

* The type `Size : Set`
* The family of types `Size< i : Set` for every `i : Size`
* The size `∞ : Size`
* Some more operations on sizes that are not relevant here.

We can think of sizes as natural numbers extended with `∞`, but pattern matching
on sizes is not allowed. The type `Size< i` is similar to the `Fin n` type of
natural numbers less than `n`. A special property of these types is that we have
subtyping `Size< i <: Size` and `Size< i <: Size< j` when `i ≤ j`.

To make use of sizes, we should parametrize our coinductive types by a size
representing the number of observations we can safely make, i.e. the "depth"
until where the coinductive value has been defined. For example, we parametrize
a stream by its size:

```agda
  record Stream (A : Set) (i : Size) : Set where
    coinductive
    field
      head : A
      tail : {j : Size< i} → Stream A j
  open Stream
```

When taking the tail of a stream of size `i`, we should pick any size `j` that
is strictly smaller than `i` and we get a stream of that size.

When writing a function that takes a stream as *input* we usually assume that
the stream is already fully defined, which means we use size `∞`:

```agda
  take : Nat → Stream A ∞ → List A
  take zero    s = []
  take (suc n) s = s .head :: take n (s .tail)

  drop : Nat → Stream A ∞ → Stream A ∞
  drop zero     s = s
  drop (suc n)  s = drop n (s .tail)
```

On the other hand, when *defining* a new stream we should define it at an
arbitrary size `i`:

```agda
  zeroes : Stream Nat i
  zeroes .head  = 0
  zeroes .tail  = zeroes
```

We can understand this definition better by making all the implicit sizes
explicit:

```agda
  zeroes' : {i : Size} → Stream Nat i
  zeroes' {i} .head      = 0
  zeroes' {i} .tail {j}  = zeroes {j}
```

In the definition of `zeroes' {i} .tail`, we have to give a function of type `{j
: Size< i} → Stream Nat j`. Since `j < i`, the recursive call `zeroes {j}` is
made at a size strictly smaller than `i`, which is why it is accepted by Agda's
productivity checker for sized types.

Using sizes, we now give a more precise type to `map` that makes it clear that
it preserves the depth for which the stream is defined:

```agda
  map : (A → B) → Stream A i → Stream B i
  map f s .head = f (s .head)
  map f s .tail = map f (s .tail)
```

This allows us to give a direct definition of `nats` using `map`, showing that
sized types allow more definitions than the guardedness criterion:

```agda
  nats : Stream Nat i
  nats .head  = 0
  nats .tail  = map suc nats
```

> **Exercise.** Define `zipWith` for sized streams with the proper size
> annotations and use it to define `fibonacci` without using `tabulate`.

```agda
  zipWith : (A → B → C) → Stream A i → Stream B i → Stream C i
  zipWith f xs ys = {!!}

  fibonacci : Stream Nat i
  fibonacci = {!!}
```

This was just a basic introduction to sized types, we will see more examples
using them in parts 2 and 3 of this series.

Unfortunately, despite their appeal there is a whole list of issues with sized
types, or at least with their current implementation in Agda.

<details><summary>Long list of currently open issues with sized types in Agda</summary>

* First, as we have seen it takes additional work to annotate types and
  functions with sizes, and the resulting definitions are not compatible with
  Agda code that does not uses sized types because of the additional arguments.

* Second, Agda has a heuristic for assigning default values to implicit sizes
  if there are no constraints on them, but the current implementation of this
  heuristic is too eager, forcing us to give explicit values to sizes that
  should be inferrable (see issues
  [#992](https://github.com/agda/agda/issues/992),
  [#2439](https://github.com/agda/agda/issues/2439),
  [#2551](https://github.com/agda/agda/issues/2551), and
  [#2930](https://github.com/agda/agda/issues/2930)).

* Third, the fact that sized types make use of subtyping (which is not used in
  other parts of Agda aside from the rarely-used `--cumulativity` flag) also
  causes a number of spurious errors (see issues
  [#1579](https://github.com/agda/agda/issues/1579),
  [#2409](https://github.com/agda/agda/issues/2409),
  [#2440](https://github.com/agda/agda/issues/2440), and
  [#3039](https://github.com/agda/agda/issues/3039)).

* Third, there are several other cases where the termination/productivity checker for sized
  types is more restrictive than it should be,
  though there is not a clear pattern as far as I can tell (see issues
  [#300](https://github.com/agda/agda/issues/300),
  [#1515](https://github.com/agda/agda/issues/1417),
  [#1869](https://github.com/agda/agda/issues/1869),
  [#1894](https://github.com/agda/agda/issues/1894),
  [#2041](https://github.com/agda/agda/issues/2041),
  [#2098](https://github.com/agda/agda/issues/2098),
  [#2331](https://github.com/agda/agda/issues/2331),
  [#2651](https://github.com/agda/agda/issues/2651), and
  [#2903](https://github.com/agda/agda/issues/2903)).

* Fourth, there are some examples that make Agda's type checker loop in the
  presence of sized types (see issues
  [#1417](https://github.com/agda/agda/issues/1417),
  [#1428](https://github.com/agda/agda/issues/1428),
  [#1523](https://github.com/agda/agda/issues/1523),
  [#3144](https://github.com/agda/agda/issues/3144), and
  [#4376](https://github.com/agda/agda/issues/4376)).

* Finally and most worryingly, there are several known inconsistencies in the
  current implementation of sized types, most (but not all) follow from the
  fact that Agda considers `∞` to be strictly smaller than itself (see issues
  [#1201](https://github.com/agda/agda/issues/1201),
  [#1946](https://github.com/agda/agda/issues/1946),
  [#2820](https://github.com/agda/agda/issues/2820),
  [#3026](https://github.com/agda/agda/issues/3026),
  [#6002](https://github.com/agda/agda/issues/6002), and
  [#7178](https://github.com/agda/agda/issues/7178)).

It has been prophesized that one day we
will get a new implementation of sized types that avoids these issues (or at
least the most severe ones). Great honor will be bestowed on the one
implementing this. We also pay our respect to the heroes who have fallen on
their [quest for this holy grail](https://github.com/agda/agda/pull/7152).
</details>

While it is unlikely that you run into these issues when using sized types in
the "intended" way, this state of affairs is not ideal and has naturally
hindered the adoption of sized types.

In the mean time, Isaac Elliott has a great blog post on [Sized types and
coinduction in Safe Agda](https://blog.ielliott.io/sized-types-and-coinduction-in-safe-agda)
where he shows a way to "fake" sized types without using the `--sized-types`
flag. While you lose some convenience such as subtyping and heuristics for
inferring sizes, it could be a good alternative if you want to use a kind of
sized types in the `--safe` fragment of Agda.

## References

- Abel & Pientka (2016): *Well-founded recursion with copatterns and sized types.*
