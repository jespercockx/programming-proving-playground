---
title: Stream processors
---

A *stream processor* describes how to transform a stream of `A`s into a stream
of `B`s:

```agda
{-# OPTIONS --guardedness #-}
module coinduction.case-studies.StreamProcessors where

open import solutions.Prelude using
  (Nat; zero; suc; _+_; List; []; _::_; _≡_; refl)
open import solutions.Coinduction using
  (Stream; take; nats; _~_; refl~)
open Stream
```

```agda
mutual
  data SP (A B : Set) : Set where
    get  : (A → SP A B)  → SP A B
    put  : B → SP' A B   → SP A B

  record SP' (A B : Set) : Set where
    coinductive
    field force : SP A B
open SP'
```

There can only be a finite number of `get`s before there must be a `put`.

## Example stream processor: summing elements pairwise

```agda
sum2by2 : SP Nat Nat
sum2by2 =
  get λ x →
  get λ y →
  put (x + y)
  λ where .force → sum2by2
```

## Running a stream processor

```agda
run : {A B : Set} → SP A B → Stream A → Stream B
run (get f)     xs = run (f (xs .head)) (xs .tail)
run (put y sp)  xs .head  = y
run (put y sp)  xs .tail  = run (sp .force) xs

sum2by2-nats :
  take 5 (run sum2by2 nats)
  ≡ (1 :: 5 :: 9 :: 13 :: 17 :: [])
sum2by2-nats = refl
```

## A slightly more interesting example

> **Question.** What does the stream processor below do?

```agda
mutual
  sums : SP Nat Nat
  sums = get λ n → sumN n 0

  sumN : Nat → Nat → SP Nat Nat
  sumN zero a = put a λ where .force → sums
  sumN (suc n) a = get λ k → sumN n (a + k)
```

Let's run it on `nats`!

## Composing stream processors

If we have a `SP A B` and a `SP B C`, we can apply them in sequence to a
`Stream A` to get a `Stream C`.

> **Exercise.** Do the same with a single processor:

```agda
compose : {A B C : Set} → SP A B → SP B C → SP A C
compose p1 p2 = {!!}

compose-correct :
  {A B C : Set} (p1 : SP A B) (p2 : SP B C) (s : Stream A) →
  run (compose p1 p2) s ~ run p2 (run p1 s)
compose-correct p1 p2 s = {!!}
```

## References

- Ghani, Hancock & Pattinson (2009): *Representations of stream processors using nested fixed points.*
