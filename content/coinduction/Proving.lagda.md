---
title: Coinductive proving
---

This chapter continues the treatment of coinduction with a look at how to state
and prove properties of coinductive structures. It builds on the definitions
from the chapter *Coinductive programming*.

```agda
{-# OPTIONS --guardedness #-}
module coinduction.Proving where

open import prelude.Prelude using
  (Nat; zero; suc; _+_; _*_; List; []; _::_; _≡_; refl; sym; trans; cong;
   ⊥; absurd)
open import prelude.Coinduction using
  (Stream; take; drop; _++_; Colist; Colist'; fromList; fromStream; []; _::_)
open Stream
open Colist'

¬_ : Set → Set
¬ P = P → ⊥
```

## Properties of coinductive types

### Finite colists

`Finite` is an *inductive* predicate on a (mixed) coinductive type:

```agda
module FiniteInfinite where
  data Finite {A : Set} : Colist A → Set where
    []   : Finite []
    -::_  : {x : A} {xs : Colist' A}
         → Finite (xs .force) → Finite (x :: xs)

  fromListFin : {A : Set} (xs : List A) → Finite (fromList xs)
  fromListFin []        = []
  fromListFin (x :: xs)  = -:: fromListFin xs
```

### Converting back to a list

We can convert a finite colist back to a list:

```agda
  toList : {A : Set} (xs : Colist A) → Finite xs → List A
  toList []        []        = []
  toList (x :: xs)  (-:: fin)  = x :: toList (xs .force) fin
```

This function uses induction: it is structurally recursive on the proof that the
colist is finite, not on the colist itself.

> **Exercise.** Prove that converting a list to a colist and back is the
> identity:

```agda
  fromListInv : {A : Set} (xs : List A)
    → toList (fromList xs) (fromListFin xs) ≡ xs
  fromListInv xs = {!!}
```

### Infinite colists

`Infinite` is a *coinductive* predicate on colists:

```agda
  mutual
    data Infinite {A : Set} : Colist A → Set where
      -::_ : {x : A} {xs : Colist' A}
           → Infinite' xs → Infinite (x :: xs)

    record Infinite' {A : Set} (xs : Colist' A) : Set where
      coinductive
      field force : Infinite (xs .force)
  open Infinite' public
```

> **Exercise.** Prove that `fromStream` always produces an infinite colist.

```agda
  fromStreamInf : {A : Set} (xs : Stream A) → Infinite (fromStream xs)
  fromStreamInf xs = {!!}
```

### Converting back to a stream

> **Exercise.** Implement the following function:

```agda
  toStream : {A : Set} (xs : Colist A) → Infinite xs → Stream A
  toStream xs inf = {!!}
```

What should the function do in the case of an empty colist?

This function uses coinduction: it is defined by copattern matching on the
resulting stream.

### Finite or infinite?

> **Question.** Can we prove the following?

```text
  finite-or-infinite : {A : Set} (xs : Colist A) → Either (Finite xs) (Infinite xs)
```

No, but we can prove this instead:

```agda
  infinite-not-finite : {A : Set} {xs : Colist A}
                      → Infinite xs → ¬ (Finite xs)
  infinite-not-finite inf fin = {!!}

  not-finite-infinite : {A : Set} {xs : Colist A}
                      → ¬ (Finite xs) → Infinite xs
  not-finite-infinite nf = {!!}
```

where `¬ P = P → ⊥`.

> **Exercise.** Prove these two implications.

## Bisimulation

Let's prove an equality on streams:

```text
  takeDrop  : {A : Set} (n : Nat) (s : Stream A) → take n s ++ drop n s ≡ s
  takeDrop zero s = refl
  takeDrop (suc n) s = {! cong (s .head ::S_) ? !}

-- Agda reports:
--   s .head ::S _y_296 != s
```

Streams are coinductive, but the identity type is *inductive*: Agda needs to
"see" both sides are equal in a finite number of steps.

We need a *coinductive* relation instead:

```agda
module GuardedBisimulation where
  record _~_ {A : Set} (s1 s2 : Stream A) : Set where
    coinductive
    field
      head  : s1 .head ≡ s2 .head
      tail  : s1 .tail ~ s2 .tail
  open _~_ public
```

Proving bisimulation is just defining a coinductive value of the right type:

```agda
  refl~ : {A : Set} (s : Stream A) → s ~ s
  refl~ s  .head  = refl
  refl~ s  .tail  = refl~ (s .tail)

  takeDrop  : {A : Set} (n : Nat) (s : Stream A)
            → (take n s ++ drop n s) ~ s
  takeDrop zero     s        = refl~ s
  takeDrop (suc n)  s .head  = refl
  takeDrop (suc n)  s .tail  = takeDrop n (s .tail)
```

### From streams to colists and back

> **Exercise.** Prove that converting a stream to a colist and back results in a
> stream that is bisimilar to the original one:

```agda
  module FromStreamInv where
    open FiniteInfinite

    fromStreamInv : {A : Set} (xs : Stream A)
      → toStream (fromStream xs) (fromStreamInf xs) ~ xs
    fromStreamInv xs = {!!}
```
