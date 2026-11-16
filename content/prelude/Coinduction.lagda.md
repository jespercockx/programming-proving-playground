---
title: Coinduction prelude
---

This module collects the coinductive definitions that the later coinduction
chapters share, in the same way that `prelude.Prelude` collects the
definitions shared between the notes chapters. The chapters themselves still
define these types from scratch as part of the exposition; this module provides
hole-free copies so that a later chapter can import what it needs without
importing an earlier chapter that contains exercise holes.

```agda
{-# OPTIONS --guardedness --cubical-compatible #-}
module prelude.Coinduction where

open import prelude.Prelude using
  (Nat; zero; suc; List; []; _::_; _≡_; refl)

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)
```

## Streams

```agda
record Stream (A : Set) : Set where
  coinductive
  field
    head  : A
    tail  : Stream A
open Stream

take : {A : Set} → Nat → Stream A → List A
take zero    s = []
take (suc n) s = s .head :: take n (s .tail)

drop : {A : Set} → Nat → Stream A → Stream A
drop zero     s  = s
drop (suc n)  s  = drop n (s .tail)

_::S_ : {A : Set} → A → Stream A → Stream A
x ::S xs = record { head = x ; tail = xs }

_++_ : {A : Set} → List A → Stream A → Stream A
[]       ++ ys = ys
(x :: xs) ++ ys = x ::S (xs ++ ys)

natsFrom : Nat → Stream Nat
natsFrom n .head = n
natsFrom n .tail = natsFrom (suc n)

nats : Stream Nat
nats = natsFrom 0
```

## Colists

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

fromList : {A : Set} → List A → Colist A
fromList []       = []
fromList (x :: xs) = x :: record { force = fromList xs }

fromStream : {A : Set} → Stream A → Colist A
fromStream {A} xs = xs .head :: rest
  where
    rest : Colist' A
    rest .force = fromStream (xs .tail)
```

## Bisimulation of streams

```agda
record _~_ {A : Set} (s1 s2 : Stream A) : Set where
  coinductive
  field
    head  : s1 .head ≡ s2 .head
    tail  : s1 .tail ~ s2 .tail
open _~_

refl~ : {A : Set} (s : Stream A) → s ~ s
refl~ s .head = refl
refl~ s .tail = refl~ (s .tail)
```
