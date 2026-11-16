---
title: Cubical bisimulation
---

```agda
{-# OPTIONS --guardedness --cubical #-}
module coinduction.CubicalBisimulation where

open import solutions.Prelude using (Nat; zero; suc)
open import solutions.Coinduction using (Stream; take; drop; _++_)
open Stream
open import coinduction.Cubical using (Path; reflP; congP; funExt)
```

Cubical Agda is an extension of Agda with primitives from *cubical type
theory*, a version of homotopy type theory (HoTT). In particular, it provides
the cubical path type, a version of *observational equality*. The minimal
fragment of it we need is defined in the module *Cubical prelude*.

In fact, we can prove that `Path A x y` is *isomorphic* to the inductive
identity type!

The cubical path type serves as a general bisimulation relation for any
coinductive type:

```agda
takeDrop  : {A : Set} (n : Nat) (s : Stream A)
  → Path (Stream A) (take n s ++ drop n s) s
takeDrop zero     s i        = s
takeDrop (suc n)  s i .head  = s .head
takeDrop (suc n)  s i .tail  =
  takeDrop n (s .tail) i
```

> **Exercise.** Prove that bisimilarity of streams implies path equality.
