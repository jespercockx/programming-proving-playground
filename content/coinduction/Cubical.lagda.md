---
title: Cubical prelude
---

This module collects the minimal cubical definitions that the chapter on
coinductive proving needs. It is a small stand-in for the path type of
`Cubical.Foundations.Prelude`, built directly on Agda's cubical primitives.

```agda
{-# OPTIONS --cubical #-}
module coinduction.Cubical where

open import Agda.Primitive.Cubical using (I; i0; i1) public
open import Agda.Builtin.Cubical.Path using (PathP)
```

The cubical *interval* type `I` has two elements `i0` and `i1` that cannot be
distinguished from inside Agda. The cubical path type `Path A x y` is the type
of functions `f : I → A` with `f i0 = x` and `f i1 = y`:

```agda
Path : (A : Set) → A → A → Set
Path A = PathP (λ _ → A)
```

The reflexivity and congruence lemmas for the path type mirror the
corresponding lemmas for the inductive identity type:

```agda
reflP : {A : Set} {x : A} → Path A x x
reflP {x = x} i = x

congP : {A B : Set} (f : A → B) {x y : A} → Path A x y → Path B (f x) (f y)
congP f p i = f (p i)
```

Functional extensionality, which is consistent but unprovable for the inductive
identity type, is trivial for the path type:

```agda
funExt : {A B : Set} {f g : A → B}
       → ((x : A) → Path B (f x) (g x))
       → Path (A → B) f g
funExt h i x = h x i
```
