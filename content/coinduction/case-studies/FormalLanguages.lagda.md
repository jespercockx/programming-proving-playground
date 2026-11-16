---
title: Formal languages
---

We can describe a formal language `l` (a set of strings) over an alphabet `A`
with two pieces of data:

- whether it is *nullable* (contains the empty string)
- for each `a ∈ A`, the *derivative* `δa(l) = { s | a·s ∈ l }`.

Note that this is a *coinductive* description of formal languages. We can
visualize a language as an infinite *trie*.

Coinductive formal languages in Agda:

```agda
{-# OPTIONS --guardedness --sized-types #-}
module coinduction.case-studies.FormalLanguages where

open import prelude.Prelude using
  (Bool; true; false; not; _&&_; _||_; if_then_else_; List; []; _::_; _≡_)
open import prelude.Coinduction using (_∘_)
```

```agda
module FormalLanguages (A : Set) (_==_ : A → A → Bool) where
  record Lang : Set where
    coinductive
    field
      ν : Bool
      δ : A → Lang
  open Lang public
```

## Some simple languages

```agda
  ∅ : Lang
  ∅ .ν = false
  ∅ .δ = λ _ → ∅

  ε : Lang
  ε .ν = true
  ε .δ = λ _ → ∅

  char : A → Lang
  char a .ν = false
  char a .δ b = if a == b then ε else ∅
```

## Language membership and tabulation

```agda
  _∋_ : Lang → List A → Bool
  l ∋ [] = l .ν
  l ∋ (x :: xs) = l .δ x ∋ xs

  trie : (List A → Bool) → Lang
  trie f .ν = f []
  trie f .δ a = trie (f ∘ (a ::_))
```

## Operations on languages

```agda
  complement : Lang → Lang
  complement l .ν    = not (l .ν)
  complement l .δ x  = complement (l .δ x)

  _∪_ : Lang → Lang → Lang
  (l₁ ∪ l₂) .ν    = l₁ .ν || l₂ .ν
  (l₁ ∪ l₂) .δ x  = l₁ .δ x ∪ l₂ .δ x

  _∩_ : Lang → Lang → Lang
  (l₁ ∩ l₂) .ν    = l₁ .ν && l₂ .ν
  (l₁ ∩ l₂) .δ x  = l₁ .δ x ∩ l₂ .δ x
```

## Language concatenation

We run into a problem when defining concatenation of languages:

```text
  _·_ : Lang → Lang → Lang
  (l₁ · l₂) .ν    = l₁ .ν && l₂ .ν
  (l₁ · l₂) .δ x  = (if l₁ .ν then l₂ else ∅) ∪ (l₁ .δ x · l₂)

-- Agda reports:
--   Termination checking failed for _·_
--   Problematic calls: l₁ .δ x · l₂
```

The guardedness is obscured by the call to `∪`.

## Sized types to the rescue

```agda
module SizedFormalLanguages (A : Set) (_==_ : A → A → Bool) where
  open import Agda.Builtin.Size using (Size; Size<_; ∞)
  variable i : Size

  record Lang (i : Size) : Set where
    coinductive
    field
      ν  : Bool
      δ  : {j : Size< i} → A → Lang j
  open Lang public

  _∋_ : Lang ∞ → List A → Bool
  l ∋ []        = l .ν
  l ∋ (x :: xs)  = l .δ x ∋ xs

  trie : (List A → Bool) → Lang i
  trie f .ν    = f []
  trie f .δ a  = trie (f ∘ (a ::_))

  ∅ : Lang i
  ∅ .ν    = false
  ∅ .δ _  = ∅

  ε : Lang i
  ε .ν    = true
  ε .δ _  = ∅

  char : A → Lang i
  char a .ν    = false
  char a .δ b  = if a == b then ε else ∅

  complement : Lang i → Lang i
  complement l .ν    = not (l .ν)
  complement l .δ x  = complement (l .δ x)

  _∩_ : Lang i → Lang i → Lang i
  (l₁ ∩ l₂) .ν    = l₁ .ν && l₂ .ν
  (l₁ ∩ l₂) .δ x  = l₁ .δ x ∩ l₂ .δ x
```

We can define union to be size-preserving:

```agda
  _∪_ : Lang i → Lang i → Lang i
  (l₁ ∪ l₂) .ν    = l₁ .ν || l₂ .ν
  (l₁ ∪ l₂) .δ x  = l₁ .δ x ∪ l₂ .δ x
```

This allows the definition of concatenation to pass:

```agda
  _·_ : Lang i → Lang i → Lang i
  (l₁ · l₂) .ν    = l₁ .ν && l₂ .ν
  (l₁ · l₂) .δ x  = (if l₁ .ν then l₂ else ∅) ∪ (l₁ .δ x · l₂)
```

## Definition of Kleene star

```agda
  _* : Lang i → Lang i
  (l *) .ν    = true
  (l *) .δ x  = l .δ x · (l *)
```

## Arden's rule

*Arden's rule* states: for a non-nullable language `k`, if `l = (k · l) ∪ m`,
then `l = (k *) · m`.

> **Question.** How do we state this rule in Agda?

Using bisimulation!

## Bisimulation of languages

```agda
  infix 6 _~⟨_⟩~_
  record _~⟨_⟩~_
    (l₁ : Lang ∞) (i : Size) (l₂ : Lang ∞) : Set where
    coinductive
    field
      ν  : l₁ .ν ≡ l₂ .ν
      δ  : {j : Size< i} (x : A) → l₁ .δ x ~⟨ j ⟩~ l₂ .δ x
  open _~⟨_⟩~_
```

## Arden's rule in Agda

Now we can state Arden's rule:

```agda
  arden : (k l m : Lang ∞) →
    l ~⟨ ∞ ⟩~ (k · l) ∪ m → l ~⟨ ∞ ⟩~ (k *) · m
  arden k l m = {!!}
```

For the full proof, see *Equational Reasoning about Formal Languages in
Coalgebraic Style* by Andreas Abel (2016).

## References

- Abel (2016): *Equational Reasoning about Formal Languages in Coalgebraic Style.*
