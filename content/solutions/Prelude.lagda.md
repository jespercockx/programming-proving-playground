---
title: Prelude
---

This module collects the definitions that the individual chapters share.
The notes build these up from scratch; here they live together so that
later chapters can import them. Solution code for the exercises lives
here as well.

```agda
{-# OPTIONS --cubical-compatible #-}
module solutions.Prelude where
```

## Natural numbers

```agda
data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
zero   + y = y
suc x  + y = suc (x + y)

_*_ : Nat → Nat → Nat
zero   * y = zero
suc x  * y = y + (x * y)
```

## Booleans

```agda
data Bool : Set where
  true  : Bool
  false : Bool

not : Bool → Bool
not true  = false
not false = true

_&&_ : Bool → Bool → Bool
true   && y = y
false  && y = false

_||_ : Bool → Bool → Bool
true   || y = true
false  || y = y

if_then_else_ : {A : Set} → Bool → A → A → A
if true   then x else y = x
if false  then x else y = y
```

## Lists

```agda
data List (A : Set) : Set where
  []    : List A
  _::_  : A → List A → List A

infixr 5 _::_

length : {A : Set} → List A → Nat
length []         = 0
length (x :: xs)  = suc (length xs)

_++_ : {A : Set} → List A → List A → List A
[]         ++  ys  = ys
(x :: xs)  ++  ys  = x :: (xs ++ ys)

map : {A B : Set} → (A → B) → List A → List B
map f []         = []
map f (x :: xs)  = f x :: map f xs

[_] : {A : Set} → A → List A
[ x ] = x :: []
```

## Pairs and the dependent pair type

```agda
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_

fst : {A B : Set} → A × B → A
fst (x , y) = x

snd : {A B : Set} → A × B → B
snd (x , y) = y

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B
```

## Maybe and lookup

```agda
data Maybe (A : Set) : Set where
  just    : A → Maybe A
  nothing : Maybe A

lookup : {A : Set} → List A → Nat → Maybe A
lookup []        n       = nothing
lookup (x :: xs) zero    = just x
lookup (x :: xs) (suc n) = lookup xs n
```

## Polymorphic identity

```agda
id : {A : Set} → A → A
id x = x
```

## Truth, falsity, disjunction

```agda
data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

absurd : {A : Set} → ⊥ → A
absurd ()

data Either (A B : Set) : Set where
  left   : A → Either A B
  right  : B → Either A B

cases : {A B C : Set} → Either A B → (A → C) → (B → C) → C
cases (left x)   f  g  = f x
cases (right y)  f  g  = g y
```

## The identity type

```agda
data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x

infix 4 _≡_

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl
```

## Predicates and equality tests

```agda
data IsTrue : Bool → Set where
  TrueIsTrue : IsTrue true

data IsEven : Nat → Set where
  zeroIsEven   : IsEven zero
  sucsucIsEven : {n : Nat} → IsEven n → IsEven (suc (suc n))

_=Nat_ : Nat → Nat → Bool
zero     =Nat  zero     = true
(suc x)  =Nat  (suc y)  = x =Nat y
_        =Nat  _        = false
```

## Exercise solutions

```agda
append-[] : {A : Set} → (xs : List A) → xs ++ [] ≡ xs
append-[] []         = refl
append-[] (x :: xs)  = cong (x ::_) (append-[] xs)

append-assoc : {A : Set} → (xs ys zs : List A)
             → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
append-assoc []         ys zs  = refl
append-assoc (x :: xs)  ys zs  = cong (x ::_) (append-assoc xs ys zs)

take : {A : Set} → Nat → List A → List A
take zero    xs        = []
take _       []        = []
take (suc n) (x :: xs) = x :: take n xs

drop : {A : Set} → Nat → List A → List A
drop zero    xs        = xs
drop _       []        = []
drop (suc n) (x :: xs) = drop n xs
```
