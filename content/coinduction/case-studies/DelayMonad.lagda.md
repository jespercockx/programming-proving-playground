---
title: The delay monad
---

The *delay monad* embeds potentially non-terminating computations in Agda:

```agda
{-# OPTIONS --guardedness #-}
module coinduction.case-studies.DelayMonad where

open import prelude.Prelude using
  (Nat; zero; suc; Either; left; right; _≡_; refl)
```

```agda
mutual
  data Delay (A : Set) : Set where
    now    : A → Delay A
    later  : Delay' A → Delay A

  record Delay' (A : Set) : Set where
    coinductive
    field force : Delay A
open Delay' public
```

## Delayed values

Classically, any `x : Delay A` is either `never` or `laters k a` for some `k :
Nat` and `a : A`:

```agda
never : {A : Set} → Delay A
never = later (λ where .force → never)

laters : {A : Set} (n : Nat) → A → Delay A
laters zero a = now a
laters (suc n) a = later
  (λ where .force → laters n a)
```

> **Exercise.** Implement `iter : (A → Either A B) → A → Delay B`.

```agda
iter : {A B : Set} → (A → Either A B) → A → Delay B
iter f x = {!!}
```

## Implementing bind for the delay monad

```agda
_>>=_ : {A B : Set} → Delay A → (A → Delay B) → Delay B
now x >>= f = f x
later d >>= f = later λ where
  .force → d .force >>= f
```

## Convergence of delayed values

```agda
data _⇓_ {A : Set} : Delay A → A → Set where
  now    : (x : A) → now x ⇓ x
  later  : {d : Delay' A} {x : A} → d .force ⇓ x → later d ⇓ x

⇓-unique : {A : Set} {d : Delay A} {x y : A}
         → d ⇓ x → d ⇓ y → x ≡ y
⇓-unique (now x) (now y) = refl
⇓-unique (later p) (later q) = ⇓-unique p q
```

## Bisimulation of delayed values

```agda
mutual
  data _~_ {A : Set} : Delay A → Delay A → Set where
    now    : (x : A) → now x ~ now x
    later  : {x y : Delay' A} → x ~' y → later x ~ later y

  record _~'_ {A : Set} (x y : Delay' A) : Set where
    coinductive
    field force : x .force ~ y .force
open _~'_ public
```

## Monad laws for Delay

```agda
refl~ : {A : Set} (x : Delay A) → x ~ x
refl~ (now x) = now x
refl~ (later x) = later λ where
  .force → refl~ (x .force)

now->>= : {A B : Set} (x : A) (f : A → Delay B)
        → (now x >>= f) ~ f x
now->>= x f = refl~ (f x)
```

> **Exercise.** State and prove the second and third monad laws `>>=-now` and
> `>>=-assoc`.

```agda
>>=-now : {A : Set} (d : Delay A) → (d >>= now) ~ d
>>=-now d = {!!}

>>=-assoc : {A B C : Set} (d : Delay A)
  → (f : A → Delay B) (g : B → Delay C)
  → ((d >>= f) >>= g) ~ (d >>= λ x → (f x >>= g))
>>=-assoc d f g = {!!}
```

## Weak bisimilarity

Since we do not really care about the number of `later`s, we can make more
things bisimilar:

```agda
mutual
  data _~D_ {A : Set} : Delay A → Delay A → Set where
    value  : {d₁ d₂ : Delay A} {x : A}
           → d₁ ⇓ x → d₂ ⇓ x → d₁ ~D d₂
    later  : {d₁ d₂ : Delay' A} → d₁ ~D' d₂ → later d₁ ~D later d₂

  record _~D'_ {A : Set} (x y : Delay' A) : Set where
    coinductive
    field force : x .force ~D y .force
open _~D'_ public
```

## The partiality monad

Instead of making more elements bisimilar, we can quotient the `Delay` monad by
`x ~ later x`.

This leads to the definition of the *partiality monad* by Altenkirch,
Danielsson and Kraus (FoSSaC 2017) as a *quotient inductive-inductive type*
(QIIT).

## References

- Capretta (2005): *General Recursion Via Coinductive Types.*
- Altenkirch, Danielsson & Kraus (2017): *Partiality, Revisited: The Partiality Monad as a Quotient Inductive-Inductive Type.*
