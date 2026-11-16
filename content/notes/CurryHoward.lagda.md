---
title: The Curry–Howard correspondence
---

```agda
module notes.CurryHoward where

open import prelude.Prelude using (Nat; zero; suc; _+_; Bool; true; false;
  []; _::_; length; _×_; _,_; Σ; id)
```

As we said before, Agda is not just a programming language but
also a proof assistant. This means we can use Agda to formulate
theorems and prove them, and Agda will check that the proofs are
correct. However, before we can use Agda as a proof assistant, we
first have to take a step back and understand the connection between
type systems and mathematical logic. This connection is known as the
*Curry-Howard correspondence*, named so after the mathematician
Haskell B. Curry (yes, that one), who discovered the correspondence
between a simple type system and propositional logic in 1934, and the
logician William A. Howard, who extended the isomorphism to
quantifiers such as ∀ ("for all") and ∃ ("exists") in
1969.

The core idea of the Curry-Howard correspondence is that we can
interpret logical propositions --- such as "P and Q", "not P",
"P implies Q",  --- as *types* whose elements are valid
proofs of that proposition.

## Propositional logic

To get a better idea of what this means, we will take a look at
several logical propositions and deduce what type they correspond
to. For each proposition, we ask two important questions: how do we
*prove* this proposition, and what can we *deduce* from it?

- **Conjunction.**  As a first example, consider the proposition "P
and Q". What do we need in order to prove it? Well, we first need a
proof of P, and we also need a proof of Q. Hence a proof of "P
and Q" is a *pair* `(p,q)` of two proofs, where p is a proof
of P and q is a proof of Q.  Similarly, if we are working on a
proof and have an assumption that "P and Q" holds, then we can
deduce that both P holds and Q holds. So given a proof r of
"P and Q", we can get a proof `fst r` of P and another
proof `snd r` of Q. So under the Curry-Howard correspondence,
"P and Q" corresponds to the pair type `P × Q`.
- **Implication.**  As a second example, let's look at the proposition
"P implies Q". In order to prove this implication, we may assume
that we have a proof x that P holds and from that we need to
construct a proof q of Q. In other words, a proof of "P implies
Q" is a *function* `λ x → q` that transforms a proof
of P into a proof of Q. In addition, if we have both a proof f
of "P implies Q" and a proof p of P, then we can combine the
two proofs to get a new proof `f p` of Q. So under the Curry-Howard
correspondence, "P implies Q" corresponds to the function type `P → Q`.
- **Disjunction.**  What type corresponds to the proposition "P or
Q"? In order to prove it, we need to either provide a proof p of
P or a proof q of Q. To avoid confusion between whether we
proved P or Q, we can label the proofs as either p
or q. Using a proof of "P or Q" is a bit less
straightforward. If we know that P holds or Q holds and we want to
prove R, then we need to show two things: (1) that P implies R,
and (2) that Q implies R. We can summarize this proof of R as
`cases z f g` where z is a proof of "P or Q", f is
a proof of "P implies R", and g is a proof of "Q implies
R" (i.e. `f : P → R` and `g : Q → R`). In conclusion, the
proposition "P or Q" corresponds to the type `Either P Q` under the Curry-Howard correspondence.

```agda
data Either (A B : Set) : Set where
  left   : A → Either A B
  right  : B → Either A B

cases : {A B C : Set} → Either A B → (A → C) → (B → C) → C
cases (left x)   f  g  = f x
cases (right y)  f  g  = g y
```

- **Truth.**  A very basic proposition is "*true*", i.e. the
proposition that always holds no matter what. Proving it is
straightforward: we don't need to provide any assumptions. We could
thus say there is a trivial proof `tt` of "*true*". On
the other hand, assuming "*true*" in a proof does not provide
any new information. We can thus say that "*true*" corresponds
to the unit type `⊤`[^1], which is defined as follows:

```agda
data ⊤ : Set where
  tt : ⊤
```

(This is very similar to the empty tuple type `()` in Haskell,
which has a single inhabitant `() :: ()`.)
- **Falsity.**  The other basic proposition is "*false*", the
proposition that is never true.
There are no ways to prove it, which
suggests that it should correspond to an *empty* type. In Agda,
we can define the empty type `⊥`[^2] as a datatype with no
constructors:

```agda
data ⊥ : Set where
  -- no constructors
```

On the other hand, if we assume we have a proof p of
"*false*", then the principle of explosion (also known under
the latin name "ex falso quodlibet", or "from falsity follows
anything") tells us we can can get a proof `absurd p` of any
proposition we want. In Agda, we can define `absurd` as follows:

```agda
absurd : {A : Set} → ⊥ → A
absurd ()
```

The special pattern `()` used to indicate this is called an
*absurd pattern*, and the clause is called an *absurd
clause*. Absurd patterns are used to indicate to Agda that there are
no possible inputs of a given type, but we cannot just skip the clause
since there would be no other clauses left.

> **Exercise.** Define the `Either` type in Agda, and write
> down a definition of the function `cases : { A B C : Set } → Either A B → (A → C) → (B → C) → C`.

> **On empty types.**  Note that it is not possible to
> define a real empty type in Haskell: even if we define a type with no
> constructors, it is still inhabited by `undefined`, as well as
> infinitely looping programs. So in order to express false
> propositions, it is essential to work in a total language such as
> Agda.

> **Propositional logic versus boolean logic.**  On the
> surface, the two types `⊤` and `⊥` seem to be very
> similar to the booleans `true` and `false`. However, they have a
> very different role: `true` and `false` are *values* that our
> Agda programs can manipulate and return, while `⊤` and
> `⊥` are *types* used by Agda itself. In particular, it
> is not possible to write a program to check whether a given type is
> `⊤` or `⊥`. So think carefully which one you want to
> use in what situation!

From these basic propositions, we can derive some other notions:

- **Negation.**  We can encode "not P" as the type `P → ⊥`.
- **Equivalence.**  We can encode "P is equivalent to Q" as `(P → Q) × (Q → P)`.

 The correspondences
between propositions and types we have discussed so far are summarized
in the table below.

| **Propositional logic** |  | **Type system** |
| --- | --- | --- |
| proposition | P | type |
| proof of a proposition | `p : P` | program of a type |
| conjunction | `P × Q` | pair type |
| disjunction | `Either P Q` | either type |
| implication | `P → Q` | function type |
| truth | `⊤` | unit type |
| falsity | `⊥` | empty type |
| negation | `P → ⊥` | function to ⊥ |
| equivalence | `(P → Q) × (Q → P)` | pair of two functions |

*The Curry-Howard correspondence between propositional logic and simple (non-dependent) types in Agda.*

Thanks to the Curry-Howard correspondence, we can take any formula in
propositional logic, translate it to a type in Agda, and then
*prove* the formula by writing down a function of that
type. Let's look at some examples:

-  The proposition "P implies P" translates to the Agda type
`P → P`, which we can prove as follows:

```agda
proof1 : {P : Set} → P → P
proof1 p = p
```

Note that this is simply the identity function `id`.
-  The proposition "If (P implies Q) and (Q implies R)
then (P implies R)" translates to the Agda type `(P → Q) × (Q → R) → (P → R)`, which we can prove as follows:

```agda
proof2 : {P Q R : Set}
       → (P → Q) × (Q → R) → (P → R)
proof2 (f , g) = λ x → g (f x)
```

Note that this is exactly (the uncurried version of) function composition.
-  The proposition "If (P or Q) implies R then (P implies
R) and (Q implies R)" translates to the Agda type
`(Either P Q → R) → (P → R) × (Q → R)`, which
we can prove as follows:

```agda
proof3 : {P Q R : Set}
       → (Either P Q → R) → (P → R) × (Q → R)
proof3 f = (λ x → f (left x)) , (λ y → f (right y))
```

> **Exercise.** Translate the following propositions to Agda types
> using the Curry-Howard correspondence, and prove them by implementing
> a function of that type.
>
> -  If A then (B implies A).
> -  If (A and *true*) then (A or *false*).
> -  If A implies (B implies C), then (A and B) implies C.
> -  If A and (B or C), then either (A and B) or (A and C).
> -  If A implies C and B implies D, then (A and B) implies (C and D).

**Constructive mathematics.**
You may already have noticed that certain propositions that are
typically held to be true cannot be proven when translated to Agda via
the Curry-Howard correspondence. For example, the law of the excluded
middle ("either P or not P") translates to the type `{ P : Set } → Either P (P → ⊥)`, for which we
cannot in general provide an implementation without knowing anything
about P. The reason is that Agda uses a *constructive logic*,
as opposed to the classical logic typically used in mathematics. In
particular, a constructive proof of "P or Q" requires us to have
a decision procedure to determine whether P holds or Q
holds. While this seems like a major limitation of Agda, experience
shows it is only very rarely a problem in practice: most of the time a
proof that uses the excluded middle can be rewritten in a way such
that it doesn't.

For the rare cases where you want to prove a proposition that only
holds in classical logic, it is possible to translate between
constructive and classical logic using the *double negation
translation*: a proposition P is true in classical logic if and only
if "not (not P)" is true in constructive logic. So to prove a
proposition P using classical logic, all we have to do is prove `(P → ⊥) → ⊥` in the constructive logic of Agda.

> **Exercise.** Write a function of type `{ P : Set } → (Either P (P → ⊥) → ⊥) → ⊥`.

```agda
double-negation : {P : Set} → (Either P (P → ⊥) → ⊥) → ⊥
double-negation f = {!!}
```

## Predicate logic

So far, we have used the Curry-Howard correspondence to view formulas
from propositional logic as Agda types, and prove them by writing down
functions. However, we would also like to write down and prove
propositions that say something about a given value or function. For
example, we would like to be able to prove that `6` is even, or that
`length (map f xs)` is equal to `length xs` for all `xs`, or that there exists a number n such
that `n + n = 12`. In order to prove such statements, we first
need to answer two more questions: how can we define predicates that
express concrete properties such as being even, and how can we express
quantifiers such as "for all" and "there exists".

Let's start with the first question. Since --- according to Curry-Howard
--- propositions are types, we can define new propositions by defining
new data types. For example, we can define a type `IsEven n` that
expresses whether n is even by pattern matching on n:

```agda
data IsEven : Nat → Set where
  zeroIsEven : IsEven zero
  sucsucIsEven : {n : Nat} → IsEven n → IsEven (suc (suc n))
```

Note that `IsEven` is an *indexed datatype*, just like
`Vec` and `Fin` We can then easily prove that `6` is
even:

```agda
6-is-even : IsEven 6
6-is-even = sucsucIsEven (sucsucIsEven (sucsucIsEven zeroIsEven))
```

On the other hand, there is no way to prove that `7` is even:
`IsEven 7` is an empty type. In fact, we can prove that
`IsEven 7` is false by defining a function from this type to
`⊥`:

```agda
7-is-not-even : IsEven 7 → ⊥
7-is-not-even (sucsucIsEven (sucsucIsEven (sucsucIsEven ())))
```

Here we have to case split four times (using `Ctrl+c Ctrl+c`)
before Agda can see that there is indeed no proof of
`IsEven 7`. Note in particular that it is possible for a
absurd pattern `()` to appear as an argument to a constructor.

One predicate that is often quite useful is the predicate stating that
a given `Bool` is `true`. It can be defined as follows:

```agda
data IsTrue : Bool → Set where
  TrueIsTrue : IsTrue true
```

**Defining properties as functions.**
In this section we define new properties as
Agda data types. An alternative approach is to define new properties
as *functions* that return a value of type `Set`. For example,
an alternative definition of `IsTrue` could be given as:

```agda
isTrue : Bool → Set
isTrue true   = ⊤
isTrue false  = ⊥
```

This approach often results in proofs that are shorter, but less readable.  It
is also less general, as some types (such as the identity type which
we will discuss in the next section) can only be defined as a data
type. Hence we prefer the approach using data types over the one using
functions.

The type `IsTrue b` has exactly one constructor if and only if
b is `true`, and it is empty if b is `false`. By using this type in
conjunction with a function that returns a boolean, we can easily
express many properties. For example, we can define the function
`_=Nat_` that checks equality of two numbers,[^3]
and use it to
prove that the list `1 :: 2 :: 3 :: []` has length `3`:

```agda
_=Nat_ : Nat → Nat → Bool
zero     =Nat  zero     = true
(suc x)  =Nat  (suc y)  = x =Nat y
_        =Nat  _        = false

length-is-3 : IsTrue (length (1 :: 2 :: 3 :: []) =Nat 3)
length-is-3 = TrueIsTrue
```

## Universal and existential quantifiers

Next, we would like to express properties that quantify over a given
type, using quantifiers such as ∀ ("for all") and ∃
("there exists"). Luckily, we already have all the types we need, we
just didn't realize it yet!

- **Universal quantification**  Consider the proposition "for all x
of type A, `P(x)`". To prove it, we need to be able to provide a
proof of `P(v)` for each concrete value `v : A`. In other words, we
need a *function* `λ v → p` that for each v produces a
proof p of `P(v)`. In the opposite direction, if we assume we have a
proof f of "for all x of type A, `P(x)`" and we have a
concrete value `v : A`, then we can apply the proof to the case of v
to get a proof `f v` of `P(v)`. So under the Curry-Howard
correspondence, "for all x of type A, `P(x)`" corresponds to the
*dependent function type* `(x : A) → P x`.
- **Existential quantification**  Next, consider the proposition
"there exists a `x : A` such that `P(x)`". To prove it, we need to
provide a concrete example `v : A`, and provide a proof p that
`P(v)` holds, i.e. we need a *pair* `(v,p)` of a `v : A` and a `p : P v`. Conversely, if we have a proof z of "there exists a `x : A` such that `P(x)`" then we should be able to extract the witness
`fst z : A` as well as the proof `snd z : P (fst z)`. From this we deduce that "there exists a `x : A` such that
`P(x)`" corresponds to the *dependent pair type* `Σ A (λ x → P x)`.

We extend the table summarizing the Curry-Howard correspondence with
universal and existential quantification in
the table below.

| **Propositional logic** |  | **Type system** |
| --- | --- | --- |
| proposition | P | type |
| proof of a proposition | `p : P` | program of a type |
| conjunction | `P × Q` | pair type |
| disjunction | `Either P Q` | either type |
| implication | `P → Q` | function type |
| truth | `⊤` | unit type |
| falsity | `⊥` | empty type |
| negation | `P → ⊥` | function to ⊥ |
| equivalence | `(P → Q) × (Q → P)` | pair of two functions |
| universal quantification | `(x : A) → P x` | dependent function type |
| existential quantification | `Σ A (λ x → P x)` | dependent pair type |

*The Curry-Howard correspondence between predicate logic and dependent types in Agda.*

As an example, we can prove that for any natural number n,
`double n` is even:

```agda
double : Nat → Nat
double zero     = zero
double (suc n)  = suc (suc (double n))

double-is-even : (n : Nat) → IsEven (double n)
double-is-even zero     = zeroIsEven
double-is-even (suc m)  = sucsucIsEven (double-is-even m)
```

Let's take a closer look at the implementation of
`double-is-even`. It makes use of two features we've used
before: *pattern matching* and *recursion*. Through the lens
of the Curry-Howard correspondence, we can see these two features in a
new light.

-  By pattern matching on the natural number n, we are doing a
*proof by cases* on n, which allows us to prove the cases `n = zero` and `n = suc m` separately. Thanks to Agda's coverage
checker, we can be sure that the proof covers all cases.
-  By making a recursive call to `double-is-even m` on the
right-hand side for `double-is-even (suc m)`, we are making
use of *induction* on the number n: we assume that the
proposition holds for `n = m`, and from that we prove that it holds
for `n = suc m`. By induction, we can then conclude that it holds
for all values of n. Thanks to Agda's termination checker, we can be
sure that we only make use of the inductive hypothesis for smaller
values of n.

So in summary, thanks to the Curry-Howard correspondence we can use
familiar techniques from functional programming to write formal
proofs!

As another example, we can prove that for any number n, `n =Nat n` is `true`:

```agda
n-equals-n : (n : Nat) → IsTrue (n =Nat n)
n-equals-n zero     = TrueIsTrue
n-equals-n (suc m)  = n-equals-n m
```

We can now also prove existential statements by making use of the
`Σ` type. For example, we can prove that there exists a
number n such that `n + n = 12` by exhibiting the number
`6`:

```agda
half-a-dozen : Σ Nat (λ n → IsTrue ((n + n) =Nat 12))
half-a-dozen = 6 , TrueIsTrue
```

As another example, we can prove that any number n is either `0` or
the successor of another number m:

```agda
zero-or-suc : (n : Nat)
  → Either (IsTrue (n =Nat 0))
           (Σ Nat (λ m → IsTrue (n =Nat (suc m))))
zero-or-suc zero     = left TrueIsTrue
zero-or-suc (suc m)  = right (m , n-equals-n m)
```

## The identity type

In the previous section, we showed how to prove that two natural
numbers are equal by making use of the function
`_=Nat_` together with the predicate `IsTrue`. This
method works for concrete types such as natural numbers, but it has a
fundamental flaw: if we want to prove something about a function with
return type X, we first need to define a function `_=X_ : X → X → Bool`. This can be rather difficult, and moreover it
doesn't work for abstract type variables: how would we state that
`id x` is equal to x for variables `x : A` of *any* type
A?

In order to express equality at any type, Martin-Löf introduced a
new type `x ≡ y`[^4], called the *identity type*, [^5]  with a single constructor `refl : x ≡ x` (short for
"reflexivity"). If x and y are equal, then `x ≡ y` has a
single inhabitant `refl`, so it behaves like the unit type
`⊤`.  On the other hand, if x and y are distinct (e.g. `x = zero` and `y = suc zero`) then `x ≡ y` has no constructors and
hence it behaves like the empty type `⊥`.  In Agda, we can
define the identity type as follows:

```agda
data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x

infix 4 _≡_
```

Just like `Vec` and `IsEven`, `_≡_` is defined as an
indexed datatype, this time with two indices of type A.

With this type, we can for example prove that, indeed,
`1+1=2`:[^6]

```agda
one-plus-one : 1 + 1 ≡ 2
one-plus-one = refl
```

 and that `0` is not equal to `1`:[^7]

```agda
zero-not-one : 0 ≡ 1 → ⊥
zero-not-one ()
```

We can also prove facts about polymorphic types, for example that the
`id` function always returns its input:

```agda
id-returns-input : {A : Set} → (x : A) → id x ≡ x
id-returns-input x = refl
```

**Unit tests in Agda.**  A neat trick you can do in
Agda is to write unit tests directly in your code by making use of the
identity type. For example, we can write a test that `length (1 :: 2 :: [])` is `2` as follows:

```agda
length-test1 :
  length (1 :: 2 :: []) ≡ 2
length-test1 = refl
```

When the Agda typechecker checks that `refl : length (1 :: 2 :: []) ≡ 2`, it will evaluate both sides
to make sure they are indeed equal. So if anything changes and the
test no longer succeeds, you will know immediately as the file will
not even typecheck any more!

Despite the fact that the identity type only has a single inhabitant
`refl`, we can prove other properties of equality: symmetry (if
`x=y`, then `y=x`), transitivity (if `x=y` and `y=z` then `x=z`), and
congruence (if `x=y` then `f(x)=f(y)`). To prove these properties, we
have to match on an argument of type `x ≡ y`. Since `refl` is the
only constructor of this type, there is always only a single
case. However, pattern matching on `refl` is not useless: by matching
a proof of `x ≡ y` against the constructor `refl`, Agda learns
that x and y are indeed equal. For example, in the definition of
`sym` below, matching on `refl` teaches Agda that x and y
must be equal, which is required for the right-hand side `refl` to be
accepted at type `y ≡ x`.

```agda
-- symmetry of equality
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- transitivity of equality
trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

-- congruence of equality
cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl
```

In general, there are two cases where we can match on a proof of `a ≡ b`:

-  If a and b can be unified by instantiating some of the
variables, then we can match on `refl`.
-  If a and b are obviously different (e.g.  are applications
of different constructors) then we can match on an absurd pattern `()`

In all other cases where a and b cannot easily be unified but they
are not obviously distinct either, Agda will throw an error message
saying it doesn't know whether there should be a case for the
constructor `refl`.

## Section summary

-  The Curry-Howard correspondence tells us that we can interpret
logical propositions as the types of valid proofs of that proposition.
-  Under the Curry-Howard correspondence, conjunction `A ∧ B`
corresponds to the pair type `A × B`, implication `A ⇒ B` corresponds to the function type `A → B`, disjunction
`A ∨ B` corresponds to the type `Either A B`, truth
corresponds to the unit type `⊤`, and falsity corresponds to
the empty type `⊥`.
-  Under the Curry-Howard correspondence, predicates on values
correspond to *dependent types*. For example, we can represent
the predicate "n is even" as the type `IsEven n`.
-  Universal quantification `∀ (x∈ A). P(x)` corresponds to
the dependent function type `(x : A) → P x`, and existential
quantification `∃ (x∈ A). P(x)` corresponds to the dependent
pair type `Σ A (λ x → P x)`.
-  The identity type `x ≡ y` represents the proposition that
x and y are equal. It is defined as an indexed datatype with a
single constructor `refl : x ≡ x`. Other properties of
equality such as symmetry, transitivity, and congruence can be proven
by pattern matching on `refl`.

[^1]: Unicode input for ⊤ is `\top`.
[^2]: Unicode input for ⊥ is `\bot`.
[^3]: Note that `Nat` is just a user-defined datatype in Agda, so it does not come with a predefined notion of equality.
[^4]: Unicode input for ≡ is `\equiv`.
[^5]: Do not confuse the *identity type* `x ≡ y` with the (type of the) *identity function* `id : {A:Set} → A → A`.
[^6]: A single page is still better than the 362 pages that Whitehead and Russell needed to prove this fact!
[^7]: Exciting!
