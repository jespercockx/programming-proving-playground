---
title: Equational reasoning in Agda
---

```agda
{-# OPTIONS --allow-unsolved-metas #-}
module notes.EquationalReasoning where

open import solutions.Prelude hiding ([_]; take; drop)
```

In chapter 16 of his book *Programming in Haskell*, Hutton
explains how to use *equational reasoning* to prove properties of
Haskell functions. However, these proofs quickly become long and
rather boring, which makes it easy for mistakes to slip through. In
Agda, we can do better: thanks to the Curry-Howard correspondence, we
can write proofs about Agda in Agda itself, and have the typechecker
check their correctness automatically. Moreover, thanks to Agda's
flexible operator syntax, we can even write these proofs in a style
very similar to Hutton's.

In order to write equational reasoning proofs in Agda, we first need
to define a few operators that will provide us with a nice syntax to
write down these proofs. It is normal that these definitions do not
make much sense on their own, but their usefulness will become
apparent soon. [^1]

```agda
begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
begin p = p

_end : {A : Set} → (x : A) → x ≡ x
x end = refl

_=⟨_⟩_ : {A : Set} → (x : A) → {y z : A}
       → x ≡ y → y ≡ z → x ≡ z
x =⟨ p ⟩ q = trans p q

_=⟨⟩_ : {A : Set} → (x : A) → {y : A} → x ≡ y → x ≡ y
x =⟨⟩ q = x =⟨ refl ⟩ q

infix   1  begin_
infix   3  _end
infixr  2  _=⟨_⟩_
infixr  2  _=⟨⟩_
```

## Simple examples

As a first simple example of equational reasoning in Agda, let us
prove that `reverse` has no effect on singleton lists, in the
sense that `reverse [ x ] = [ x ]` for any value x, where `[ x ] = x :: []`:

```agda
[_] : {A : Set} → A → List A
[ x ] = x :: []

reverse : {A : Set} → List A → List A
reverse []         = []
reverse (x :: xs)  = reverse xs ++ [ x ]

reverse-singleton : {A : Set} (x : A) → reverse [ x ] ≡ [ x ]
reverse-singleton x =
  begin
    reverse [ x ]
  =⟨⟩                       --  definition of [_]
    reverse (x :: [])
  =⟨⟩                       --  applying reverse (second clause)
    reverse [] ++ [ x ]
  =⟨⟩                       --  applying reverse (first clause)
    [] ++ [ x ]
  =⟨⟩                       --  applying _++_
    [ x ]
  end
```

From this, we can see the general structure of a proof that uses
equational reasoning: it starts with `begin` and ends with
`end`, and in between is a sequence of expressions separated by
`=⟨⟩` symbols. Each of the expressions should be equal to the
previous one, and the result of the whole block (starting with
`begin` and ending with `end`) is a proof that the first
expression is equal to the last one. This results in proofs that are
very easy to read compared to ones using `refl` and `trans`
directly.

## Proof by cases and induction

We can combine equational reasoning with other techniques we have seen
before. For example, we can prove that `not (not b) = b`
by case analysis (i.e. pattern matching) on b:

```agda
not-not : (b : Bool) → not (not b) ≡ b
not-not false =
  begin
    not (not false)
  =⟨⟩                -- applying the inner not
    not true
  =⟨⟩                -- applying not
    false
  end

not-not true =
  begin
    not (not true)
  =⟨⟩                -- applying the inner not
    not false
  =⟨⟩                -- applying not
    true
  end
```

We can also prove facts about natural numbers by induction
(i.e. recursion). For example, we can prove that `n + 0 = n`
for all `n : Nat` (note that this fact is not immediately obvious
from the definition of `_+_`, which only says something about
`0 + n` and `(suc m) + n`):

```agda
add-n-zero : (n : Nat) → n + zero ≡ n
add-n-zero zero =
  begin
    zero + zero
  =⟨⟩                             -- applying +
    zero
  end

add-n-zero (suc n) =
  begin
    (suc n) + zero
  =⟨⟩                             -- applying +
    suc (n + zero)
  =⟨ cong suc (add-n-zero n) ⟩    -- using induction hypothesis
    suc n
  end
```

In order to prove that `suc (n + 0)` is equal to `suc n`,
we have to make use of the induction hypothesis `add-n-zero n`,
which says that `n + 0 = n`. Agda cannot figure this out on its
own, so we have to provide the proof manually. This is where the
operator `_=⟨_⟩_` comes in: it allows us to provide an
equality proof in between the angle brackets. We have to provide a
proof of `suc (n + 0) ≡ suc n` but `add-n-zero n` has type `n + 0 ≡ n`, so we apply `cong suc` to
it to apply `suc` to both sides of the equation.

> **Exercise.** Prove that `m + suc n = suc (m + n)` for all natural numbers m and n. Next, use the
> previous lemma and this one to prove commutativity of addition,
> i.e. that `m + n = n + m` for all natural numbers m
> and n.

```agda
add-n-suc : (m n : Nat) → m + (suc n) ≡ suc (m + n)
add-n-suc m n = {!!}

add-comm : (m n : Nat) → m + n ≡ n + m
add-comm m n = {!!}
```

As another example, let us show that addition of natural numbers is
associative, i.e. that `x + (y + z) = (x + y) + z`. Since there are three variables, we have to choose on
which one to pattern match. Since `_+_` is defined by pattern
matching on its first argument, and x appears twice as the first
argument to `_+_`, it is natural to try matching on x first:

```agda
add-assoc : (x y z : Nat) → x + (y + z) ≡ (x + y) + z
add-assoc zero y z =
  begin
    zero + (y + z)
  =⟨⟩                              -- applying the outer +
    y + z
  =⟨⟩                              -- unapplying add
    (zero + y) + z
  end

add-assoc (suc x) y z =
  begin
    (suc x) + (y + z)
  =⟨⟩                              -- applying the outer add
    suc (x + (y + z))
  =⟨ cong suc (add-assoc x y z) ⟩  -- using induction hypothesis
    suc ((x + y) + z)
  =⟨⟩                              -- unapplying the outer add
    (suc (x + y)) + z
  =⟨⟩                              -- unapplying the inner add
    ((suc x) + y) + z
  end
```

In general, each case of a proof typically starts by applying some
definitions, then perhaps applying an auxiliary lemma and/or induction
hypothesis, and finally unapplying some definitions. When you are
stuck writing a proof, it often helps to work from both directions:
"forwards" from the starting point and "backwards" from the final
result, until it becomes clear what step is still required.

**Exercise.** Consider the following function:

```agda
replicate : {A : Set}
  → Nat → A → List A
replicate zero     x  = []
replicate (suc n)  x  =
  x :: replicate n x
```

Prove that the length of `replicate n x` is always equal to
n, by induction on the number n.

```agda
length-replicate : {A : Set} → (n : Nat) (x : A) → length (replicate n x) ≡ n
length-replicate n x = {!!}
```

## Induction on lists

Induction can be used to prove properties of any recursive datatype,
not just natural numbers. As an example, we will prove that reversing
a list is its own inverse, i.e. `reverse (reverse xs) = xs`, by induction on `xs`.

The proof of the base case (for `[]`) is straightforward, but
the inductive case (for `x :: xs`) requires a bit more
work. In particular, it requires us to prove that `reverse`
distributes over list concatenation, swapping the two lists in the
process:

`reverse (xs ++ ys) = reverse ys ++ reverse xs`

We can prove such auxiliary lemmas either as standalone definitions,
or as local definitions in a `where`-block. Here we take the
latter approach.

```agda
reverse-reverse : {A : Set} → (xs : List A) → reverse (reverse xs) ≡ xs
reverse-reverse [] =
  begin
    reverse (reverse [])
  =⟨⟩                                             -- applying inner reverse
    reverse []
  =⟨⟩                                             -- applying reverse
    []
  end

reverse-reverse (x :: xs) =
  begin
    reverse (reverse (x :: xs))
  =⟨⟩                                             -- applying the inner reverse
    reverse (reverse xs ++ [ x ])
  =⟨ reverse-distributivity (reverse xs) [ x ] ⟩  -- distributivity (see below)
    reverse [ x ] ++ reverse (reverse xs)
  =⟨⟩                                             -- reverse singleton list
    [ x ] ++ reverse (reverse xs)
  =⟨⟩                                             -- definition of ++
    x :: reverse (reverse xs)
  =⟨ cong (x ::_) (reverse-reverse xs) ⟩          -- using induction hypothesis
    x :: xs
  end

  where
    reverse-distributivity : {A : Set} → (xs ys : List A)
                           → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
    reverse-distributivity [] ys =
      begin
        reverse ([] ++ ys)
      =⟨⟩                                    -- applying ++
        reverse ys
      =⟨ sym (append-[] (reverse ys)) ⟩      -- see append-[] lemma
        reverse ys ++ []
      =⟨⟩                                    -- unapplying reverse
        reverse ys ++ reverse []
      end

    reverse-distributivity (x :: xs) ys =
      begin
        reverse ((x :: xs) ++ ys)
      =⟨⟩                                                   -- applying ++
        reverse (x :: (xs ++ ys))
      =⟨⟩                                                   -- applying reverse
        reverse (xs ++ ys) ++ reverse [ x ]
      =⟨⟩                                                   -- applying reverse
        reverse (xs ++ ys) ++ [ x ]
      =⟨ cong (_++ [ x ]) (reverse-distributivity xs ys) ⟩  -- using induction hypothesis
        (reverse ys ++ reverse xs) ++ [ x ]
      =⟨ append-assoc (reverse ys) (reverse xs) [ x ] ⟩     -- using associativity of ++
        reverse ys ++ (reverse xs ++ [ x ])
      =⟨⟩                                                   -- unapplying inner ++
        reverse ys ++ (reverse (x :: xs))
      end
```

The proof of distributivity in turn requires two auxiliary lemmas:
that `xs ++ [] = xs`, and the associativity of
`_++_`.

> **Exercise.** Fill in the missing proofs of `append-[]` and `append-assoc`.

As another example, we can show that the `map` function
satisfies the two functor laws:

```text
map id  = id  (identity law)
map (g . h)  = map g . map h  (composition law)
```

The first law is straightforward to prove:

```agda
map-id : {A : Set} (xs : List A) → map id xs ≡ xs
map-id [] =
  begin
    map id []
  =⟨⟩          -- applying map
    []
  end

map-id (x :: xs) =
  begin
    map id (x :: xs)
  =⟨⟩                            -- applying map
    id x :: map id xs
  =⟨⟩                            -- applying id
    x :: map id xs
  =⟨ cong (x ::_) (map-id xs) ⟩  -- using induction hypothesis
    x :: xs
  end
```

In the final step of the proof, we make use of the *section
syntax* `x ::_`; this is equivalent to `λ xs → x :: xs`.

For the second law, we first need to define function composition. The
symbol . is not a valid function name, but we can instead use the
symbol ∘.[^2]

```agda
_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘ h = λ x → g (h x)
```

With this definition, we can also state and prove the second functor
law for `map` on lists:

```agda
map-compose : {A B C : Set} (f : B → C) (g : A → B) (xs : List A)
            → map (f ∘ g) xs ≡ map f (map g xs)
map-compose f g [] =
  begin
    map (f ∘ g) []
  =⟨⟩                                           -- applying map
    []
  =⟨⟩                                           -- unapplying map
    map f []
  =⟨⟩                                           -- unapplying map
    map f (map g [])
  end

map-compose f g (x :: xs) =
  begin
    map (f ∘ g) (x :: xs)
  =⟨⟩                                           -- applying map
    (f ∘ g) x :: map (f ∘ g) xs
  =⟨⟩                                           -- applying function composition
    f (g x) :: map (f ∘ g) xs
  =⟨ cong (f (g x) ::_) (map-compose f g xs) ⟩  -- using induction hypothesis
    f (g x) :: map f (map g xs)
  =⟨⟩                                           -- unapplying map
    map f (g x :: map g xs)
  =⟨⟩                                           -- unapplying map
    map f (map g (x :: xs))
  end
```

> **Exercise.** Prove that `length (map f xs)`
> is equal to `length xs` for all `xs`.

```agda
length-map : {A B : Set} (f : A → B) (xs : List A) → length (map f xs) ≡ length xs
length-map f xs = {!!}
```

**Exercise.** Define the functions `take` and `drop` that respectively
return or remove the first n elements of the list (or all elements
if the list is shorter).

```agda
take : {A : Set} → Nat → List A → List A
take n xs = {!!}

drop : {A : Set} → Nat → List A → List A
drop n xs = {!!}
```

Prove that for any number n and any list `xs`, we have
`take n xs ++ drop n xs = xs`.

```agda
take-drop : {A : Set} (n : Nat) (xs : List A) → take n xs ++ drop n xs ≡ xs
take-drop n xs = {!!}
```

## Verifying optimizations

In section 16.6 of *Programming in Haskell*, Hutton notes that
the naive implementation of `reverse` using concatenation
`_++_` is very inefficient: it needs to traverse the whole
list for each application of `_++_`, resulting in quadratic
complexity overall. A more efficient implementation of this function
uses a helper function with an extra argument called an
*accumulator* to pass around the intermediate results.

```agda
reverse-acc : {A : Set} → List A → List A → List A
reverse-acc []        ys = ys
reverse-acc (x :: xs) ys = reverse-acc xs (x :: ys)

reverse' : {A : Set} → List A → List A
reverse' xs = reverse-acc xs []
```

We can test that this function `reverse'` is indeed much faster
than `reverse`: it has linear rather than quadratic complexity.
However, can we be sure that the two implementations do indeed produce
the same result? Let's prove it!

```agda
reverse'-reverse : {A : Set} → (xs : List A) → reverse' xs ≡ reverse xs
reverse'-reverse xs =
  begin
    reverse' xs
  =⟨⟩                           -- definition of reverse'
    reverse-acc xs []
  =⟨ reverse-acc-lemma xs [] ⟩  -- using reverse-acc-lemma
    reverse xs ++ []
  =⟨ append-[] (reverse xs) ⟩   -- using append-[]
    reverse xs
  end
```

To prove the correctness of `reverse'`, we need to prove a fact
about the helper function `reverse-acc`, namely that
`reverse-acc xs [] = reverse xs ++ []`. However, if we try to prove this directly, we get
stuck: in the recursive case, the second argument of
`reverse-acc` is no longer `[]`, so it is not possible to make
use of the inductive hypothesis. Instead, we need to prove a more
general result where we replace `[]` by a variable `ys`. [^3]

```agda
  where
    reverse-acc-lemma : {A : Set} → (xs ys : List A)
      → reverse-acc xs ys ≡ reverse xs ++ ys
    reverse-acc-lemma [] ys =
      begin
        reverse-acc [] ys
      =⟨⟩                     -- definition of reverse-acc
        ys
      =⟨⟩                     -- unapplying ++
        [] ++ ys
      =⟨⟩                     -- unapplying reverse
        reverse [] ++ ys
      end

    reverse-acc-lemma (x :: xs) ys =
      begin
        reverse-acc (x :: xs) ys
      =⟨⟩                                            -- definition of reverse-acc
        reverse-acc xs (x :: ys)
      =⟨ reverse-acc-lemma xs (x :: ys) ⟩            -- using induction hypothesis
        reverse xs ++ (x :: ys)
      =⟨⟩                                            -- unapplying ++
        reverse xs ++ ([ x ] ++ ys)
      =⟨ sym (append-assoc (reverse xs) [ x ] ys) ⟩  -- using associativity of append
        (reverse xs ++ [ x ]) ++ ys
      =⟨⟩                                            -- unapplying reverse
        reverse (x :: xs) ++ ys
      end
```

The proof of `reverse-acc-lemma` is mostly standard. The only
notable thing is the use of the two lemmas `append-[]` and
`append-assoc` which you have proved before: if you want to make
them accessible here, you'll need to move them out of the
`where`-block to the top level to make them globally
accessible.

In his book, Hutton gives another example of using
an accumulator for flattening a tree structure. In Agda, we can define
binary trees as follows:

```agda
data Tree (A : Set) : Set where
  leaf  : A → Tree A
  node  : Tree A → Tree A → Tree A
```

We can then define two versions of the `flatten` function: one
naive implementation that uses `_++_`, and one efficient one
that uses an accumulator:

```agda
flatten : {A : Set} → Tree A → List A
flatten (leaf x)      = [ x ]
flatten (node t1 t2)  = flatten t1 ++ flatten t2

flatten-acc : {A : Set} → Tree A → List A → List A
flatten-acc (leaf x)      xs  = x :: xs
flatten-acc (node t1 t2)  xs  =
  flatten-acc t1 (flatten-acc t2 xs)

flatten' : {A : Set} → Tree A → List A
flatten' t = flatten-acc t []
```

Now we can prove that these two implementations are functionally equivalent,
following the example of the `reverse` function above:

```agda
flatten-acc-flatten : {A : Set} (t : Tree A) (xs : List A) → flatten-acc t xs ≡ flatten t ++ xs
flatten-acc-flatten (leaf x)   xs =
  begin
    flatten-acc (leaf x) xs
  =⟨⟩                                                   -- definition of flatten-acc
    x :: xs
  =⟨⟩                                                   -- unapplying ++
    [ x ] ++ xs
  =⟨⟩                                                   -- unapplying flatten
    flatten (leaf x) ++ xs
  end
flatten-acc-flatten (node l r) xs =
  begin
    flatten-acc (node l r) xs
  =⟨⟩                                                   -- applying flatten-acc
    flatten-acc l (flatten-acc r xs)
  =⟨ flatten-acc-flatten l (flatten-acc r xs) ⟩         -- using IH for l
    flatten l ++ (flatten-acc r xs)
  =⟨ cong (flatten l ++_) (flatten-acc-flatten r xs) ⟩  -- using IH for r
    flatten l ++ (flatten r ++ xs)
  =⟨ sym (append-assoc (flatten l) (flatten r) xs) ⟩    -- using append-assoc
    (flatten l ++ flatten r) ++ xs
  =⟨⟩                                                   -- unapplying flatten
    (flatten (node l r)) ++ xs
  end

flatten'-flatten : {A : Set} → (t : Tree A) → flatten' t ≡ flatten t
flatten'-flatten t = {!  !}
```

> **Exercise.** Complete the proof of `flatten'-flatten` by making use of the `flatten-acc-flatten` lemma above and the `append-[]` lemma we used earlier.

## Compiler correctness

We conclude this section with the extended example from section 16.7
of *Programming in Haskell*. Rather than duplicating the full
explanation here, we just show how to port the code to Agda and
formally state the correctness property. Please refer to the book for
a full explanation.

```agda
data Expr : Set where
  valE  : Nat → Expr
  addE  : Expr → Expr → Expr

eval : Expr → Nat
eval (valE x)      = x
eval (addE e1 e2)  = eval e1 + eval e2

data Op : Set where
  PUSH  : Nat → Op
  ADD   : Op

Stack  = List Nat
Code   = List Op

exec : Code → Stack → Stack
exec []             s              = s
exec (PUSH x :: c)  s              = exec c (x :: s)
exec (ADD    :: c)  (m :: n :: s)  = exec c (n + m :: s)
exec (ADD    :: c)  _              = []

-- First version, inefficient and hard to reason about
-- compile : Expr → Code
-- compile (valE x)     = [ PUSH x ]
-- compile (addE e1 e2) = compile e1 ++ compile e2 ++ [ ADD ]

-- Second version, much faster and easier to
-- prove correct
compile' : Expr → Code → Code
compile' (valE x)      c  = PUSH x :: c
compile' (addE e1 e2)  c  = compile' e1 (compile' e2 (ADD :: c))

compile : Expr → Code
compile e = compile' e []

compile'-exec-eval : (e : Expr) (s : Stack) (c : Code)
  → exec (compile' e c) s ≡ exec c (eval e :: s)
compile'-exec-eval (valE x) s c =
  begin
    exec (compile' (valE x) c) s
  =⟨⟩                                                    -- applying compile'
    exec (PUSH x :: c) s
  =⟨⟩                                                    -- applying exec for PUSH
    exec c (x :: s)
  =⟨⟩                                                    -- unapplying eval for valE
    exec c (eval (valE x) :: s)
  end

compile'-exec-eval (addE e1 e2) s c =
  begin
    exec (compile' (addE e1 e2) c) s
  =⟨⟩                                                    -- applying compile'
    exec (compile' e1 (compile' e2 (ADD :: c))) s
  =⟨ compile'-exec-eval e1 s (compile' e2 (ADD :: c)) ⟩  -- using IH for e1
    exec (compile' e2 (ADD :: c)) (eval e1 :: s)
  =⟨ compile'-exec-eval e2 (eval e1 :: s) (ADD :: c) ⟩   -- using IH for e2
    exec (ADD :: c) (eval e2 :: eval e1 :: s)
  =⟨⟩                                                    -- applying exec for ADD
    exec c (eval e1 + eval e2 :: s)
  =⟨⟩                                                    -- unapplying eval for addE
    exec c (eval (addE e1 e2) :: s)
  end

compile-exec-eval : (e : Expr) → exec (compile e) [] ≡ [ eval e ]
compile-exec-eval e =
  begin
    exec (compile e) []
  =⟨ compile'-exec-eval e [] [] ⟩                        -- using compile'-exec-eval lemma
    exec [] (eval e :: [])
  =⟨⟩                                                    -- applying exec for []
    eval e :: []
  =⟨⟩                                                    -- unapplying [_]
    [ eval e ]
  end
```

## Section summary

-  Equational reasoning is the process of proving that two
expressions are equivalent by giving a sequence of equalities. In
Agda, we can write equational reasoning proofs by using the operators
`begin_`, `_end`, `_=⟨_⟩_`, and
`_=⟨⟩_`.
-  We can write proofs by case analysis as functions that use
pattern matching, and proofs by induction as functions that call
themselves recursively on smaller arguments.
-  Equational reasoning can be used to prove many properties of
functional programs. In particular, we can use it to prove typeclass
laws for specific instances, to verify the correctness of
optimizations, and to prove compiler correctness.

[^1]: To enter the ⟨ symbol in Agda, write `\<`, and similarly for ⟩, write `\>`.
[^2]: Unicode input for ∘ is `\buw`
[^3]: When proving something by induction, it often happens that a direct attempt fails, but we can first prove a more general statement for which the induction does work, and then derive the desired result from that. So when you are stuck on a proof, keep your eyes open for possible generalizations!
