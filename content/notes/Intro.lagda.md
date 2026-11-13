---
title: An introduction to Agda for Haskell programmers
---

```agda
module notes.Intro where
```

Agda is both a strongly typed functional programming language with
support for first-class *dependent types* and a *proof assistant*
based on the Curry-Howard correspondence between propositions and types.
The goal of these lecture notes is to introduce both these unique aspects
of Agda to a general audience of functional programmers. It starts from
basic knowledge of Haskell as taught in Hutton's book *Programming in
Haskell*, and builds up to using equational reasoning to formally prove
correctness of functional programs.

Most programmers think of a type system as a set of rules that
together prevent a class of basic runtime errors, such as using a
string where the program expects an integer. This is indeed why type
systems were first introduced to programming languages: to prevent
program crashes that would follow from interpreting data in memory
incorrectly.[^1]  However, since their invention, type systems have evolved
to include a much broader range of applications:

-  By making use of type information, an IDE can help the
programmer during the programming by providing type information and
suggestions and by generating and modifying code based on the type
information. For example, the IDE can use types to generate all
possible cases in a case expression.
-  A type can express precise invariants of data in a program, such
as the length of a list or the lower and upper bounds of a search
tree. These expressive types that can depend on runtime inputs are
known as *dependent types*.
-  Types can even be used to express mathematical properties and
proofs of these properties, which can be checked automatically by the
type checker. This usage of a type system as a logic is based on a
deep and fundamental result known as the *Curry-Howard
correspondence*.

While strongly typed languages such as Java or Haskell have type
systems that are quite expressive, due to various reasons it is hard
to fully appreciate the three above points from their
perspective. In these lecture notes, we will study Agda, a functional language that
is similar to Haskell but is a bit more experimental and has an even
more expressive type system with full support for dependent types.

On the surface level, Agda code looks quite similar to Haskell code,
with some small syntactic differences. However, beneath the hood are a
number of notable differences:

-  Types in Agda are *first-class values*: basic types such as
  `Nat` and `Bool` are themselves values of another type called
  `Set`. Values of type `Set` can be passed around as arguments
  and returned just as other values.
-  All functions in Agda are *total*: where evaluating a
  function call in Haskell could lead to a runtime error or loop
  forever, evaluating a function call in Agda is guaranteed to always
  return a value of the correct type in finite time.
-  Agda has support for *dependent function types* where the
  type of the output can be different depending on the runtime value
  of the input. This allows us to assign a precise type to functions
  that are impossible to type correctly in many other languages, such
  as `printf`.
-  Agda also has types that correspond to (proofs of) *logical
  propositions*. Using these types, Agda can also be used as a
  *proof assistant* for writing and checking mathematical proofs.

> **Historical note.**  Agda's type system is based on
> *dependent type theory*, a formal language invented by the
> Swedish philosopher Per Martin-Löf. His original motivation was to
> provide a new foundation for *constructive mathematics*, a kind
> of mathematics where each proof of existence contains an algorithm to
> actually construct the object that is proven to exist. For example, a
> constructive proof of "there exists a prime number greater than
> 1000" provides an algorithm to actually produce such a number. Later
> on, it was discovered that Martin-Löf's type theory is also well
> suited to implement computer proof assistants (such as the Coq system)
> and programming languages with built-in support for verification (such
> as Agda).

The goal of these lecture notes is *not* to provide a full guide to using
Agda as a full-featured programming language. Instead, we use Agda as a vehicle
to study the basic building blocks that make up a dependently typed functional
programming language. Most of the types and functions we define --- as well as
much more --- can be found in Agda's standard library, which you can get from
[github.com/agda/agda-stdlib](https://github.com/agda/agda-stdlib). In
these notes, we will not make use of the standard library and instead define
everything from the ground up. When using Agda for real, it is of course
much easier to get these definitions from the library instead!

## Installing Agda

You do not need to install Agda to use these notes: all the code runs in your browser. If you would rather install it locally, see the [Agda user manual](https://agda.readthedocs.io/).

## Syntactic differences with Haskell

As we noted before, the syntax of Agda is in many respects similar to
that of Haskell. Here we list the most important differences:

- **Typing**  Typing is denoted by a single colon in Agda. For example, instead
of writing `b :: Bool` as in Haskell, in Agda we write `b : Bool`
to indicate that `b` is a boolean.
- **Unicode**  Agda allows optional use of unicode symbols in
  code. For example, we can write `Bool → Bool` instead of
  `Bool -> Bool` and `λ x → x` instead of
  `\ x -> x`. It is also allowed to use unicode
  symbols in names of definitions and variables. For example, we can
  define a function that is named √.[^2]
- **Naming**  In Agda there is no syntactic difference between an
  expression and a type. As a consequence, there are no restrictions
  on what names have to start with a small letter or a capital
  letter. In addition, almost all ascii and unicode
  characters[^3] can be used as part of a name. As a
  convention, names of functions, constructors, and variables in Agda
  code usually start with a small letter, while names of both type
  constructors and type variables usually start with a capital
  letter. While this naming convention is not enforced by the
  language, we will keep to it in these notes.
- **Operators**  To refer to the name of an operator such as + in isolation,
Agda uses underscores (as opposed to parentheses in Haskell). For example, we
have `_+_ : Nat → Nat → Nat`.
- **Whitespace**  Due to the liberal naming rules, Agda requires the use of
spaces before and after each operator. For example, Agda requires you to write
`1 + 1` instead of `1+1`. In fact, `1+1` is a valid name
for a function or variable!
- **Lists**  Unlike Haskell, Agda does not assign a special role to lists
compared to other data structures. In particular, there is no special syntax
for list literals or list comprehensions in Agda. Instead, the type
`List A` is simply a datatype defined with two constructors `[]`
and `::`. The Haskell list `[1,2,3]` can then be written in
Agda as `1 :: 2 :: 3 :: []`.
- **Tuples**  Similarly, Agda does not have a special built-in type of
tuples.  Instead, the type `A × B` is defined as a datatype
with one constructor `_,_`. For example, we have `(6 , true) : Nat × Bool`.

> **Warning.**  Agda will interpret
> all names with underscores as operators, so the use of underscores in
> non-operator names is strongly discouraged.

## Data types and pattern matching

Like in Haskell, the core part of any Agda program consists of declarations of
new *data types* and new *function definitions* by pattern
matching on these data types.

Unlike Haskell, there is no automatic import of any modules from the standard
library, so we are free to either load whichever library we want or define
everything from scratch. In this introduction, we will do the latter.

Let's define our first datatype in Agda: the type of (unary) natural numbers:

```agda
data Nat : Set where
  zero  : Nat
  suc   : Nat → Nat
```

**Natural number literals.**  By default, this definition of natural numbers
forces us to write out the numbers as `zero`, `suc zero`,
`suc (suc zero)`, . However, Agda also has built-in support
for decimal numbers, which we can activate by writing the following
pragma below the definition of `Nat`:

```agda
{-# BUILTIN NATURAL Nat #-}
```

Once we have activated this pragma, Agda will interpret the numbers
`0`, `1`, `2`,  using the constructors `zero` and `suc`.

The datatype definition consists of a *data signature* `Nat : Set` and
two *constructor signatures* `zero : Nat` and `suc : Nat → Nat`.
We can immediately spot a few differences with the corresponding Haskell
definition `data Nat = Zero | Suc Nat`:

-  The names of the constructors start with a small letter instead of a
capital letter (see *Naming* above).
-  The definition spells out the full type of each constructor instead of
just the types of their arguments.
-  The definition also assigns a type to the symbol `Nat` itself,
namely `Nat : Set`. The reason is that each defined symbol in Agda
must have a type - including types themselves - and `Set` is the type of
"simple" types such as `Nat`.

Next, we define addition `_+_` on natural numbers by pattern
matching as follows:

```agda
_+_ : Nat → Nat → Nat
zero     + y  = y
(suc x)  + y  = suc (x + y)
```

Just like in Haskell, a definition by pattern matching consists of a *type signature* followed by a list of
*clauses* or equalities. Also like in Haskell, functions can make
*recursive calls* to themselves on the right-hand side of a clause.

> **Exercise.** Define the function `halve : Nat → Nat` that
> computes the result of dividing the given number by 2 (rounded down). Test your
> definition by evaluating it for several concrete inputs.

```agda
halve : Nat → Nat
halve n = {!!}
```

To test our definition, we first load the file in VS Code
(`Ctrl+c Ctrl+l`) and then ask Agda to evaluate an expression
by pressing `Ctrl+c Ctrl+n` (for "normalize expression").  A
prompt will appear where you can enter the term to be evaluated. For
example, if you enter `1 + 1` you should get
back the response `2`.

> **Exercise.** Define the function `_*_ : Nat → Nat → Nat` for multiplication
> of two natural numbers.

```agda
_*_ : Nat → Nat → Nat
m * n = {!!}
```

> **Exercise.** Define the type `Bool` with constructors
> `true` and `false`, and define the functions for negation
> `not : Bool → Bool`, conjunction `_&&_ : Bool → Bool → Bool`,
> and disjunction `_||_ : Bool → Bool → Bool` by pattern matching.

```agda
data Bool : Set where
  true  : Bool
  false : Bool

_&&_ : Bool → Bool → Bool
x && y = {!!}

_||_ : Bool → Bool → Bool
x || y = {!!}
```

## Interactive programming in Agda

One of the unique features of Agda is its support for
*interactive programming*, which is integrated closely with the
typechecker. To use the interactive mode of Agda, you start by writing
an incomplete definition with one or more *holes*, placeholders
for code you haven't written yet. Holes are written in Agda code as a
question mark `?` or the special string `{!!}`.

```agda
not : Bool → Bool
not b = {!  !}
```

Agda can load a file even if it still contains holes. If you load the
file (with `Ctrl+c Ctrl+l`), Agda will assign a number to the holes and give you
some information about each one:

```text
?0 : Bool
```

Once you have loaded a file with holes, there are various ways you can
ask the Agda typechecker to help you through the use of shortcuts: [^4]

- **Get goal type and context (`Ctrl+c Ctrl+,`)**  This command
  will give you the type of the hole the cursor is currently in, as
  well as the types of all the variables that are currently in
  scope. For example, for the hole above you get:

```text
Bool
b : Bool
```

- **Case (`Ctrl+c Ctrl+c`)**  This command will perform a case
  split on a variable. For example, if you put the cursor in the hole
  in the definition of `not` and press `Ctrl+c Ctrl+c`,
  Agda will prompt us for a variable to split on. You can then
  enter the name `b` of the variable and press `enter`,
  giving us two clauses, one for each constructor:

  Alternatively, you can first enter the name of a variable in
  the hole (between the `{!` and `!}` signs)
  and then press `Ctrl+c Ctrl+c` to split on that variable.
- **Give (`Ctrl+c Ctrl+space`)**  This command allows
  you to enter an expression into a hole. For example, if you put
  our cursor in the first hole in the definition of `not`
  and press `Ctrl+c Ctrl+space`, Agda will prompt us
  for an expression to give. You can then enter `false` in
  the prompt and press `enter`. Agda will check that the
  expression is of the right type (in this case `Bool`) and
  then (if typechecking is successful) replace the hole with the given
  expression.

  By doing the same with the term `true` in the second hole,
  the definition of `not` is completed.

  Alternatively, you can first enter an expression into
  the hole and then
  press `Ctrl+c Ctrl+space` to replace the hole with that expression.

> **Writing programs interactively.**  When starting
> out with Agda, it may feel easier to not use the interactive commands
> and instead write the program directly. However, once the types of
> your program become more complex, it becomes much more difficult to
> write down the definition directly and you will need to rely more and
> more on these interactive commands. So it is a good idea to get some
> experience with these commands by using them as often as possible.

You can get a full overview of all available commands by pressing
`Ctrl+Shift+P` to open the command palette in VS Code and then typing
`Agda`.

## The `Set` type and polymorphic functions

One of the fundamental features of Agda is that types such as
`Nat` or `Bool` are first-class values that can be
returned and passed around as arguments. The type of `Nat` and
`Bool` is called `Set` by Agda. For example, we can define an
alias for `Nat` as follows:

```agda
MyNat : Set
MyNat = Nat
```

This works just like the declaration `type MyNat = Nat` in
Haskell: the type checker will treat the two types `Nat` and
`MyNat` as identical for all intents and purposes.

The type `Set` is also used to implement polymorphic functions and
datatypes in Agda. For example, we can define the polymorphic identity
function `id` as follows:

```agda
id : (A : Set) → A → A
id A x = x
```

The function `id` takes two arguments: a type A of type `Set`
and an element x of type A. For example, `id Bool true`
has type `Bool` and evaluates to `true`, while
`id Nat zero` has type `Nat` and evaluates to `zero`.

> **The type of `Set`.**  Since all the types we have seen so far have type
> `Set`, and `Set` itself is also a type, you might be wondering
> whether `Set` itself also has type `Set`, i.e. whether we have
> `Set : Set`. The answer is no: there are deep reasons why this is
> not allowed in Agda. Concretely, in 1972 the logician Jean-Yves Girard
> discovered a paradox in type theory (which is also at the basis of
> Agda). If Agda would allow `Set : Set`, it would break logical
> soundness of Agda, which is important for using Agda as a theorem
> prover (see later). More concretely, with `Set : Set` it would
> be possible to circumvent Agda's termination checker and implement
> non-terminating functions. To avoid this paradox and
> the problems it causes, Agda introduces another type `Set₁` such
> that `Set : Set₁`, a type `Set₂` such that `Set₁ : Set₂`, et
> cetera.

Since writing out the type arguments each time becomes boring quickly,
Agda also allows them to be declared *implicit* by using curly
braces ``:

```text
id : {A : Set} → A → A
id x = x
```

With this definition, we can simply write `id true` or
`id zero` and Agda will infer the type automatically.

As another example, `if/then/else` can simply be defined as a
function in Agda:

```agda
if_then_else_ : {A : Set} → Bool → A → A → A
if true   then x  else y  = x
if false  then x  else y  = y
```

Note that the underscores _ in the name will make Agda recognize it
as an operator, so we can write terms such as
`if b then false else true`.

Just as we can define polymorphic functions, we can also define
polymorphic datatypes by adding an argument of type `Set`. For
example, the type of lists can be defined as follows: [^5]

```agda
data List (A : Set) : Set where
  []    : List A
  _::_  : A → List A → List A

infixr 5 _::_
```

Similarly, we can define the type of pairs as a polymorphic
datatype. In Agda, the type of pairs is usually written as `A × B` in analogy of the notion of the product of two sets in
mathematics.[^6] It is defined as follows:

```agda
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B
infixr 4 _,_
```

We can define functions on pairs by pattern matching, for example:

```agda
fst : {A B : Set} → A × B → A
fst (x , y) = x

snd : {A B : Set} → A × B → B
snd (x , y) = y
```

> **Exercise.** Implement the following Agda functions:
>
> -  `length : { A : Set } → List A → Nat`
> -  `_++_ : { A : Set } → List A → List A → List A`
> -  `map : {A B : Set} → (A → B) → List A → List B`

```agda
length : {A : Set} → List A → Nat
length xs = {!!}

_++_ : {A : Set} → List A → List A → List A
xs ++ ys = {!!}

map : {A B : Set} → (A → B) → List A → List B
map f xs = {!!}
```

> **Exercise.** Implement the type `Maybe A` with two
> constructors `just : A → Maybe A` and `nothing : Maybe A`. Next, implement the function `lookup : { A : Set } → List A → Nat → Maybe A` that returns the
> element at the given position in the list.

```agda
data Maybe (A : Set) : Set where
  just    : A → Maybe A
  nothing : Maybe A

lookup : {A : Set} → List A → Nat → Maybe A
lookup xs n = {!!}
```

## Totality checking

If we call a function in Haskell, we know (thanks to purity) that it will not
perform arbitrary side-effects like doing IO or modifying global variables.
However, there are still a few things that could happen:

-  There could be an error in the program due to an incomplete pattern
match, or because the program contains a call to `error` or
`undefined`.
-  The function might not return because it gets stuck in an infinite loop.

Since functions in Haskell do not always produce a result, we call Haskell a
*partial language*.

In contrast, Agda is a *total language*, i.e. Agda functions are
*total functions* in the mathematical sense:

-  There is no `error` or `undefined`
-  Agda performs a *coverage check* to ensure all definitions by pattern matching are complete.
-  Agda performs a *termination check* to ensure all recursive definitions are terminating.

Let's look at some examples. Suppose we write an incomplete definition by
pattern matching:

```text
foo : Bool → Bool
foo true = false

-- Agda reports:
--   Incomplete pattern matching for foo. Missing cases:
--     foo false
```

Then Agda highlights the definition and gives us an error:

```text
Incomplete pattern matching for foo. Missing cases:
  foo false
when checking the definition of foo
```

Likewise, if we write a non-terminating definition:

```text
bar : Nat → Nat
bar x = bar x

-- Agda reports:
--   Termination checking failed for the following functions:
--     bar
--   Problematic calls:
--     bar x
```

Then Agda also highlights the definition and gives us an error:

```text
Termination checking failed for the following functions:
  bar
Problematic calls:
  bar x
```

> **Limitations of coverage and termination checking.**
> In general, coverage checking and termination checking are undecidable
> problems, so it is impossible to detect all complete
> and terminating functions without allowing some false negatives.
> Agda instead errs on the side of caution and allows only a subset of
> all complete and terminating functions. So it could
> happen that you write down a complicated function that is complete and
> terminating, yet Agda still throws an error. If that happens, you will
> have to write the function in a different way to make it obvious to Agda
> that the function is really total. A good rule of thumb is to
> use `Ctrl+c Ctrl+c` to make sure you have cases for all constructors,
> and to only make recursive calls on arguments that are *structurally decreasing*,
> i.e. that are a subterm of the pattern on the left-hand side of the clause.
> When in doubt, it can also pay off to split complex functions into simpler
> helper functions that are easier for Agda to analyze.

> **Exercise.** Is it possible to implement a function of type `{ A : Set } → List A → Nat → A` in Agda? If yes, do so. If
> no, explain why not.

These restrictions on coverage and termination can sometimes seem
quite restrictive, but it also enables entirely new things to be done
with the type system. In particular, totality of functions is crucial
for working with dependent types, as function calls can appear inside
types. It is also crucial for using Agda as a proof assistant, to rule
out circular proofs. We will discuss both of these topics in more
detail in the following sections.

## Section summary

-  Agda is a purely functional programming language much like
Haskell.
-  When defining a datatype in Agda, we need to give the full
type of each constructor (instead of just the types of the arguments
as in Haskell).
-  We can query the Agda typechecker using the commands
`Ctrl+c Ctrl+l` (load file), `Ctrl+c Ctrl+d` (deduce
type), and `Ctrl+c Ctrl+n` (normalise expression).
-  A hole is a part of an Agda program that is not yet complete,
and is entered using `?` or `{!!}`. We can
interactively develop a program with holes using the commands
`Ctrl+c Ctrl-,` (information about hole), `Ctrl+c
Ctrl+c` (case split), and `Ctrl+c Ctrl+space` (give solution).
-  Types in Agda are themselves values of type `Set`. We can
define polymorphic functions in Agda by adding an argument of type
`Set`.
-  Implicit arguments are declared using curly braces `` and
can be omitted from both definition and usage of the function.
-  Agda is a total language, which means that Agda functions will
never crash or fail to terminate. To ensure totality, Agda uses a
coverage checker to check completeness of functions by pattern
matching and a termination checker to check termination of recursive
functions.

[^1]: For example, a type system can prevent the floating point number `1.0` from being interpreted as a memory address.
[^2]: Many unicode characters can be entered easily using LaTeX syntax when using the Agda mode for VS Code. For example, when you type `\to` it will be replaced by →, and `\lambda` is replaced by λ. A full list of the unicode characters used in these lecture notes and how to input them can be found in the appendix.
[^3]: The exceptions are the symbols `.;{}()"`.
[^4]: When you have edited your code in some way and you want to run one of these commands, always remember to first load the file using `Ctrl+c Ctrl+l`.
[^5]: In order to write expressions such as `1 :: 2 :: 3 :: []` (as opposed to `1 :: (2 :: (3 :: []))`), we also need to tell Agda that `::` is right associative. We can do so as follows: `infixr 5 _::_`
[^6]: To write `×`, type `\times`.
