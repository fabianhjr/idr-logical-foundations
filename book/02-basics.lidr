= Functional Programming in Idris

== Introduction

  The functional programming style is founded on simple, everyday mathematical
intuition: If a procedure or method has no side effects, then (ignoring
efficiency) all we need to understand about it is how it maps inputs to outputs
--- that is, we can think of it as just a concrete method for computing a
mathematical function. This is one sense of the word "functional" in "functional
programming." The direct connection between programs and simple mathematical
objects supports both formal correctness proofs and sound informal reasoning
about program behavior.

  The other sense in which functional programming is "functional" is that it
emphasizes the use of functions (or methods) as _first-class_ values --- i.e.,
values that can be passed as arguments to other functions, returned as results,
included in data structures, etc. The recognition that functions can be treated
as data gives rise to a host of useful and powerful programming idioms.

  Other common features of functional languages include _algebraic data types_
and _pattern matching_, which make it easy to construct and manipulate rich data
structures, and sophisticated _polymorphic type systems_ supporting abstraction
and code reuse. Idris offers all of these features.

  The first half of this chapter introduces the most essential elements of
Idris's functional programming language. The second half introduces some basic
_tactics_ that can be used to prove properties of Idris programs.

== Data and Functions

=== Enumerated Types

  Idris offers a powerful mechanism for defining new data types from scratch.
Naturally, the Idris distribution comes preloaded with an extensive standard
library providing definitions of booleans, numbers, and many common data
structures like lists and hash tables. But there is nothing magic or primitive
about these library definitions. To illustrate this, we will explicitly
recapitulate all the definitions we need in this course, rather than just
getting them implicitly from the library.

=== Days of the Week

  To see how this definition mechanism works, let's start with a very simple
example. The following declaration tells Idris that we are defining a new set of
data values --- a _type_.

> data Day = Monday
>          | Tuesday
>          | Wednesday
>          | Thursday
>          | Friday
>          | Saturday
>          | Sunday

  The type is called `Day`, and its members are Monday, Tuesday, etc. Each line
of the definition can be read "Monday is a day, Tuesday is a day, etc."

  Having defined `Day`, we can write functions that operate on days.

> nextWeekday : Day -> Day
> nextWeekday d = case d of
>                     Monday    => Tuesday
>                     Tuesday   => Wednesday
>                     Wednesday => Thursday
>                     Thursday  => Friday
>                     Friday    => Monday
>                     Saturday  => Monday
>                     Sunday    => Monday

  One thing to note is that the argument and return types of this function are
explicitly declared. Like most functional programming languages, Idris can often
figure out these types for itself when they are not given explicitly --- i.e.,
it can do _type inference_ --- but we'll generally include them to make reading
easier.

  Having defined a function, we should check that it works on some examples.
There are actually two different ways to do this in Idris. First, we can load
the file intro an interpreter and evaluate an expression involving next_weekday.

```idris
...> nextWeekday Monday
Tuesday : Day
```

  Second, we can record what we _expect_ the result to be in the form of a
Type equality:

> test_next_weekday : (nextWeekday (nextWeekday Saturday)) = Tuesday

  This declaration does two things: it makes an assertion (that the second
weekday after sunday is tuesday), and it gives the assertion a name that can be
used to refer to it later. Having made the assertion, we can also ask Idris to
verify it, like this:

> test_next_weekday = Refl

  The details are not important for now (we'll come back to them in a bit), but
essentially this can be read as "The assertion we've just made can be proved by
observing that both sides of the equality evaluate to the same thing, after some
simplification."

=== Homework Submission Guidelines

  If you are using Software Foundations in a course, your instructor may use
automatic scripts to help grade your homework assignments. In order for these
scripts to work correctly (so that you get full credit for your work!), please
be careful to follow these rules:

  - The grading scripts work by extracting marked regions of the `.lidr` files
    that you submit. It is therefore important that you do not alter the
    "markup" that delimits exercises (`> `), the name of the exercise, etc.
    Please leave this markup exactly as you find it.
  - Do not delete exercises. If you skip an exercise (e.g., because it is marked
    Optional, or because you can't solve it), it is OK to leave a partial proof
    in your .lidr file, but in this case please make sure it has _holes_ where
    needed. (So that `make test` passes)
  - It is fine to use additional definitions (of helper functions, useful
    lemmas, etc.) in your solutions. You can put these between the exercise
    header and the theorem you are asked to prove.

=== Booleans

  In a similar way, we can define the standard type bool of booleans, with
members `True` and `False`.

> data Boolean = True | False

  Although we are rolling our own booleans here for the sake of building up
everything from scratch, Idris does, of course, provide a default implementation
of the booleans, together with a multitude of useful functions and lemmas. (Take
a look at [Prelude.Bool]) in the [Idris library documentation]) We will use
similar naming conventions to those in the Idris Library but use different names
to avoid ambigous references between our implementation and Idris's.

  Functions over booleans can be defined in the same way as above, however we
can do cases implicitly over the definition of a function --- use whichever is
convinient:

> neg : Boolean -> Boolean
> neg True  = False
> neg False = True

> and : Boolean -> Boolean -> Boolean
> and True  b2 = b2
> and False _  = False

> or : Boolean -> Boolean -> Boolean
> or True  _  = True
> or False b2 = b2

  The last two of these illustrate Idris's syntax for multi-argument function
definitions. The corresponding multi-argument application syntax is illustrated
by the following "unit tests," which constitute a complete specification --- a
truth table --- for the `or` function:

> test_or1 : (or True  False) = True
> test_or1 = Refl
> test_or2 : (or False False) = False
> test_or2 = Refl
> test_or3 : (or False True)  = True
> test_or3 = Refl
> test_or4 : (or True  True)  = True
> test_or4 = Refl

  We can also introduce some familiar syntax for the boolean operations we have
just defined. Infix operatores need to have a `fixity` declaration that
specifies the association order and order presedence. This operations will be
declared as right associative and with a presedence level of 4.

> infixr 4 \/, /\

> (\/) : Boolean -> Boolean -> Boolean
> (\/) = or
> (/\) : Boolean -> Boolean -> Boolean
> (/\) = and

> test_or5 : False \/ False \/ True = True
> test_or5 = Refl

=== Type Holes

  While developing a program --- or a proof  --- in Idris, we might be unsure
about how to proceed. Forunatly, Idris provides a special term called a
_type hole_. This is an _undefined_ term, in that if we try to evaluate a type
hole we will get the type back and **not** its evaluation.

  The importance of type holes is that they allow a program to typecheck and
provide us with information about what terms could be put in its place. (Any
term that have the same type) There is also an interactive assistant that can
help us replace type holes for normal terms.

==== Exercise:

  1 star (`nand`)

  Remove the type holes and complete the definition of the following function;
then make sure that the assertions below can each be verified by Idris. (Remove
the type holes and fill in each proof, following the model of the `or`
assertions above.) The function should return True if either or both of its
inputs are False.

> nand : Boolean -> Boolean -> Boolean
> nand = ?nand_def

> test_nand1 : (nand True  False) = True
> test_nand1 = ?nand_1
> test_nand2 : (nand False False) = True
> test_nand2 = ?nand_2
> test_nand3 : (nand False True)  = True
> test_nand3 = ?nand_3
> test_nand4 : (nand True  True)  = False
> test_nand4 = ?nand_4

==== Exercise:

  1 star (`and3`)

  Do the same for the and3 function below. This function should return true when
all of its inputs are true, and false otherwise.

> and3 : Boolean -> Boolean -> Boolean -> Boolean
> and3 = ?and3_def

> test_and3_1 : (and3 True  True  True)  = True
> test_and3_1 = ?and3_1
> test_and3_2 : (and3 False True  True)  = False
> test_and3_2 = ?and3_2
> test_and3_3 : (and3 True  False True)  = False
> test_and3_3 = ?and3_3
> test_and3_4 : (and3 True  True  False) = False
> test_and3_4 = ?and3_4

=== Function Types

  Every expression in Idris has a type, describing what sort of thing it
computes. The `:t` command asks Idris to print the type of an expression.

```idris
...> :t True
Prelude.Bool.True : Bool
Main.True : Boolean
...> :t neg True
neg True : Boolean
```

  Functions like `neg` itself are also data values, just like True and False.
Their types are called function types, and they are written with arrows.

```idris
...> :t neg
neg : Boolean -> Boolean
```

  The type of `neg`, written `Boolean` $\rightarrow$ `Boolean` and pronounced
"Boolean arrow Boolean," can be read, "Given an input of type Boolean, this
function produces an output of type Boolean." Similarly, the type of and,
written `Boolean` $\rightarrow$ `Boolean` $\rightarrow$ `Boolean`, can be read,
"Given two inputs, both of type Boolean, this function produces an output of
type Boolean."

=== Compound Types

  The types we have defined so far are examples of "enumerated types": their
definitions explicitly enumerate a finite set of elements, each of which is just
a bare constructor. Here is a more interesting type definition, where one of the
constructors takes an argument:

> data RGB = Red | Green | Blue

> data Color = Black
>            | White
>            | Primary RGB

  Let's look at this in a little more detail.

  Every inductively defined type (`Day`, `Bool`, `RGB`, `Color`, etc.) contains
a set of _constructor expressions_ built from _constructors_ like `Red`,
`Primary`, `True`, `False`, `Monday`, etc. The definitions of `RGB` and `Color`
say how expressions in the sets `RGB` and `Color` can be built:

  - `Red`, `Green`, and `Blue` are the constructors of `RGB`;
  - `Black`, `White`, and `Primary` are the constructors of `Color`;
  - The expression `Red` belongs to the set `RGB`, as do the expressions `Green`
    and `Blue`;
  - The expressions `Black` and `White` belong to the set `Color`;
  - If `p` is an expression belonging to the set `RGB`, then `Primary p`
    (pronounced "the constructor Primary applied to the argument p") is an
    expression belonging to the set `Color`;
  - And expressions formed in these ways are the only ones belonging to the sets
    `RGB` and `Color`.

  We can define functions on colors using pattern matching just as we have done
for day and bool.

> isMonochrome : Color -> Bool
> isMonochrome c = case c of
>                      Black => True
>                      White => True
>                      Primary p => False

  Since the `Primary` constructor takes an argument, a pattern matching `Primary`
should include either a variable (as above) or a constant of appropriate type
(as below).

> isRed : Color -> Bool
> isRed c = case c of
>               Black => False
>               White => False
>               Primary Red => True
>               Primary _   => False

  The pattern `Primary _` here is shorthand for "primary applied to any rgb
constructor except red." (The wildcard pattern `_` has the same effect as the
dummy pattern variable `p` in the definition of monochrome.)

=== Numbers

  An even more interesting way of defining a type is to allow its constructors
to take arguments from the very same type — that is, to allow the rules
describing its elements to be inductive.


  For example, we can define (a unary representation of) natural numbers as
follows:

> data Nat' = Zero
>           | S Nat'

  The clauses of this definition can be read:

  - `Zero` is a natural number.
  - `S` can be put in front of a natural number to yield another one --- if `n`
    is a natural number, then `S n` is too.

  Again, let's look at this in a little more detail. The definition of nat says
how expressions in the set nat can be built:

  - `Zero` and `S` are constructors;
  - The expression `Zero` belongs to the set `Nat`;
  - If `n` is an expression belonging to the set `Nat`, then `S n` is also an
    expression belonging to the set `Nat`;
  - And expressions formed in these two ways are the only ones belonging to the
    set `Nat`.

  The same rules apply for our definitions of `Day`, `Boolean`, `Color`, etc.

  The above conditions are the precise force of the _Inductive Types_. They
imply that the expression `Zero`, the expression `S Zero`, the expression
`S (S Zero)`, the expression `S (S (S Zero))`, and so on all belong to the set
`Nat`, while other expressions built from data constructors, like `True`,
`True /\ False`, `S (S False)`, and `Zero (Zero (Zero S))` do not.

  A critical point here is that what we've done so far is just to define a
_representation_ of numbers: a way of writing them down. The names `Zero` and
`S` are arbitrary, and at this point they have no special meaning --- they are
just two different marks that we can use to write down numbers (together with a
rule that says any `Nat'` will be written as some string of `S` marks followed
by a `Zero`). If we like, we can write essentially the same definition this way:

> data Nat'' = Stop
>            | Tick Nat'

  The _interpretation_ of these marks comes from how we use them to compute.

  We can do this by writing functions that pattern match on representations of
natural numbers just as we did above with booleans and days --- for example,
here is the predecessor function:

> pred : Nat' -> Nat'
> pred n = case n of
>              Zero => Zero
>              S n' => n'

  The second branch can be read: "if `n` has the form `S n'` for some `n'`, then
return `n'`."

  Because natural numbers are such a pervasive form of data, Idris provides a
bit of built-in magic for parsing and printing them: ordinary arabic numerals
can be used as an alternative to the "unary" notation defined by the
constructors `Z` and `S`. Idris prints numbers in arabic form by default:

```idris
...> (S (S (S (S Z))))
4 : Nat
```

  And Idris knows how to read an `Integer` into `Nat` and will cast when
evaluating.

> minusTwo : Nat -> Nat
> minusTwo n = case n of
>                  Z   => Z
>                  S Z => Z
>                  S (S n') => n'

```idris
...> minusTwo 4
2 : Nat
```

  The constructor `S` has the type `Nat` $\rightarrow$ `Nat`, just like `pred`
and functions like `minusTwo`:

```idris
...> :t S
Basics.S : Nat' -> Nat'
Prelude.Nat.S : Nat -> Nat
...> :t pred
Basics.pred : Nat' -> Nat'
Prelude.Nat.pred : Nat -> Nat
Prelude.pred : Enum a => a -> a
...> :t minusTwo
minusTwo : Nat -> Nat
```

  These are all things that can be applied to a number to yield a number.
However, there is a fundamental difference between the first one and the other
two: functions like `pred` and `minusTwo` come with _computation rules_ ---
e.g., the definition of `pred` says that `pred 2` can be simplified to `1` ---
while the definition of `S` has no such behavior attached. Although it is like a
function in the sense that it can be applied to an argument, it does not `do`
anything at all! It is just a way of writing down numbers. (Think about standard
arabic numerals: the numeral 1 is not a computation; it's a piece of data. When
we write 111 to mean the number one hundred and eleven, we are using 1, three
times, to write down a concrete representation of a number.)

  For most function definitions over numbers, just pattern matching is not
enough: we also need recursion. For example, to check that a number `n` is even,
we may need to recursively check whether `n-2` is even. The best way to proceed
is by destructuring instead of a case clause. (The totality checker has better
support for destructuring)

> even : Nat -> Bool
> even  Z    = True
> even (S Z) = False
> even (S (S n')) = even n'

  We can define `odd` by a similar declaration, but here is a simpler
definition:

> odd : Nat -> Bool
> odd n = not (even n)

> test_odd1 : odd 1 = True
> test_odd1 = Refl
> test_odd2 : odd 4 = False
> test_odd2 = Refl

  (You will notice if you step through these proofs that all of the work is done
by `Refl(exivity)`. We'll see more about why that is shortly.)

  Naturally, we can also define multi-argument functions by recursion.

> plus' : Nat -> Nat -> Nat
> plus' Z      m = m
> plus' (S n') m = S (plus' n' m)

  Adding three to two now gives us five, as we'd expect.

```idris
...> plus' 3 2
5 : Nat
```

  The evaluation that Idris performs to reach this conclusion can be visualized
as follows:

  1. `plus' (S (S (S Z))) (S (S Z))`
  2. `S (plus' (S (S Z)) (S (S Z)))`
  3. `S (S (plus' (S Z) (S (S Z))))`
  4. `S (S (S plus' Z (S (S Z))))`
  5. `S (S (S (S (S Z))))`

  We can also destructure any number of arguments at once:

> minus' : Nat -> Nat -> Nat
> minus'  Z      _     = Z
> minus'  n      Z     = n
> minus' (S n') (S m') = minus' n' m'

  Again, the `_` in the first line is a wildcard pattern. Writing `_` in an
argument destruting is the same as writing some variable that doesn't get used
on the right-hand side. This avoids the need to invent a variable name.

> exp : Nat -> Nat -> Nat
> exp base Z     = S Z
> exp base (S p) = mult base (exp base p)

==== Exercise:

  1 star (`factorial`)

  Recall the standard mathematical factorial function:

 > `factorial(0) = 1`

 > `factorial(n) = n * factorial(n-1) (if n>0)`

  Translate this into Idris.

> factorial : Nat -> Nat
> factorial = ?factorial_def

> test_factorial1 : factorial 3 = 6
> test_factorial1 = ?factorial_1
> test_factorial2 : factorial 5 = mult 10 12
> test_factorial2 = ?factorial_2

== Proof by Simplification

  Now that we've defined a few datatypes and functions, let's turn to stating
and proving properties of their behavior. Actually, we've already started doing
this: each _test_ in the previous sections makes a precise claim about the
behavior of some function on some particular inputs. The proofs of these claims
were always the same: use `Reflexivity` to check that both sides contain
identical values.

  The same sort of "proof by reflexivity" can be used to prove more interesting
properties as well. For example, the fact that 0 is a "neutral element" for + on
the left can be proved just by observing that 0 + n reduces to n no matter what
n is, a fact that can be read directly off the definition of plus.

  <!--- TODO: Explain Parameterized Blocks -->
  <!--- http://docs.idris-lang.org/en/latest/tutorial/modules.html#parameterised-blocks -->

> parameters (n: Nat)
>     plus_0_n : 0 + n = n
>     plus_0_n = Refl

  Moreover, it will be useful later to know that reflexivity does somewhat more
simplification --- for example, it tries "unfolding" defined terms, replacing
them with their right-hand sides. The reason for this is that, if reflexivity
succeeds, the whole goal is finished and we don't need to look at whatever
expanded expressions reflexivity has created by all this simplification and
unfolding.

  The form of the theorem we just stated and its proof are almost exactly the
same as the simpler examples we saw earlier; there are just a few differences.

  We've added the parameter `n: Nat`, so that our theorem talks about all
natural numbers `n`. Informally, to prove theorems of this form, we generally
start by saying "Suppose n is some number..." Formally, this is achieved in the
proof by taking an argument of the appropriate type, which makes `n` any
arbitrary `Nat`.

  Other similar theorems can be proved with the same pattern.

> parameters (n: Nat)
>     plus_1_left : 1 + n = S n
>     plus_1_left = Refl
>     mult_0_left : 0 * n = 0
>     mult_0_left = Refl

== Proof by Rewriting

  This theorem is a bit more interesting than the others we've seen:

> parameters (n, m: Nat)
>     plus_id_example : n = m -> n + n = m + m

  Instead of making a universal claim about all numbers `n` and `m`, it talks
about a more specialized property that only holds when `n = m`. The arrow symbol
is pronounced "implies."

  As before, we need to be able to reason by assuming we are given such numbers
`n` and `m`. We also need to assume that we are given the equality `n = m`.
Since `n` and `m` are arbitrary numbers, we can't just use reflexivity to prove
this theorem. Instead, we prove it by observing that, if we are assuming
`n = m`, then we can replace `n` with `m` in the goal type and obtain an
equality with the same expression on both sides. The tactic that tells Idris to
perform this replacement is called `rewrite`.

>     plus_id_example eq = rewrite eq in Refl

  The eq parameter moves the hypothesis `n = m` into the context. The
`rewrite eq in Refl` statement tells Idris to rewrite the current goal
`(n + n = m + m)` by replacing any occurance the left side of the equality
`n = m` with the right side. (To replace the right hand side of the equality
with the left hand side we could us `rewrite sym eq in Refl`) We can also use
the rewrite tactic with a previously proved theorem instead of a hypothesis from
the context.

==== Exercise:

  1 star (`plus_id_exercise`)

  Remove the type hole and fill in the proof.

> parameters (n, m, o: Nat)
>     plus_id_exercise : n = m -> m = o -> n + m = m + o
>     plus_id_exercise = ?plus_id_exercise_proof

  The type hole tells Idris that we want to skip trying to prove this theorem
and just accept it as a given. This can be useful for developing longer proofs,
since we can state subsidiary lemmas that we believe will be useful for making
some larger argument, use type holes to accept them on faith for the moment, and
continue working on the main argument until we are sure it makes sense; then we
can go back and fill in the proofs we skipped. Be careful, though: every time
you use type holes you are leaving a door open for total nonsense to enter
Idris's nice, rigorous, formally checked world!

==== Exercise:

  2 stars (`mult_S_1`)

> parameters (n, m: Nat)
>     mult_S_1 : m = S n -> m * (1 + n) = m * m
>     mult_S_1 = ?mult_S_1_def

== Proof by Case Analysis

  Of course, not everything can be proved by simple calculation and rewriting:
In general, unknown, hypothetical values (arbitrary numbers, booleans, lists,
etc.) can block simplification. For example, if we try to prove the following
fact using the absurd tactic, we get an error.

> parameters (n: Nat)
>     plus_1_neq_0_firsttry : Not (n + 1 = 0)
>     plus_1_neq_0_firsttry = ?absurd -- absurd will error

  The reason for this is that the definitions of `+` begins by performing a
match on its arguments. But here, the first argument to `+` is the unknown
number `n` and the argument to Not is the compound expression `n + 1 = 0`;
neither can be simplified.

  To make progress, we need to consider the possible forms of `n` separately. If
`n` is `Z`, then we can calculate the final result of `Not (n + 1 = 0)` and
check that it is, indeed, false. And if `n = S n'` for some `n'`, then, although
we don't know exactly what number `n + 1` yields, we can calculate that, at
least, it will begin with one `S`, and this is enough to calculate that, again,
Not (n + 1 = 0) will be false.

> plus_1_neq_0 : (n: Nat) -> Not (n + 1 = 0)
> plus_1_neq_0 Z     = absurd -- 1 /= 0
> plus_1_neq_0 (S n) = absurd -- Unfolding

  Destructuring generates two subgoals, which we must then prove, separately, in
order to get Idris to accept the theorem. In this example, each of the subgoals
is easily proved by a single use of absurd, which itself performs some
simplification --- e.g., the second one simplifies `Not (S n' + 1 = 0)` to
absurd by first rewriting `(S n' + 1)` to `S (n' + 1)`, then unfolding the
equality, and finaly simplifying the match.

  Destructuring can be used with any inductively defined datatype. For example,
we use it next to prove that boolean negation is involutive --- i.e., that
negation is its own inverse.

> not_involutive : (b: Bool) -> not (not b) = b
> not_involutive True  = Refl
> not_involutive False = Refl

  It is sometimes useful to destruct more arguments, generating yet more proof
obligations. For example:

> and_commutative : (a, b: Bool) -> a && b = b && a
> and_commutative True  True  = Refl
> and_commutative True  False = Refl
> and_commutative False True  = Refl
> and_commutative False False = Refl

==== Exercise:

  2 stars (`andb_true_elim1`)

> and_true_elim1 : (a, b: Bool) -> a && b = True -> a = True
> and_true_elim1 = ?and_true_elim1_proof

==== Exercise:

  1 star (`Z_neq_plus_1`)

> z_neq_plus_1 : (n: Nat) -> Not (0 = n + 1)
> z_neq_plus_1 = ?z_neq_plus_1_proof

=== More on Notation (Optional)

  (In general, sections marked Optional are not needed to follow the rest of the
book, except possibly other Optional sections. On a first reading, you might
want to skim these sections so that you know what's there for future reference.)

Recall the infix declarations for plus and times:

```idris
infixl 5 +
infixl 4 *
```

  For each symbol in Idris, we must specify its _precedence level_ and its
_associativity_. The precedence level `n` is specified by writing `n`; this
helps Idris parse compound expressions. The associativity setting helps to
disambiguate expressions containing multiple occurrences of the same symbol. For
example, the parameters specified above for `+` and `*` say that the expression
`1+2*3*4` is shorthand for `(1+((2*3)*4))`. Idris uses precedence levels from
0 to 10, and left or right associativity. We will see more examples of this
later, e.g., in the Lists chapter.

== More Exercises

==== Exercise:

  2 stars (`boolean_functions`)

> parameters (f : Bool -> Bool, x: Bool)
>     identity_applied_twice : f x = x -> f (f x) = x
>     identity_applied_twice = ?identity_applied_twice_proof

  Now state and prove a theorem `negation_applied_twice` similar to the previous
one but where the hypothesis says that the function `f` has the property that
`f x = not x`.

> -- Code Here

==== Exercise:

  3 stars, optional (`and_eq_or`)

> and_eq_or : (a, b: Bool) -> a && b = a || b -> a = b
> and_eq_or = ?and_eq_or_proof

==== Exercise:

  3 stars (`binary`)

  Consider a different, more efficient representation of natural numbers using
a binary rather than unary system. That is, instead of saying that each natural
number is either zero or the successor of a natural number, we can say that each
binary number is either:

  - Zero,
  - Twice a binary number
  - Or, one more than twice a binary number.

  (a) First, write an inductive definition of the type `Bin` corresponding to
this description of binary numbers. (Hint: Recall that the definition of `Nat`
above)

  (b) Next, write an increment function `incr` for binary numbers, and a
function `binToNat` to convert `Bin` numbers to `Nat` numbers.

  (c) Write five unit tests `test_bin_incr1`, `test_bin_incr2`, etc. for your
increment and binary-to-unary functions. (A "unit test" in Idris is a specific
type that can be proved with just reflexivity, as we've done for several of our
definitions.) Notice that incrementing a binary number and then converting it to
unary should yield the same result as first converting it to unary and then
incrementing.

> -- Code Here

  <!---            -->
  <!--- References -->
  <!---            -->

[Prelude.Bool]: https://www.idris-lang.org/docs/current/prelude_doc/docs/Prelude.Bool.html
[Idris library documentation]: https://www.idris-lang.org/docs/current/base_doc/
