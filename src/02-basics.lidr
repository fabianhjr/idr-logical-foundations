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
>                      Monday    => Tuesday
>                      Tuesday   => Wednesday
>                      Wednesday => Thursday
>                      Thursday  => Friday
>                      Friday    => Saturday
>                      Saturday  => Sunday
>                      Sunday    => Monday

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

> test_next_weekday : (nextWeekday (nextWeekday Sunday)) = Tuesday

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

> data Bool = True | False

  Although we are rolling our own booleans here for the sake of building up
everything from scratch, Idris does, of course, provide a default implementation
of the booleans, together with a multitude of useful functions and lemmas. (Take
a look at [Prelude.Bool]) in the [Idris library documentation] if you are
interested) Whenever possible, we'll name our own definitions and theorems so
that they exactly coincide with the ones in the standard library.

  Functions over booleans can be defined in the same way as above:

> not : Bool -> Bool
> not b = case b of
>             False => True
>             True  => False

> and : Bool -> Bool -> Bool
> and b1 b2 = case b1 of
>                 False => False
>                 True  => b2

> or : Bool -> Bool -> Bool
> or b1 b2 = case b1 of
>                False => b2
>                True  => True

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

> infixr 4 ||, &&

> (||) : Bool -> Bool -> Bool
> (||) = or
> (&&) : Bool -> Bool -> Bool
> (&&) = and

> test_or5 : False || False || True = True
> test_or5 = Refl

=== Type Holes

  <!--- TODO: Idris Holes -->

=== Exercises

==== Exercise: 1 star (nand)

  Remove the type holes and complete the definition of the following function;
then make sure that the assertions below can each be verified by Idris. (Remove
the type holes and fill in each proof, following the model of the or tests
above.) The function should return True if either or both of its inputs are
False.

> nand : Bool -> Bool -> Bool
> nand b1 b2 = ?nand_def

> test_nand1 : (nand True  False) = True
> test_nand1 = ?nand1
> test_nand2 : (nand False False) = True
> test_nand2 = ?nand2
> test_nand3 : (nand False True)  = True
> test_nand3 = ?nand3
> test_nand4 : (nand True  True)  = False
> test_nand4 = ?nand4

==== Exercise: 1 star (and3)

  Do the same for the and3 function below. This function should return true when
all of its inputs are true, and false otherwise.

> and3 : Bool -> Bool -> Bool -> Bool
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
True : Bool
...> :t not True
not True : Bool
```

  Functions like `not` itself are also data values, just like True and False.
Their types are called function types, and they are written with arrows.

```idris
...> :t not
not : Bool -> Bool
```

  The type of not, written Bool $\rightarrow$ Bool and pronounced "Bool arrow
Bool," can be read, "Given an input of type Bool, this function produces an
output of type Bool." Similarly, the type of and, written Bool $\rightarrow$
Bool $\rightarrow$ Bool, can be read, "Given two inputs, both of type bool, this
function produces an output of type bool."

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



  <!-- References -->



[Prelude.Bool]: https://www.idris-lang.org/docs/current/prelude_doc/docs/Prelude.Bool.html
[Idris library documentation]: https://www.idris-lang.org/docs/current/base_doc/
