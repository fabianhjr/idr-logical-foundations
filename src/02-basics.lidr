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

> next_weekday : Day -> Day
> next_weekday d = case d of
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
...> next_weekday Monday
Tuesday : Day
```

  Second, we can record what we _expect_ the result to be in the form of a
Type equality:

> test_next_weekday : (next_weekday (next_weekday Sunday)) = Tuesday

  This declaration does two things: it makes an assertion (that the second
weekday after sunday is tuesday), and it gives the assertion a name that can be
used to refer to it later. Having made the assertion, we can also ask Idris to
verify it, like this:

> test_next_weekday = Refl

  The details are not important for now (we'll come back to them in a bit), but
essentially this can be read as "The assertion we've just made can be proved by
observing that both sides of the equality evaluate to the same thing, after some
simplification."

=== Type Holes

  <!--- TODO: Idris Holes -->

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
    needed. (So that `idris --check --total` passes)
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



  <!-- References -->



[Prelude.Bool]: https://www.idris-lang.org/docs/current/prelude_doc/docs/Prelude.Bool.html
[Idris library documentation]: https://www.idris-lang.org/docs/current/base_doc/
