= Polymorphism and Higher-Order Functions

  In this chapter we continue our development of basic concepts of functional
programming. The critical new ideas are _polymorphism_ (abstracting functions
over the types of the data they manipulate) and _higher-order functions_
(treating functions as data). We begin with polymorphism.

== Polymorphism

=== Polymorphic Lists

  In the previous chapter, we've been working just with lists of numbers.
Obviously, interesting programs also need to be able to manipulate lists with
elements from other types --- lists of strings, lists of booleans, lists of
lists, etc. We could just define a new inductive datatype for each of these, for
example...

```idris
data BoolList = Nil
              | Cons Bool BoolList
```

... but this would quickly become tedious mostly because we would also need to
define new versions of all our list manipulating functions (`length`, `rev`,
etc.) for each new datatype definition.

  To avoid all this repetition, Idris supports polymorphic type definitions. For
example, here is a polymorphic list datatype.

```idris
data List elem = Nil
               | Cons elem (List elem)
```

  This is exactly like the definition of `NatList` and `BoolList`, except that
the `Nat` or `Bool` argument to the `Cons` constructor has been replaced by an
arbitrary type `elem`, an argument for `elem` has been added to the definition,
and the occurrences of `NatList` or `BoolList` in the types of the constructors
have been replaced by `List elem`. (We used `List Nat` in the previous chapter)

   What sort of thing is `List` itself? One good way to think about it is that
`List` is a function from Types to Types. For any particular type `elem`, the
type `List elem` is an inductively defined set of lists whose elements are of
type `elem`.

```idris
...> :t List
List : Type -> Type
```

  The parameter `a` in the definition of `List` becomes a parameter to the
constructor `Cons` --- that is, cons is now a polymorphic constructor, that
needs to be supplied with the type of the list it's building. As an example,
Nil constructs the empty list of any type.

```idris
...> :t Nil
Nil : List elem
```

  Similarly, `Cons 3` adds an element of type `Nat` to a list of type `List
Nat`. Here is an example of forming a list containing just the natural number 3.

```idris
...> :t (the Nat 3 :: Nil)
[3] : List Nat
```

  We can now go back and make polymorphic versions of all the list-processing
functions that we wrote before. Here is `replicate`, for example:

```idris
replicate : Nat -> a -> List a
replicate  Z    _ = []
replicate (S n) x = x :: replicate n x
```

> test_replicate1 : replicate 2 4 = [4, 4]
> test_replicate1 = Refl

  To use repeat to build other kinds of lists, we simply instantiate it with an
appropriate type parameter:

> test_replicate2 : replicate 1 False = [False]
> test_replicate2 = Refl

==== Exercise:

  2 stars (`mumble_grumble`)

  Consider the following two inductively defined types.

> data Mumble = A
>             | B Mumble Nat
>             | C
> data Grumble a = D Mumble
>                | E a

  Which of the following are well-typed elements of `Grumble a` for some type
`a`?

  - D (B A 5)
  - E True
  - E (B C 0)
  - C

=== Supplying Type Arguments Explicitly

  One small problem with type inference is that, occasionally, Idris does not
have enough local information to determine a type argument; in such cases, we
need to tell Idris what type we want explicitly. For example,

```idris
...> the (List Nat) [3]
[1, 2, 3] : List Nat
```

=== Exercises

==== Exercise:

  2 stars, optional (`poly_exercises`)

  Here are a few simple exercises, just like ones in the Lists chapter, for
practice with polymorphism. Complete the proofs below.

> app_nil_r : (l: List a) -> l ++ [] = l
> app_nil_r = ?app_nil_r_proof

> app_assoc : (l1, l2, l3: List a) -> l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3
> app_assoc = ?app_assoc_proof

> app_length : (l1, l2: List a) -> length (l1 ++ l2) = length l1 + length l2
> app_length = ?app_length_proof

==== Exercise:

  2 stars, optional (`more_poly_exercises`)

  Here are some slightly more interesting ones...

\ignore{

> rev : List a -> List a
> rev  []     = []
> rev (x::xs) = rev xs ++ [x]

}

> rev_app_distr : (l1, l2: List a) -> rev (l1 ++ l2) = rev l2 ++ rev l1
> rev_app_distr = ?rev_app_distr_proof

> rev_involutive : (l: List a) -> rev (rev l) = l
> rev_involutive = ?rev_involutive_proof

=== Polymorphic Pairs

  Following the same pattern, the type definition we gave in the last chapter
for pairs of numbers can be generalized to polymorphic pairs, often called
products:
