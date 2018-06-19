= Working with Structured Data

\long\def\ignore#1{}

\ignore{

> import Prelude.Uninhabited

}

== Pairs of Numbers

  In an Inductive type definition, each constructor can take any number of
arguments --- none (as with `True` and `Zero`), one (as with `S`), or more than
one, as here:

> data NatProd = Pair Nat Nat

  This declaration can be read: "There is just one way to construct a pair of
numbers: by applying the constructor Pair to two arguments of type Nat."

```idris
...> :t Pair 3 5
Pair 3 5 : NatProd
```

  Here are two simple functions for extracting the first and second components
of a pair. The definitions also illustrate how to do pattern matching on
two-argument constructors.

> first : NatProd -> Nat
> first (Pair a _) = a

> second : NatProd -> Nat
> second (Pair _ b) = b

> swap_pair : NatProd -> NatProd
> swap_pair (Pair a b) = Pair b a

```idris
...> first (Pair 3 5).
3 : Nat
```

  Since pairs are used quite a bit, it is nice to be able to write them with the
  standard mathematical notation $(x, y)$ instead of `Pair x y`. (we've actually
seen this already in the Basics chapter --- this works because the pair notation
is also provided as part of the standard library)

```idris
...> fst (3, 5)
3 : Integer
```

  Let's try to prove a few simple facts about pairs.

  If we state things in a particular (and slightly peculiar) way, we can
complete proofs with just reflexivity (and its built-in simplification):

> parameters (n, m: Nat)
>     surjective_pairing' : (n, m) = (fst (n, m), snd (n, m))
>     surjective_pairing' = Refl

  But reflexivity is not enough if we state the lemma in a more natural way:

> parameters (p: NatProd)
>     surjective_pairing_stuck : p = Pair (first p) (second p)
>     surjective_pairing_stuck = ?Refl -- Reflexivity doesn't work

  We have to expose the structure of `p` so that `Refl` can perform the pattern
match in `first` and `second`. We can do this destructuring.

> surjective_pairing : (p: NatProd) -> p = Pair (first p) (second p)
> surjective_pairing (Pair a b) = Refl

  Notice that, unlike its behavior with `Nat`, destructuring generates just one
subgoal here. That's because NatProds can only be constructed in one way.

==== Exercise:

  1 star (`snd_fst_is_swap`)

> snd_fst_is_swap : (p: NatProd) -> Pair (second p) (first p) = swap_pair p
> snd_fst_is_swap = ?snd_fst_is_swap_proof

==== Exercise:

  1 star, optional (`fst_swap_is_snd`)

> fst_swap_is_snd : (p: NatProd) -> first (swap_pair p) = second p
> fst_swap_is_snd = ?fst_swap_is_snd_proof

== Lists of Numbers

  Generalizing the definition of pairs, we can describe the type of lists of
numbers like this: "A list is either the empty list or else a pair of a number
and another list."

> data NatList = Nil
>              | Cons Nat NatList

  For example, here is a three-element list:

> my_list : NatList
> my_list = Cons 1 (Cons 2 (Cons 3 Nil))

  As with pairs, it is more convenient to write lists in familiar programming
notation. Idris uses `::` as an infix cons operator and square brackets as a
postfix notation for constructing lists. For example, the next three
declarations mean exactly the same thing:

> my_list_1 : List Nat
> my_list_1 = 1 :: (2 :: (3 :: []))

> my_list_2 : List Nat
> my_list_2 = 1 :: 2 :: 3 :: []

> my_list_3 : List Nat
> my_list_3 = [1, 2, 3]

=== Repeat

  A number of functions are useful for manipulating lists. For example, the
`repeat` function takes a number n and a count and returns a list of length
`c` where every element is `n`.

> repeat : Nat -> Nat -> NatList
> repeat _  Z    = Nil
> repeat n (S c) = Cons n (repeat n c)

=== Length

  The `length` function calculates the length of a list.

> length : NatList -> Nat
> length Nil        = Z
> length (Cons _ l) = S (length l)

=== Append

  The `app` function concatenates (appends) two lists.

> app : NatList -> NatList -> NatList
> app  Nil        l2 = l2
> app (Cons h l1) l2 = Cons h (app l1 l2)

  Actually, `app` will be used a lot in some parts of what follows, so it is
convenient to have an infix operator for it. Idris uses `++`.

> test_app1 : [1, 2, 3] ++ [4, 5] = [1, 2, 3, 4, 5]
> test_app1 = Refl

> test_app2 : [] ++ [4, 5] = [4, 5]
> test_app2 = Refl

> test_app3 : [1, 2, 3] ++ [] = [1, 2, 3]
> test_app3 = Refl

=== Head and Tail

  Here are two smaller examples of programming with lists. The hd function
returns the first element (the "head") of the list, while tl returns everything
but the first element (the "tail"). Of course, the empty list has no first
element, so we must restrict the domain.

  <!--- TODO: Add further explanation on NonEmpty / Restricting Domains -->

> data NonEmptyNatList : NatList -> Type where
>      -- The only constructor only works for a NatList with a Cons
>      IsNonEmpty : NonEmptyNatList (Cons _ _)

> Uninhabited (NonEmptyNatList Nil) where
>     uninhabited IsNonEmpty impossible

> hd : (l: NatList) -> {auto ok: NonEmptyNatList l} -> Nat
> hd  Nil       impossible
> hd (Cons e _) = e

> test_hd1 : hd (Cons 1 (Cons 2 (Cons 3 Nil))) = 1
> test_hd1 = Refl

  However, attempting to evaluate a `Nil` will result in a _Type Error_ **not**
a _Runtime Error_. This also means that when using hd in a program, we will be
required by the type system to ensure we are not passing an empty list.

```idris
...> hd Nil
(input):1:1-6:When checking argument ok to function Main.hd:
        Can't find a value of type
                NonEmptyNatList []
```

> tl : NatList -> NatList
> tl  Nil       = Nil
> tl (Cons _ l) = l

> test_tl : tl (Cons 1 (Cons 2 (Cons 3 Nil))) = (Cons 2 (Cons 3 Nil))
> test_tl = Refl
