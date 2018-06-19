= Working with Structured Data

== Tuples of Numbers

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

> parameters (p: (Nat, Nat))
>     surjective_pairing_stuck : p = (fst p, snd p)
>     surjective_pairing_stuck = ?Refl -- Reflexivity doesn't work

  We have to expose the structure of `p` so that `Refl` can perform the pattern
match in `first` and `second`. We can do this destructuring.

> surjective_pairing : (p: (Nat, Nat)) -> p = (fst p, snd p)
> surjective_pairing (a, b) = Refl

  Notice that, unlike its behavior with `Nat`, destructuring generates just one
subgoal here. That's because Tuples can only be constructed in one way.

==== Exercise:

  1 star (`snd_fst_is_swap`)

> snd_fst_is_swap : (p: (Nat, Nat)) -> (snd p, fst p) = swap p
> snd_fst_is_swap = ?snd_fst_is_swap_proof

==== Exercise:

  1 star, optional (`fst_swap_is_snd`)

> fst_swap_is_snd : (p: (Nat, Nat)) -> fst (swap p) = snd p
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

=== Replicate

  A number of functions are useful for manipulating lists. For example, the
`replicate` function takes a number `c` and an number `n` and returns a list of
length `c` where every element is `n`.

```idris
replicate : Nat -> Nat -> List Nat
replicate Z     _ = []
replicate (S c) n = n :: (replicate n c)
```

=== Length

  The `length` function calculates the length of a list.

```idris
length : List Nat -> Nat
length  []    = Z
length (_::l) = S (length l)
```

=== Append

  The `++` function appends two lists.

```idris
infixl 7 ++
(++) : List Nat -> List Nat -> List Nat
(++)  []     l2 = l2
(++) (h::l1) l2 = h :: (l1 ++ l2)
```

  _Sidenote_: `++` will be used a lot in some parts of what follows.

> test_app1 : [1, 2, 3] ++ [4, 5] = [1, 2, 3, 4, 5]
> test_app1 = Refl

> test_app2 : [] ++ [4, 5] = [4, 5]
> test_app2 = Refl

> test_app3 : [1, 2, 3] ++ [] = [1, 2, 3]
> test_app3 = Refl

=== Head and Tail

  Here are two smaller examples of programming with lists. The `head` function
returns the first element (the "head") of the list, while `tail` returns
everything but the first element (the "tail"). Of course, the empty list has no
first element, so we must restrict the argument to lists with at least 1 element
--- or Non-Empty lists. Doing so will _restrict_ the domain of head to `NonEmpty`
lists.

  <!--- TODO: Add further explanation on NonEmpty / Restricting Domains -->

```idris
data NonEmpty : List Nat -> Type where
     -- The only constructor only works for a List with a cons(::)
     IsNonEmpty : NonEmpty (_::_)
```

  We have to show Idris explicitly that `NonEmpty []` is impossible with the
given definition.

```idris
Uninhabited (NonEmpty []) where
    uninhabited IsNonEmpty impossible
```


```idris
head : (l: List Nat) -> {auto ok: NonEmpty l} -> Nat
head  []    impossible
head (h::_) = h
```

> test_head : head [1, 2, 3] = 1
> test_head = Refl

  However, attempting to evaluate a `Nil` will result in a _Type Error_ **not**
a _Runtime Error_. This also means that when using `head` in a program, we will
to show the type system that we are not passing an empty list.

```idris
...> head []
(input):1:1-6:When checking argument ok to function Main.hd:
        Can't find a value of type
                NonEmpty []
```

  `tail` is more straightforward.

```idris
tail : List Nat -> List Nat
tail  []    = []
tail (_::l) = l
```

> test_tail : tail [1, 2, 3] = [2, 3]
> test_tail = Refl

=== Exercises

==== Exercise:

  2 stars, recommended (`list_funs`)

  Complete the definitions of `nonZeros`, `oddMembers` and `countOddMembers`
below. Have a look at the tests to understand what these functions should do.

\ignore {

> -- This is a gift function
> odd : Nat -> Bool
> odd  Z    = False
> odd (S n) = not (odd n)

}

> nonZeros : List Nat -> List Nat
> nonZeros = ?nonZeros_def

> test_nonZeros : nonZeros [0, 1, 0, 2, 3, 0, 0] = [1, 2, 3]
> test_nonZeros = ?nonZeros1

> oddMembers : List Nat -> List Nat
> oddMembers = ?oddMembers_def

> test_oddMembers : oddMembers [0, 1, 0, 2, 3, 0, 0] = [1, 3]
> test_oddMembers = ?oddMembers1

> countOddMembers : List Nat -> Nat
> countOddMembers = ?countOddMembers_def

> test_countOddMembers1 : countOddMembers [1, 0, 3, 1, 4, 5] = 4
> test_countOddMembers1 = ?countOddMembers1
> test_countOddMembers2 : countOddMembers [0, 2, 4] = 0
> test_countOddMembers2 = ?countOddMembers2
> test_countOddMembers3 : countOddMembers [] = 0
> test_countOddMembers3 = ?countOddMembers3

==== Exercise:

  3 stars, advanced (`alternate`)

  Complete the definition of `alternate`, which "zips up" two lists into one,
alternating between elements taken from the first list and elements from the
second. See the tests below for more specific examples.

> alternate : List Nat -> List Nat -> List Nat
> alternate = ?alternate_def

> test_alternate1 : alternate [1, 2, 3] [4, 5, 6] = [1, 4, 2, 5, 3, 6]
> test_alternate1 = ?alternate1
> test_alternate2 : alternate [1] [4, 5, 6] = [1, 4, 5, 6]
> test_alternate2 = ?alternate2
> test_alternate3 : alternate [1, 2, 3] [4] = [1, 4, 2, 3]
> test_alternate3 = ?alternate3
> test_alternate4 : alternate [] [20, 30] = [20, 30]
> test_alternate4 = ?alternate4

=== Bags via Lists

  A bag (or multiset) is like a set, except that each element can appear
multiple times rather than just once. One possible implementation is to
represent a bag of numbers as a list.

> Bag : Type
> Bag = List Nat

==== Exercise:

  3 stars, recommended (`bag_functions`)

  Complete the following definitions for the functions `count`, `sum`, `add`,
and `member` for bags.

> count : Nat -> Bag -> Nat
> count = ?count_def

> test_count1 : count 1 [1, 2, 3, 1, 4, 1] = 3
> test_count1 = ?count1
> test_count2 : count 6 [1, 2, 3, 1, 4, 1] = 0
> test_count2 = ?count2

  Multiset `sum` is similar to set union: `sum a b` contains all the elements of
`a` and of `b`. (Mathematicians usually define union on multisets a little bit
differently --- using max instead of sum --- which is why we don't use that name
for this operation.) You are encouraged to think about whether `sum` can be
implemented in another way --- perhaps by using functions that have already been
defined.

> sum : Bag -> Bag -> Bag
> sum = ?sum_def

> test_sum1 : count 1 (sum [1, 2, 3] [1, 4, 1]) = 3
> test_sum1 = ?sum1


> add : Nat -> Bag -> Bag
> add = ?add_def

> test_add1 : count 1 (add 1 [1, 4, 1]) = 3
> test_add1 = ?add1
> test_add2 : count 5 (add 1 [1, 4, 1]) = 0
> test_add2 = ?add2

> member : Nat -> Bag -> Bool
> member = ?member_def

> test_member1 : member 1 [1, 4, 1] = True
> test_member1 = ?member1
> test_member2 : member 2 [1, 4, 1] = False
> test_member2 = ?member2

==== Exercise:

  3 stars, optional (`bag_more_functions`)

  Here are some more bag functions for you to practice with.

  When `remove_one` is applied to a `Bag` without the number to remove, it
should return the same `Bag` unchanged.

> remove_one : Nat -> Bag -> Bag
> remove_one = ?remove_one_def

> test_remove_one1 : count 5 (remove_one 5 [2, 1, 5, 4, 1]) = 0
> test_remove_one1 = ?remove_one1
> test_remove_one2 : count 5 (remove_one 5 [2, 1, 4, 1]) = 0
> test_remove_one2 = ?remove_one2
> test_remove_one3 : count 4 (remove_one 5 [2, 1, 4, 5, 1, 4]) = 2
> test_remove_one3 = ?remove_one3
> test_remove_one4 : count 5 (remove_one 5 [2, 1, 5, 4, 5, 1, 4]) = 0
> test_remove_one4 = ?remove_one4

> remove_all : Nat -> Bag -> Bag
> remove_all = ?remove_all_def

> test_remove_all1 : count 5 (remove_all 5 [2, 1, 5, 4, 1]) = 0
> test_remove_all1 = ?remove_all1
> test_remove_all2 : count 5 (remove_all 5 [2, 1, 4, 1]) = 0
> test_remove_all2 = ?remove_all2
> test_remove_all3 : count 4 (remove_all 5 [2, 1, 4, 5, 1, 4]) = 2
> test_remove_all3 = ?remove_all3
> test_remove_all4 : count 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0
> test_remove_all4 = ?remove_all4

> subset : Bag -> Bag -> Bool
> subset = ?subset_def

> test_subset1 : subset [1, 2] [2, 1, 4, 1] = True
> test_subset1 = ?subset1
> test_subset2 : subset [1, 2, 2] [2, 1, 4, 1] = False
> test_subset2 = ?subset2

==== Exercise:

  3 stars, recommended (`bag_theorem`)

  Write down an interesting theorem `bag_theorem` about bags involving the
functions count and add, and prove it. Note that, since this problem is somewhat
open-ended, it's possible that you may come up with a theorem which is true, but
whose proof requires techniques you haven't learned yet. Feel free to ask for
help if you get stuck!

> -- Code here

== Reasoning About Lists
