= Proof by Induction

== Proof by Induction

  We proved in the last chapter that `Z` is a neutral element for `+` on the
left, using an easy argument based on simplification. We should observe that
proving the fact that it is also a neutral element on the right...

> parameters (n: Nat)
>     plus_n_0_firsttry : n + 0 = n
>     plus_n_0_firsttry = ?Refl -- Refl will error

-----

==== Error

```idris
    |
... | >     plus_n_0_firsttry = Refl
    |                           ~~~~
When checking right hand side of Main.plus_n_0_firsttry with expected type
        n + 0 = n

Type mismatch between
        n = n (Type of Refl)
and
        plus n 0 = n (Expected type)

Specifically:
        Type mismatch between
                n
        and
                plus n 0
```

-----

  ...can't be done in the same simple way. Just applying reflexivity doesn't
work, since the `n` in `n + 0` is an arbitrary unknown number, so the match in
the definition of + can't be simplified.

  And reasoning by cases using destructuring doesn't get us much further: the
branch of the case analysis where we assume n = 0 goes through fine, but in the
branch where n = S n' for some n' we get stuck in exactly the same way.

> plus_n_0_secondtry : (n: Nat) -> n + 0 = n
> plus_n_0_secondtry  Z    = Refl
> plus_n_0_secondtry (S n) = ?Refl -- Refl will error

-----

==== Error

```idris
    |
... | > plus_n_0_secondtry (S n) = Refl
    |                              ~~~~
When checking right hand side of plus_n_0_secondtry with expected type
        S n + 0 = S n

Type mismatch between
        S n = S n (Type of Refl)
and
        S (plus n 0) = S n (Expected type)

Specifically:
        Type mismatch between
                n
        and
                plus n 0
```

-----

  We could destructure one more time to get one step further, but, since `n` can
be arbitrarily large, if we just go on like this we'll never finish.

  To prove interesting facts about numbers, lists, and other inductively defined
sets, we usually need a more powerful reasoning principle: induction.

  Recall (from high school, a discrete math course, etc.) the principle of
induction over natural numbers: If `P(n)` is some proposition involving a
natural number `n` and we want to show that `P` holds for all numbers `n`, we
can reason like this:

  - Show that `P(Z)` holds;
  - Show that, for any `n`, if `P(n)` holds, then so does `P(S n)`;
  - Conclude that `P(n)` holds for all `n`.

  In Idris, the steps are the same: we begin with the goal of proving `P(n)` for
all `n` and break it down into two separate subgoals: one where we must show
`P(Z)` and another where we must show `P(n)` $\rightarrow$ `P(S n)`. Here's
how this works for the theorem at hand:

> plus_n_0 : (n: Nat) -> n + 0 = n
> plus_n_0  Z    = Refl
> plus_n_0 (S n) = rewrite plus_n_0 n in Refl

  In the second subgoal we destructure `S n`, and add the assumption `n + 0 = n`
to the context by rewritting the hypothesis into Refl. The goal in this case
becomes `S n = (S n) + 0`, which simplifies to S n = S (n + 0), which in turn
follows from the inductive hypothesis.

> minus_diag : (n: Nat) -> minus n n = 0
> minus_diag  Z    = Refl
> minus_diag (S n) = rewrite minus_diag n in Refl

==== Exercise:

  2 stars, recommended (`basic_induction`)

  Prove the following using induction. You might need previously proven results:

> mult_0_r : (n: Nat) -> n * 0 = 0
> mult_0_r = ?mult_0_r_proof

> plus_n_Sm : (n, m: Nat) -> n + (S m) = S (n + m)
> plus_n_Sm = ?plus_n_Sm_proof

> plus_comm : (n, m: Nat) -> n + m = m + n
> plus_comm = ?plus_comm_proof

> plus_assoc : (n, m, p: Nat) -> n + (m + p) = (n + m) + p
> plus_assoc = ?plus_assoc_proof

==== Exercise:

  2 stars (`double_plus`)

  Consider the following function, which doubles its argument:

> double : Nat -> Nat
> double  Z    = Z
> double (S n) = S (S (double n))

  Use induction to prove this simple fact about `double`:

> double_plus : (n: Nat) -> double n = n + n
> double_plus = ?double_plus_proof

==== Exercise:

  2 stars, optional (`even_S`)

  Recall our definition of `even n`:

> even : Nat -> Bool
> even  Z    = True
> even (S Z) = False
> even (S (S n')) = even n'

  One inconvenient aspect of our definition of `even n` is the recursive call on
`n - 2`. This makes proofs about `even n` harder when done by induction on `n`,
since we may need an induction hypothesis about `n - 2`. The following lemma
gives an alternative characterization of `even (S n)` that works better with
induction:

> even_S : (n: Nat) -> even (S n) = not (even n)
> even_S = ?even_S_proof

==== Exercise:

  1 star (`destruct_induction`)

  Briefly explain the difference between destructuring and induction.

== Proofs Within Proofs

  In Idris, as in informal mathematics, large proofs are often broken into a
sequence of theorems, with later proofs referring to earlier theorems. But
sometimes a proof will require some miscellaneous fact that is too trivial and
of too little general interest to bother giving it its own top-level name. In
such cases, it is convenient to be able to simply state and prove the needed
"sub-theorem" right at the point where it is used.

> parameters (n, m: Nat)
>     mult_plus_0 : (n + 0) * m = n * m
>     mult_plus_0 = rewrite plus_n_0 n in Refl

  For example, suppose we want to prove that `(n + m) + (p + q) = (m + n) +
(p + q)`. The only difference between the two sides of the `=` is that the
arguments `m` and `n` to the first inner `+` are swapped, so it seems we should
be able to use the commutativity of addition (`plus_comm`) to rewrite one into
the other. However, the `rewrite` tactic is not very smart about where it
applies the rewrite. There are three uses of `+` here. To use `plus_comm` at the
point where we need it, we can introduce a local lemma stating that `n + m =
m + n` (for the particular `m` and `n` that we are talking about here), prove
this lemma using `plus_comm`, and then use it to do the desired rewrite.

  <!--- TODO: Better example -->

> parameters (n, m, p, q: Nat)
>     plus_rearrange : (n + m) + (p + q) = (m + n) + (p + q)
>     plus_rearrange = let aux_lemma = plus_comm n m in
>                      rewrite aux_lemma in Refl

== Formal vs. Informal Proof

 > Informal proofs are algorithms; formal proofs are code.

  What constitutes a successful proof of a mathematical claim? The question has
challenged philosophers for millennia, but a rough and ready definition could be
this: A proof of a mathematical proposition `P` is a written (or spoken) text
that instills in the reader or hearer the certainty that `P` is true --- an
unassailable argument for the truth of P. That is, a proof is an act of
communication.

  Acts of communication may involve different sorts of readers. On one hand, the
"reader" can be a program like Idris, in which case the "belief" that is
instilled is that `P` can be mechanically derived from a certain set of formal
logical rules, and the proof is a recipe that guides the program in checking
this fact. Such recipes are _formal proofs_.

  Alternatively, the reader can be a human being, in which case the proof will
be written in English or some other natural language, and will thus necessarily
be _informal_. Here, the criteria for success are less clearly specified. A
"valid" proof is one that makes the reader believe `P`. But the same proof may
be read by many different readers, some of whom may be convinced by a particular
way of phrasing the argument, while others may not be. Some readers may be
particularly pedantic, inexperienced, or just plain thick-headed; the only way
to convince them will be to make the argument in painstaking detail. But other
readers, more familiar in the area, may find all this detail so overwhelming
that they lose the overall thread; all they want is to be told the main ideas,
since it is easier for them to fill in the details for themselves than to wade
through a written presentation of them. Ultimately, there is no universal
standard, because there is no single way of writing an informal proof that is
guaranteed to convince every conceivable reader.

  In practice, however, mathematicians have developed a rich set of conventions
and idioms for writing about complex mathematical objects that --- at least
within a certain community --- make communication fairly reliable. The
conventions of this stylized form of communication give a fairly clear standard
for judging proofs good or bad.

  Because we are using Idris in this course, we will be working heavily with
formal proofs. But this doesn't mean we can completely forget about informal
ones! Formal proofs are useful in many ways, but they are _not_ very efficient
ways of communicating ideas between human beings.

  For example, here is a proof that addition is associative:

> parameters (m, p: Nat)
>     plus_assoc' : (n: Nat) -> n + (m + p) = (n + m) + p
>     plus_assoc' Z     = Refl
>     plus_assoc' (S n) = rewrite plus_assoc' n in Refl

  Idris is perfectly happy with this. For a human, however, it is difficult to
make much sense of it. We can use comments and bullets to show the structure a
little more clearly...

> parameters (m, p: Nat)
>     plus_assoc'' : (n: Nat) -> n + (m + p) = (n + m) + p
>     plus_assoc''  Z    =
>         -- If n=0 then 0 + (m + p) = m + p and (0 + m) + p = (m) + p.
>         Refl
>     plus_assoc'' (S n) =
>         -- If n = S n' then use the inductive hypothesis.
>         rewrite plus_assoc'' n in Refl

  ...and if you're used to Idris you may be able to step through the tactics one
after the other in your mind and imagine the state of the context and goal stack
at each point, but if the proof were even a little bit more complicated this
would be next to impossible.

  A (pedantic) mathematician might write the proof something like this:

  **Theorem**: For any $n$, $m$ and $p$ natural numbers, $n + (m + p) = (n + m)
  + p$

  **Proof**: By induction on $n$

  - First, suppose $n = 0$. We must show:

    $$0 + (m + p) = (0 + m) + p$$

    This follows directly from the definition of $+$.

  - Next, suppose $n = S n'$, where

    $$n' + (m + p) = (n' + m) + p$$

    - We must show

      $$(S n') + (m + p) = ((S n') + m) + p$$

    - By the definition of $+$, this follows from

      $$S (n' + (m + p)) = S ((n' + m) + p)$$

      which is immediate from the induction hypothesis.

  $\Box$

  The overall form of the proof is basically similar, and of course this is no
accident: Idris proofs are structured the same way a mathematician would write.
But there are significant differences of detail: the formal proof is much more
explicit in some ways (e.g., the use of reflexivity) but much less explicit in
others (in particular, the "proof state" at any given point in the Idris proof
is completely implicit, whereas the informal proof reminds the reader several
times where things stand).

==== Exercise:

  2 stars, advanced, recommended (`plus_comm_informal`)

  Translate your solution for plus_comm into an informal proof:

  **Theorem**: Addition is commutative.

  **Proof**: _add your proof here_

  $\Box$

==== Exercise:

  2 stars, optional (`eq_nat_refl_informal`)

  Write an informal proof of the following theorem, using the informal proof of
`plus_assoc` as a model. Don't just paraphrase the Idris code into English!

  **Theorem**: For any $n$, $n=n$

  **Proof**: _add your proof here_

  $\Box$
