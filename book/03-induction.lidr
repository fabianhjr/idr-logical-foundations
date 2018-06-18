= Proof by Induction

  We proved in the last chapter that `Z` is a neutral element for `+` on the
left, using an easy argument based on simplification. We should observe that
proving the fact that it is also a neutral element on the right...

> parameters (n: Nat)
>     plus_n_0_firsttry : n + 0 = n
>     plus_n_0_firsttry = ?Refl -- Reflexivity doesn't work.

  ...can't be done in the same simple way. Just applying reflexivity doesn't
work, since the `n` in `n + 0` is an arbitrary unknown number, so the match in
the definition of + can't be simplified.

  And reasoning by cases using destructuring doesn't get us much further: the
branch of the case analysis where we assume n = 0 goes through fine, but in the
branch where n = S n' for some n' we get stuck in exactly the same way.

> plus_n_0_secondtry : (n: Nat) -> n + 0 = n
> plus_n_0_secondtry  Z    = Refl
> plus_n_0_secondtry (S n) = ?Refl -- Reflexivity doesn't work.

  We could destructure one more time to get one step further, but, since `n` can
be arbitrarily large, if we just go on like this we'll never finish.

  To prove interesting facts about numbers, lists, and other inductively defined
sets, we usually need a more powerful reasoning principle: induction.

  Recall (from high school, a discrete math course, etc.) the principle of
induction over natural numbers: If `P(n)` is some proposition involving a
natural number `n` and we want to show that `P` holds for all numbers `n`, we
can reason like this:

  - Show that `P(O)` holds;
  - Show that, for any `n'`, if `P(n')` holds, then so does `P(S n')`;
  - Conclude that `P(n)` holds for all `n`.

  In Idris, the steps are the same: we begin with the goal of proving `P(n)` for
all `n` and break it down into two separate subgoals: one where we must show
`P(Z)` and another where we must show `P(n')` $\rightarrow$ `P(S n')`. Here's
how this works for the theorem at hand:

> plus_n_0 : (n: Nat) -> n + 0 = n
> plus_n_0  Z    = Refl
> plus_n_0 (S n) = let inductiveHipothesis = plus_n_0 n in
>                  rewrite inductiveHipothesis in Refl

  In the second subgoal we destructure `S n`, and add the assumption `n + 0 = n`
to the context with the name inductiveHipothesis. The goal in this case becomes
`S n = (S n) + 0`, which simplifies to S n = S (n + 0), which in turn follows
from rewritting the inductiveHipothesis (`n + 0 = n`).

> minus_diag : (n: Nat) -> minus n n = 0
> minus_diag  Z    = Refl
> minus_diag (S n) = let inductiveHipothesis = minus_diag n in
>                    rewrite inductiveHipothesis in Refl

==== Exercise: 2 stars, recommended (basic_induction)

  Prove the following using induction. You might need previously proven results:

> mult_0_r : (n: Nat) -> n * 0 = 0
> mult_0_r = ?mult_0_r_proof

> plus_n_Sm : (n, m: Nat) -> n + (S m) = S (n + m)
> plus_n_Sm = ?plus_n_Sm_proof

> plus_comm : (n, m: Nat) -> n + m = m + n
> plus_comm = ?plus_comm_proof

> plus_assoc : (n, m, p: Nat) -> n + (m + p) = (n + m) + p
> plus_assoc = ?plus_assoc_proof

==== Exercise: 2 stars (double_plus)

  Consider the following function, which doubles its argument:

> double : Nat -> Nat
> double  Z    = Z
> double (S n) = S (S (double n))

  Use induction to prove this simple fact about `double`:

> double_plus : (n: Nat) -> double n = n + n
> double_plus = ?double_plus_proof

==== Exercise: 2 stars, optional (evenb_S)

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
