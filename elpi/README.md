A tiny proof assistant for local set theory in ELPI, with Hilbert/Frege/Gentzen(?) style proofs.

That is, a proof is a sequence of statements
```
Hn,
H(n-1),
...,
H1,
H0
```
such that for each k,
```
H0, H1, ..., H(k-1) ⊢ Hk
```
is derivable in one step, either by an axiom or by a lemma.

A theorem is declared by
```
(pi x1 ... xn \
 (thm [hyps] conc
  [proof]))
```
where `x1, ..., xn` are free variables that appear in both the hypothesis and conclusion.

Once a theorem is proven, a lemma may be declared by
```
lemma (name) conc H :- sublist hyps H.
```

The theory (axioms) is defined in `theory.elpi`.

Theorems and proofs are defined in `theorems.elpi`.

Example output is given in `saved-output.txt`.


To run: (last tested with [`ELPI`](https://github.com/LPCIC/elpi) 1.13.1 from opam)

```
elpi -exec regression theorems.elpi
```