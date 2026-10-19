#set document(title: [Notes, and homework problems for Calculus III])
#set enum(numbering: "(1)")

#title()

= Basic linear algebra
== Homework set 1
From 1.5: 1, 4, 5 \
From 1.6: 1, 2, 3, 8a, 9, 10, 12, 15, 16

= Derivatives
== Homework set 2
2.1: 1, 2, 3, 4, 5, 7, 8 \
2.2: 1 \
3.1 1 \
3.2 6, 13, 15 \
3.4 10,11 \
4.1 2, 3, 4

= Maxima and minima
== Homework set 3
5.1: 5, 6, 12 \
5.2: 1, 2, 4, 5, 8

== Homework set 4
5.3: 1, 5, 6, 10, 12, 25

= Potential functions, line integrals
== Homework set 5
6.2: 3, 4 \
6.3: 7, 8, 9, 10 \
7.1: 1, 2 \
7.2: 5, 6, 8 \
8.1: 1, 2, 3

== Homework set 6
8.2: 1 \
8.3: 6,9, 15 \
9.2: 1:a,b,c,d, 2:a,b, 3

== Homework set 7
9.3: 1,2 \
10.1: 1:a,b,c, 2

= Surface Integrals Divergence and Stokes theorem
== Homework set 8
11.3: 1,2 \
12.1: 2 \
12.2: 1,2,3

== Homework set 9
12.3: 1:a,b, 12 \
12.5: 2,3,6 \
12.6: 7, 9

= Change of variables
== Homework set 10
1) Find the derivative a.k.a Jacobian $L' = D L$ of a linear map $L : RR^n -> R^m$. \
17.3: 1, 6, 8, 9 \
17.5: 1, 2, 3 (just use change of variables method), 4
/*
= Tangent bundle
== Sheafs, and Tangent bundle as derivations
A few clarifying points on sheafs, and derivations as tangent vectors that we went over
in class. We may define something like the tangent bundle
$cal(T)(X, cal(F))$ for a
somewhat
general sheaf of $RR$-algebras $cal(F)$ over $X$.
We shall make a few assumptions on $cal(F)$ to make this cleaner. First we shall
assume that $cal(F)(U)$ is a subalgebra of the algebra of
continuous functions on $U$ for each $U$. Second we shall assume the
following: for every $U$ and $p in U$ there is an $f in cal(F)(U)$, $f(p) = 1$, $"support" f subset U$.
We then define $cal(T)_p(X, cal(F))$ as the space of
$RR$-derivations: linear maps $l : cal(F)(U) -> RR$, $U in.rev p$, which
satisfy the Leibnitz rule: $l(f dot.op g) = l(f) g(p) + f(p) l(g)$.

Exercise 1: Use the second property of $cal(F)$ to show that if $f$ vanishes
in a neighborhood of $p$ and $l$ is a derivation then $l(f) = 0$.

Exercise 2: Show that $cal(T)_p X$ is well defined i.e. is
independent of $U$. (We really mean here that it is well defined up to
a natural isomorphism.)
(Hint: Use exercise 1.)

Exercise 3. Show that if $X = RR^n$ and the sheaf
$cal(F)$ is the sheaf of smooth functions then, $cal(T)_p RR^n$ is naturally isomorphic to $cal(T)_0 RR^n$ for each $p$. (Hint: use the pushforward map of
derivations that we discussed in class.)

We have already shown in class in $cal(T)_0 RR^n$
is naturally isomorphic to $RR^n$, in fact the natural
derivations $D_i |_0 = frac(partial, partial x_i) |_0$ are a basis.

Consequently we may get from this that for a smooth manifold $M$ defined as a
sheaf of $RR$-algebras on a topological space $M$, locally isomorphic to the sheaf of
$RR$-algebras of smooth functions on $RR^n$, there is a well
defined tangent bundle $cal(T) M$, which is a rank $n$ real
vector bundle, (fibers are $RR^n$) which is constructed with just
algebraic data. So there are no $C^oo$ related charts, atlases or other
such strange things. This story is equivalent to the other story of
smooth manifolds defined in terms of smooth atlases, with the
corresponding tangent bundle, defined in terms of equivalence classes
of smooth curves for example. And this is what we shall go back to.
Although it will sometimes still be convinient to speak in terms of
derivations, which of course still make sense in any case.

This completes our brief excursion into sheafs.

= Tangent bundle hw problems, due thurs
Ex1: Check that the Mobius band is a vector bundle over $S^1$,
i.e. check local triviality.
From Spivak Ch3:
ex 5 (pick any of the i, ii, iii),
10, 14.

= Cotangent bundle, due thurs
From Spivak: Ch4 1, 2, 3.

= Differential forms
Ex0: Let ${e_i}$ be the standard basis for $RR^n$
and let ${e_i^(*)}$ be the dual basis. Show that the
$n$-tensor $e_1^(*) and ... e_n^(*)$, is the
"determinant" tensor. Hint: you only need to know how they evaluate
on the standard basis, and then use skew-symmetry, multilinearity. \
Ex1: Check that the differential satisfies $d^2 = 0$. \
From Spivak, Ch 7, 27.

= Integration of differential forms
From Spivak ch 8: 2, 3, 4, 7.

= Stokes theorem
Ex0: Suppose that $M, N$ are without boundary. Show that if $f : M^k -> N$ is homotopic to $g$ then for a
$k$-form $omega$ on $N$ $integral_M f^(*) omega = integral_M g^(*) omega$. Hint: Consider first the case where support of $omega$
is in the interiour of the image of a singular cube $f compose c$, $c$
is a singular cube into $M$. Then look at
the new singular cube $f compose c times I -> N$ induced by the
homotopy what does Stokes theorem tell you?
(This allows us to
define degree without the much more difficult theorem 13, in Spivak,
which requires construction of something called "chain homotopy"). \
Spivak ch8: 9,13 \
*/
