#set document(title: [Notes for differential geometry course, Colima (to be updated)], author: "Yasha Savelyev")
#set enum(numbering: "(1)")

#title()

Yasha Savelyev, #link("mailto:yasha.savelyev@gmail.com")

= Introduction
This will be a course in differential geometry with the ultimate goal
of proving the global Gauss-Bonnet theorem for surfaces. The input for
this theorem is
a surface $(S, g)$ where $g$ is a Riemannian metric, which is
an inner product the tangent vector spaces $T_s S$ which is varying
smoothly in $s$. It will be often
convinient and we shall make much use of this, to think of our surface
being embedded in $RR^3$, or $RR^n$ and of the metric being induced
from the ambient space. But unlike many introductory courses in
differential geometry our approach will non-the-less be intrinsic, so
ultimately independent of any such embeddings. This will mean that we
are going to have to learn a bit about things like smooth manifolds,
the tangent bundle, and differential forms on manifolds. Learning these extra bits of
abstraction will most definitely be worth it. For the moment you are
definitely encouraged to look at some supplimentary material to build
your intuition for example:
#link("https://www.google.com.mx/url?sa=t&rct=j&q=&esrc=s&source=web&cd=1&cad=rja&uact=8&ved=0ahUKEwjOq_OnxLHLAhXlm4MKHXGvB-oQFggbMAA&url=https%3A%2F%2Fmath.berkeley.edu%2F~giventh%2Fdifgem.pdf&usg=AFQjCNE7B1_IqYO1343Dgf4VGEAHHLp87Q")[Givental]
(click me). I am going to add more in the future.

The global Gauss-Bonnet theorem will relate
the integral of the curvature over
the surface, which in particular depends on the data of a Riemannian
metric $g$ on $S$ to its Euler characteristic which is a topological,
metric independent invariant of the surface. This is a special case of
the celebrated Atiyah-Singer theorem, one of the most important
theorems of 20th century.
The global Gauss-Bonnet theorem has a higher
dimensional analogue, we may have time to at least state it, but will
probably not attempt to prove it.

To give you a heads up we are not going to go particularly fast, but the
material can be "deep" in places, so will require you to actively think about some
concepts in your spare time.

= Manifolds, and smooth structures
This will follow Spivak: A comprehensive introduction to differential
geometry Vol I. The first three chapters. You may also take a look at
Spivak: Calculus on manifolds.

== Homework set 1
From Chapter 1: Problems 9, 16, 20.
From Chapter 2: 1,4, 23.
Check that diffeomorphisms are homeomorphisms, and that the
inverse of a diffeomorphism is a diffeomorphism, we mentioned
this in class. (As we defined them.)

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
Spivak ch8: 9,13
