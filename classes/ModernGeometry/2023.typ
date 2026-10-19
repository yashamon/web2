#set enum(numbering: "(1)")

my email: yashasavelyev\@gmail.com \
\
HW Set 1 for wed \
\
Kiselev: \
52, 53, 55, 60, 61, 67, 69, 75, 79, 89, 96, 97 \
\
HW Set 2 for wed \
104, 105, 106, 107, 113, 114, 141, 143, 145, 150 \
\
HW Set 3 for wed \
153, 154, 155, 158, 159, 178, 179, 180 \
\
HW Set 4 for wed \
From taste of topology: \
2.1: 1,2
2.3: 2,3 \
\
HW Set 5 for wed \
1) Sea $(X, d)$ un espacio metrico y sea $(X, L_d)$ un length space induced by $d$. Demuestra que: $ forall x, y thin forall gamma : d(x, y) <= L(gamma) $ where $gamma$ is a path from $x$ to $y$. \
\
2) Let $X = RR^2$ and $d_T$ the taxicab metric:
$ d_T(p_1, p_2) = | x_1 - x_2 | + | y_1 - y_2 | $ for $p_1 = (x_1, y_1)$ and $p_2 = (x_2, y_2)$.
Describe the minimal geodesics from $p_1$ to $p_2$ for $L_(d_T)$. \
\
3) Let $X = RR^2$, $d$ the Euclidean metric and
$d_P$ the Paris railroad metric with respect to $P in RR^2$. So:
$ d_P(p_1, p_2) = d(p_1, P) + d(p_2, P), $
where $d$ is the Euclidean metric, and $p_1, p_2 in RR^2$.

Describe the minimal geodesics from $p_1$ to $p_2$ for $L_(d_P)$. \
\
4) Sea $(RR^2, L)$ un length space. Vamos
a llamar un mapeo inyectivo $ gamma : RR -> RR^2 $ una *_recta_*, si cado segmento $gamma |_([a, b])$ de $gamma$ es un geodesico minimal al respecto de $L$. Cuales son rectas en $(RR^2, L_(d_P))$
y cuales son rectas en $(RR^2, L_(d_T))$? \
\
5) Con ese definición de las rectas se cumplen los axiomas de geometría de Euclid para $(RR^2, L_(d_T))$ y para $(RR^2, L_(d_P))$? Justify. \
\
HW set 6 for wed \
0) Show that for the Eucledian metric $d$ on $RR^2$
parallel transport along a segment from $A$ to $B$ is just
rigid translation by the map $RR^2 -> RR^2$, $C mapsto C + (B - A)$.
1) Let $phi.alt : (X, d_X) -> (Y, d_Y)$ be a surjective
isometry of metric spaces, so that $forall x, y in X : d_X(x, y) = d_Y(phi.alt(x), phi.alt(y))$. Show that

- $phi.alt$ is continuous.

- $phi.alt$ is injective.

- $phi.alt^(-1) : (Y, d_Y) -> (X, d_X)$ is also an
  isometry.

2) For $phi.alt$ as in problem 1. Show that $gamma : [a, b] -> X$ is
a minimal geodesic in $(X, L_(d_X))$ if and only if
$phi.alt compose gamma$ is a minimal geodesic in $(Y, L_(d_Y))$. \
\
3) Extra credit: Suppose that $X, Y$ are surfaces in $RR^3$ and $d_X, d_Y$ the natural metrics as discussed in class. For
$phi.alt : X -> Y$ as above, show that $phi.alt$ preserves angles between geodesics. \
\
4) Extra credit: Use the above to show that for $phi.alt$ as
in problem 3),
the holonomy around a closed piece-wise geodesic curve
$gamma$ in $X$ coincides with the holonomy around a closed
piece-wise geodesic curve $phi.alt compose gamma$ in $Y$.
Conclude that the zero curvature condition is preserved by
an isometry as in problem 3).
