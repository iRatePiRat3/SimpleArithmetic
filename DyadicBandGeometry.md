Dyadic Band Geometry for Affine–Valuation Dynamics
1. Introduction

We study a family of integer dynamical systems of the form

𝑇
𝑎
,
𝑏
(
𝑛
)
=
𝑎
𝑛
+
𝑏
2
𝑣
2
(
𝑎
𝑛
+
𝑏
)
,
T
a,b
	​

(n)=
2
v
2
	​

(an+b)
an+b
	​

,

defined on odd integers 
𝑛
n, where 
𝑎
≥
3
a≥3 is odd and 
𝑏
b is an integer (typically odd).
This class includes the odd-only formulation of the Collatz map (
𝑎
=
3
,
𝑏
=
1
a=3,b=1) but is considered here in full generality.

Rather than focusing on convergence properties, we introduce a dyadic coordinate system that separates:

scale (bit-length),

fractional position within scale,

and valuation discharge via 
𝑣
2
(
𝑎
𝑛
+
𝑏
)
v
2
	​

(an+b).

This coordinate framework makes explicit the geometric structure underlying affine–valuation maps and isolates the sole nonlocal mechanism driving band transitions.

2. Dyadic Band Coordinates
Definition 2.1 (Band index)

For 
𝑛
∈
𝑁
n∈N, define

𝑏
(
𝑛
)
=
⌊
log
⁡
2
𝑛
⌋
.
b(n)=⌊log
2
	​

n⌋.

Thus 
𝑛
n lies in the dyadic band

2
𝑏
(
𝑛
)
≤
𝑛
<
2
𝑏
(
𝑛
)
+
1
.
2
b(n)
≤n<2
b(n)+1
.
Definition 2.2 (Band scale)

Define the band scale

𝐵
(
𝑛
)
=
2
𝑏
(
𝑛
)
+
1
.
B(n)=2
b(n)+1
.
Definition 2.3 (Normalized coordinate)

Define the normalized dyadic coordinate

𝑥
(
𝑛
)
=
𝑛
𝐵
(
𝑛
)
∈
[
1
2
,
1
)
.
x(n)=
B(n)
n
	​

∈[
2
1
	​

,1).

This provides a bijective encoding

𝑛
⟷
(
𝑏
(
𝑛
)
,
𝑥
(
𝑛
)
)
,
n⟷(b(n),x(n)),

with 
𝑥
(
𝑛
)
x(n) a dyadic rational uniquely determined by 
𝑛
n.

Definition 2.4 (Remainder coordinate)

Define the within-band remainder

𝑟
(
𝑛
)
=
𝑛
−
2
𝑏
(
𝑛
)
,
0
≤
𝑟
(
𝑛
)
<
2
𝑏
(
𝑛
)
,
r(n)=n−2
b(n)
,0≤r(n)<2
b(n)
,

and the normalized remainder

𝑅
(
𝑛
)
=
𝑟
(
𝑛
)
𝐵
(
𝑛
)
∈
[
0
,
1
2
)
.
R(n)=
B(n)
r(n)
	​

∈[0,
2
1
	​

).

Then

𝑥
(
𝑛
)
=
1
2
+
𝑅
(
𝑛
)
.
x(n)=
2
1
	​

+R(n).

Thus 
𝑥
x and 
𝑅
R encode equivalent horizontal information.

3. Affine–Valuation Dynamics

Let 
𝑎
≥
3
a≥3 be odd and 
𝑏
b fixed. Define the odd-only affine–valuation map:

𝑇
𝑎
,
𝑏
(
𝑛
)
=
𝑎
𝑛
+
𝑏
2
𝑣
2
(
𝑎
𝑛
+
𝑏
)
,
𝑛
 odd
.
T
a,b
	​

(n)=
2
v
2
	​

(an+b)
an+b
	​

,n odd.

We analyze the effect of 
𝑇
𝑎
,
𝑏
T
a,b
	​

 in band coordinates.

4. Vertical Motion (Band Transitions)
Lemma 4.1 (Exact band identity)

For odd 
𝑛
n,

𝑏
(
𝑇
𝑎
,
𝑏
(
𝑛
)
)
=
𝑏
(
𝑎
𝑛
+
𝑏
)
−
𝑣
2
(
𝑎
𝑛
+
𝑏
)
.
b(T
a,b
	​

(n))=b(an+b)−v
2
	​

(an+b).
Proof

By definition,

𝑇
𝑎
,
𝑏
(
𝑛
)
=
𝑎
𝑛
+
𝑏
2
𝑣
2
(
𝑎
𝑛
+
𝑏
)
.
T
a,b
	​

(n)=
2
v
2
	​

(an+b)
an+b
	​

.

Taking binary logarithms,

log
⁡
2
𝑇
𝑎
,
𝑏
(
𝑛
)
=
log
⁡
2
(
𝑎
𝑛
+
𝑏
)
−
𝑣
2
(
𝑎
𝑛
+
𝑏
)
.
log
2
	​

T
a,b
	​

(n)=log
2
	​

(an+b)−v
2
	​

(an+b).

Taking floors yields the identity. ∎

Corollary 4.2 (Band displacement)

Define the band displacement

Δ
𝑏
(
𝑛
)
=
𝑏
(
𝑇
𝑎
,
𝑏
(
𝑛
)
)
−
𝑏
(
𝑛
)
.
Δb(n)=b(T
a,b
	​

(n))−b(n).

Then

Δ
𝑏
(
𝑛
)
=
𝑏
(
𝑎
𝑛
+
𝑏
)
−
𝑣
2
(
𝑎
𝑛
+
𝑏
)
−
𝑏
(
𝑛
)
.
Δb(n)=b(an+b)−v
2
	​

(an+b)−b(n).

Thus upward motion is governed by multiplication by 
𝑎
a, and downward motion by valuation discharge.

5. Logarithmic Drift Identity
Lemma 5.1 (Exact drift formula)

For odd 
𝑛
n,

log
⁡
2
𝑇
𝑎
,
𝑏
(
𝑛
)
=
log
⁡
2
𝑛
+
log
⁡
2
𝑎
−
𝑣
2
(
𝑎
𝑛
+
𝑏
)
+
𝜖
(
𝑛
)
,
log
2
	​

T
a,b
	​

(n)=log
2
	​

n+log
2
	​

a−v
2
	​

(an+b)+ϵ(n),

where

𝜖
(
𝑛
)
=
log
⁡
2
 ⁣
(
1
+
𝑏
𝑎
𝑛
)
.
ϵ(n)=log
2
	​

(1+
an
b
	​

).

Moreover,

∣
𝜖
(
𝑛
)
∣
≤
𝐶
𝑛
∣ϵ(n)∣≤
n
C
	​


for a constant 
𝐶
C depending only on 
𝑎
,
𝑏
a,b.

Interpretation

The asymptotic vertical drift is governed by

log
⁡
2
𝑎
−
𝑣
2
(
𝑎
𝑛
+
𝑏
)
.
log
2
	​

a−v
2
	​

(an+b).

All nontrivial behavior of the system is concentrated in the valuation term 
𝑣
2
(
𝑎
𝑛
+
𝑏
)
v
2
	​

(an+b).

6. Carry-Buffer Locality

We formalize the intuition that sufficiently large zero gaps prevent carry propagation across binary regions.

Lemma 6.1 (Carry-buffer locality for multiplication)

Let

𝑛
=
𝐻
⋅
2
𝑚
+
𝑡
+
𝑆
,
0
≤
𝑆
<
2
𝑚
,
𝑡
≥
1.
n=H⋅2
m+t
+S,0≤S<2
m
,t≥1.

Then

𝑎
𝑛
=
𝑎
𝐻
⋅
2
𝑚
+
𝑡
+
𝑎
𝑆
.
an=aH⋅2
m+t
+aS.

If

𝑎
𝑆
<
2
𝑚
+
𝑡
,
aS<2
m+t
,

then no binary carry from the lower block 
𝑎
𝑆
aS propagates into the higher block 
𝑎
𝐻
⋅
2
𝑚
+
𝑡
aH⋅2
m+t
.

In particular, the high-order bits of 
𝑎
𝑛
an coincide with those of 
𝑎
𝐻
⋅
2
𝑚
+
𝑡
aH⋅2
m+t
.

Proof

Binary carries propagate only when lower terms exceed the base threshold.
Since 
𝑎
𝑆
<
2
𝑚
+
𝑡
aS<2
m+t
, the addition of 
𝑎
𝑆
aS affects only bits below position 
2
𝑚
+
𝑡
2
m+t
.
Thus the upper block remains unaffected. ∎

Corollary 6.2 (Buffer condition for 
𝑎
=
3
a=3)

If

𝑛
=
𝐻
⋅
2
𝑚
+
𝑡
+
𝑆
,
0
≤
𝑆
<
2
𝑚
,
n=H⋅2
m+t
+S,0≤S<2
m
,

and 
𝑡
≥
2
t≥2, then

3
𝑆
<
3
⋅
2
𝑚
=
3
⋅
2
𝑚
<
2
𝑚
+
2
≤
2
𝑚
+
𝑡
,
3S<3⋅2
m
=3⋅2
m
<2
m+2
≤2
m+t
,

so carries from the tail cannot affect the head.

Thus a zero buffer of length at least 2 guarantees head stability under multiplication by 3.

7. Structural Interpretation

The affine–valuation map decomposes into three mechanisms:

Multiplicative expansion (controlled by 
𝑎
a).

Carry interaction (local vs cascading, governed by buffer size).

Valuation discharge (controlled by 
𝑣
2
(
𝑎
𝑛
+
𝑏
)
v
2
	​

(an+b)).

The dyadic band coordinate system cleanly separates:

vertical scale motion,

horizontal within-band position,

valuation-driven collapse.

This framework applies uniformly to all maps 
𝑇
𝑎
,
𝑏
T
a,b
	​

 and isolates the valuation term as the sole driver of long-term uncertainty.

8. Scope

This paper does not address convergence properties of any specific instance (including 
𝑎
=
3
,
𝑏
=
1
a=3,b=1).
Instead, it provides a geometric coordinate formalism for analyzing affine–valuation dynamics and formalizes carry-buffer phenomena governing binary locality.
