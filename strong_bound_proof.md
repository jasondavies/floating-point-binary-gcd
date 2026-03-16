# Strong-Bound Admissibility Proof

## Scope

This proof is for the reduced forward dynamics, which is exactly the setting
used by the reverse search: every non-root reverse-search state is reduced,
meaning `gcd(a, b) = 1`, with `a >= b > 0`.

That is the only setting needed for admissibility of the pruning bound inside
the reduced reverse graph.

## Definitions

Let `(a, b)` be a reduced state with `a >= b > 0`. Write

- `M(a, b) = max(bitlen(a), bitlen(b))`
- `e(a, b) = bitlen(a) - bitlen(b)`
- `bitlen(0) = 0`

For one forward step, define

- `e = e(a, b)`
- `t = 2^e b`
- `r = |a - t|`

and then map

`(a, b) -> (max(b, r), min(b, r))`,

followed by normalization by the gcd.

The target bound is

`min_drop_for_steps_strong(s) = 3 * floor(s / 5) + rho(s mod 5)`,

where

- `rho(0) = 0`
- `rho(1) = 0`
- `rho(2) = 1`
- `rho(3) = 1`
- `rho(4) = 2`

Equivalently,

- `min_drop_for_steps_strong(0) = 0`
- `min_drop_for_steps_strong(1) = 0`
- `min_drop_for_steps_strong(2) = 1`
- `min_drop_for_steps_strong(3) = 1`
- `min_drop_for_steps_strong(4) = 2`
- `min_drop_for_steps_strong(5) = 3`

and then periodic with slope `3/5`.

The theorem to prove is:

> For every valid forward trajectory of reduced states of length `s`, the top
> bit-length drops by at least
> `min_drop_for_steps_strong(s)`.

In other words, if `(a_0, b_0) -> (a_1, b_1) -> ... -> (a_s, b_s)` is any
valid forward trajectory through reduced states, with `a_i >= b_i > 0` for
`0 <= i < s` and `a_s >= b_s >= 0`, then

`M(a_0, b_0) - M(a_s, b_s) >= min_drop_for_steps_strong(s)`.

## 1. Normalization is trivial on reduced states

### Lemma 1

If `gcd(a, b) = 1`, then after one unreduced step the output pair is also
coprime. Hence the normalization factor is `1`.

### Proof

Let `e = bitlen(a) - bitlen(b)` and `r = |a - 2^e b|`. Then

`gcd(b, r) = gcd(b, a - 2^e b) = gcd(b, a) = 1`.

Reordering does not change the gcd, so the unreduced output
`(max(b, r), min(b, r))` is already coprime. Therefore normalization does
nothing. `qed`

### Consequence

Starting from a reduced state, every later state is reduced, and the forward
dynamics are exactly the unreduced algebra. So from this point on the proof
may ignore normalization entirely.

This is stronger than "normalization only helps": in the reduced search space,
normalization is always trivial.

## 2. The two-step lemma

### Lemma 2

If `e(a, b) > 0`, then one step reduces `M` by at least `1`.

### Proof

Let `n = bitlen(a) = M(a, b)`. Since `e > 0`, we have `bitlen(b) <= n - 1`.
Also `t = 2^e b` has the same bit-length as `a`, so both `a` and `t` lie in
the interval `[2^(n-1), 2^n)`. Therefore

`r = |a - t| < 2^(n-1)`,

so `bitlen(r) <= n - 1`.

The next state is `(max(b, r), min(b, r))`, and both entries have bit-length
at most `n - 1`. Hence the new top bit-length is at most `n - 1`, so `M`
drops by at least `1`. `qed`

### Lemma 3

If `e(a, b) = 0`, then the next state is `(b, a - b)`, and the following
state has positive exponent gap.

### Proof

If `e = 0`, then `t = b`, so `r = a - b` and the next state is `(b, a - b)`.

Because `a` and `b` have the same bit-length and `a >= b > 0`, we have
`a < 2^n` and `b >= 2^(n-1)` for `n = bitlen(a) = bitlen(b)`. Hence

`0 <= a - b < 2^(n-1) <= b`,

so `bitlen(a - b) < bitlen(b)`.

By Lemma 1 there is no normalization on reduced states, so the next state is
exactly `(b, a - b)`. Therefore the following step starts from unequal
bit-lengths, hence with positive exponent gap. `qed`

### Corollary 4

Every valid two-step continuation reduces `M` by at least `1`.

### Proof

If the first step has positive exponent gap, use Lemma 2.

If the first step has zero exponent gap, use Lemma 3 to see that the second
step starts with positive exponent gap, and then apply Lemma 2 to the second
step. `qed`

This is the rigorous weak bound:

`M(a_0, b_0) - M(a_s, b_s) >= floor(s / 2)`.

In particular, the remainder values for `s = 0, 1, 2, 3, 4` are

- `0`
- `0`
- `1`
- `1`
- `2`

which matches `rho(0), ..., rho(4)` except that the strong bound is better
starting at `s = 5`.

## 3. Reduction of the strong bound to a five-step lemma

### Lemma 5

If every valid five-step block drops `M` by at least `3`, then the full strong
bound follows.

### Proof

Write `s = 5q + r` with `0 <= r < 5`.

Apply the five-step lemma to each of the first `q` disjoint five-step blocks.
That contributes at least `3q` total drop.

For the final remainder block of length `r`, apply Corollary 4:

- `r = 0` gives drop at least `0`
- `r = 1` gives drop at least `0`
- `r = 2` gives drop at least `1`
- `r = 3` gives drop at least `1`
- `r = 4` gives drop at least `2`

So the remainder contributes at least `rho(r)`. Therefore the total drop is at
least

`3q + rho(r) = min_drop_for_steps_strong(s)`.

This is exactly the desired bound. `qed`

So it remains only to prove:

> Every valid five-step block drops the top bit-length by at least `3`.

## 4. Combinatorial reduction of the five-step lemma

Consider any valid five-step block, and write `M_i` for the top bit-length
before step `i`.

By Lemma 2:

- every step with `e > 0` causes an immediate drop of at least `1`.

By Lemma 3:

- if a step has `e = 0`, then the next step must have `e > 0`.

Thus:

- zero-steps cannot be adjacent;
- every five-step block contains at least two positive-gap steps;
- if a five-step block dropped by at most `2`, then it could contain no more
  than two positive-gap steps, because each such step already contributes at
  least `1`.

Hence any hypothetical bad five-step block with total drop at most `2` must
contain exactly two positive-gap steps and exactly three zero-steps. Since the
zero-steps cannot be adjacent, the only possible pattern is

`0, >0, 0, >0, 0`.

So it is enough to prove:

> Every valid five-step block with `e`-pattern `0, >0, 0, >0, 0` drops by at
> least `3`.

## 5. Exact drop in an alternating block

Assume we have a valid five-step block with exponent-gap pattern

`0, d_1, 0, d_2, 0`

where `d_1, d_2 >= 1`.

Let the initial state be `(A, B)` with `A >= B > 0` and

`bitlen(A) = bitlen(B) = n + 1`.

Define successive unreduced residuals:

- `D = A - B`
- `E = |B - 2^(d_1) D|`
- `X = |D - E|`
- `Y = min(D, E)`
- `Z = |Y - 2^(d_2) X|`

Since all states are reduced, by Lemma 1 these are also the actual reduced
states and residuals.

### Lemma 6

In such an alternating block, the total drop in top bit-length is exactly
`d_1 + d_2`.

### Proof

Step 1 has exponent gap `0`, so it maps `(A, B)` to `(B, D)` with

- `bitlen(B) = n + 1`
- `bitlen(D) < bitlen(B)`

Because Step 2 is assumed to have exponent gap `d_1`, we have

`bitlen(D) = bitlen(B) - d_1 = n + 1 - d_1`.

After Step 2 the new state is `(max(D, E), min(D, E))`. Step 3 is assumed to
have exponent gap `0`, so both entries after Step 2 must have the same
bit-length. One of them is `D`, so both must have bit-length `n + 1 - d_1`.
In particular, the top bit-length after Step 2 is exactly `n + 1 - d_1`.

Thus Steps 1 and 2 together decrease the top bit-length by exactly `d_1`.

Now Step 3 starts from an equal-bit-length pair `(max(D, E), min(D, E))`,
which may be written as `(Y + X, Y)` in one order or the other, with
`Y = min(D, E)` and `X = |D - E|`.

Also `Y > X`, because `D` and `E` have the same bit-length, so
`Y >= 2^(m-1)` while `X < 2^(m-1)` for `m = bitlen(D) = bitlen(E)`.
Therefore the Step-3 output is exactly the ordered pair `(Y, X)`.

Since Step 4 has exponent gap `d_2`,
the smaller entry `X` has bit-length exactly `bitlen(Y) - d_2`.

After Step 4 the new state is `(max(X, Z), min(X, Z))`. Step 5 is assumed to
have exponent gap `0`, so both entries after Step 4 must have the same
bit-length. One of them is `X`, so both must have bit-length
`bitlen(Y) - d_2`.

Therefore Steps 3 and 4 decrease the top bit-length by exactly `d_2`, and
Step 5 contributes no further drop at its start.

Hence the total drop across the five-step block is exactly `d_1 + d_2`. `qed`

### Corollary 7

To prove the alternating-case lemma, it is enough to rule out the minimal
obstruction

`0, 1, 0, 1, 0`.

### Proof

If an alternating five-step block dropped by at most `2`, then by Lemma 6 we
would have `d_1 + d_2 <= 2`. Since `d_1, d_2 >= 1`, this forces
`d_1 = d_2 = 1`. `qed`

So it remains to prove that the pattern `0, 1, 0, 1, 0` is impossible.

## 6. Algebraic normal form for the obstruction `0, 1, 0, 1, 0`

Assume for contradiction that a valid five-step block has exponent-gap pattern

`0, 1, 0, 1, 0`.

Let the initial state be `(A, B)` with

- `A >= B > 0`
- `gcd(A, B) = 1`
- `bitlen(A) = bitlen(B) = n + 1`

Define

- `D = A - B`
- `E = |B - 2D|`
- `X = |D - E|`
- `Y = min(D, E)`
- `Z = |Y - 2X|`

### Lemma 8

These quantities satisfy

- `bitlen(D) = n`
- `bitlen(E) = n`
- `bitlen(X) = n - 1`
- `bitlen(Z) = n - 1`

### Proof

Step 1 has exponent gap `0`, so it sends `(A, B)` to `(B, D)`. Since
`bitlen(B) = n + 1` and Step 2 has exponent gap `1`, the smaller entry `D`
must have bit-length `n`.

Step 2 sends `(B, D)` to `(max(D, E), min(D, E))`. Since Step 3 has exponent
gap `0`, both entries after Step 2 have the same bit-length. One of them is
`D`, which has bit-length `n`, so `E` also has bit-length `n`.

Step 3 sends the equal-bit-length pair `(max(D, E), min(D, E))` to
`(Y, X) = (min(D, E), |D - E|)` in some order, with larger entry `Y`.
Since Step 4 has exponent gap `1`, the smaller entry `X` must have
bit-length `n - 1`.

Step 4 sends `(Y, X)` to `(max(X, Z), min(X, Z))`. Since Step 5 has exponent
gap `0`, both entries after Step 4 have the same bit-length. One of them is
`X`, which has bit-length `n - 1`, so `Z` also has bit-length `n - 1`. `qed`

### Lemma 9

Exactly one of the following three algebraic cases holds.

Case I.a:

- `D > E`
- `B < 2D`
- `D = Y + X`
- `B = Y + 2X`
- `A = 2Y + 3X`

Case I.b:

- `D > E`
- `B > 2D`
- `D = Y + X`
- `B = 3Y + 2X`
- `A = 4Y + 3X`

Case II:

- `E > D`
- `Y = D`
- `B = 3Y + X`
- `A = 4Y + X`

### Proof

Since `bitlen(X) = n - 1 > 0`, we have `X > 0`, so `D != E`.

If `D > E`, then `Y = E` and `X = D - E`, hence

`D = Y + X`.

Now either `B < 2D` or `B > 2D`.

The equality `B = 2D` is impossible, because then `E = |B - 2D| = 0`, but
`bitlen(E) = n > 0`.

If `B < 2D`, then `E = 2D - B`, so

`B = 2D - E = 2(Y + X) - Y = Y + 2X`,

and therefore

`A = B + D = (Y + 2X) + (Y + X) = 2Y + 3X`.

This is Case I.a.

If instead `B > 2D`, then `E = B - 2D`, so

`B = E + 2D = Y + 2(Y + X) = 3Y + 2X`,

and therefore

`A = B + D = (3Y + 2X) + (Y + X) = 4Y + 3X`.

This is Case I.b.

If `D > E` does not hold, then since `D != E` we must have `E > D`. In that
case `Y = D`.

Also `E = B - 2D`, not `2D - B`, because if `E = 2D - B`, then `E > D` would
imply `2D - B > D`, hence `D > B`, impossible since `D = A - B < B`.

So `E = B - 2D`, and therefore

`X = E - D = B - 3D`,

hence

`B = 3D + X = 3Y + X`,

and finally

`A = B + D = (3Y + X) + Y = 4Y + X`.

This is Case II.

The three cases are mutually exclusive and exhaustive. `qed`

## 7. Scaled inequalities

From Lemma 8 we have

- `2^(n-1) <= Y < 2^n`
- `2^(n-2) <= X < 2^(n-1)`
- `2^(n-2) <= Z < 2^(n-1)`

Also `n >= 2`, because `X > 0` and `bitlen(X) = n - 1`, while every positive
integer has bit-length at least `1`.

Now scale by `2^(n-2)` and define

- `y = Y / 2^(n-2)`
- `x = X / 2^(n-2)`

Then

- `2 <= y < 4`
- `1 <= x < 2`

and because `Z = |Y - 2X|`,

`1 <= |y - 2x| < 2`.

We now eliminate the three cases one by one.

### Lemma 10

Case II is impossible.

### Proof

In Case II we have `A = 4Y + X`, so after scaling,

`A / 2^(n-2) = 4y + x`.

But `y >= 2` and `x >= 1`, so

`4y + x >= 9`.

Hence

`A >= 9 * 2^(n-2) > 8 * 2^(n-2) = 2^(n+1)`,

contradicting `bitlen(A) = n + 1`, which means `A < 2^(n+1)`. `qed`

### Lemma 11

Case I.b is impossible.

### Proof

In Case I.b we have `B = 3Y + 2X`, so after scaling,

`B / 2^(n-2) = 3y + 2x`.

But `y >= 2` and `x >= 1`, so

`3y + 2x >= 8`.

Hence

`B >= 8 * 2^(n-2) = 2^(n+1)`,

contradicting `bitlen(B) = n + 1`, which means `B < 2^(n+1)`. `qed`

### Lemma 12

Case I.a is impossible.

### Proof

In Case I.a we have `A = 2Y + 3X`, so

`2y + 3x = A / 2^(n-2) < 8`,

because `A < 2^(n+1) = 8 * 2^(n-2)`.

On the other hand, from `1 <= |y - 2x|` there are only two possibilities:

1. `y >= 2x + 1`
2. `y <= 2x - 1`

If `y >= 2x + 1`, then

`2y + 3x >= 2(2x + 1) + 3x = 7x + 2 >= 9`,

since `x >= 1`.

If `y <= 2x - 1`, then `y >= 2` implies

`2x >= y + 1 >= 3`,

so `x >= 3/2`. Therefore

`2y + 3x >= 2 * 2 + 3 * (3/2) = 4 + 9/2 > 8`.

Both alternatives contradict `2y + 3x < 8`. So Case I.a is impossible. `qed`

### Corollary 13

The pattern `0, 1, 0, 1, 0` is impossible.

### Proof

By Lemma 9, one of Cases I.a, I.b, II must hold. By Lemmas 10, 11, and 12,
each of those cases is impossible. Contradiction. `qed`

## 8. The five-step lemma

### Lemma 14

Every valid five-step block drops the top bit-length by at least `3`.

### Proof

Assume for contradiction that some valid five-step block drops by at most `2`.

By the combinatorial reduction in Section 4, its exponent-gap pattern must be

`0, >0, 0, >0, 0`.

By Corollary 7, the only way such a block can drop by at most `2` is if the
pattern is the minimal obstruction

`0, 1, 0, 1, 0`.

But Corollary 13 shows that this pattern is impossible. Contradiction. `qed`

## 9. Main theorem

### Theorem 15

For every valid forward trajectory through reduced states of length `s`,

`M(a_0, b_0) - M(a_s, b_s) >= min_drop_for_steps_strong(s)`.

### Proof

By Lemma 14, every five-step block drops `M` by at least `3`. By Lemma 5,
this implies the full strong bound

`min_drop_for_steps_strong(s) = 3 * floor(s / 5) + rho(s mod 5)`.

Therefore every valid `s`-step continuation drops the top bit-length by at
least `min_drop_for_steps_strong(s)`. `qed`

## 10. Admissibility for reverse-search pruning

Let the reverse search run inside the `k`-bit box, and let the current reduced
state be `(a, b)` with `a >= b > 0`. Define

`delta = k - bitlen(a)`.

Suppose, for contradiction, that the current reverse node had an ancestor at
reverse distance `s` that still lay inside the `k`-bit box. Equivalently,
there would be a forward trajectory

`(a_0, b_0) -> (a_1, b_1) -> ... -> (a_s, b_s) = (a, b)`

through reduced states, where the ancestor `(a_0, b_0)` lies inside the
`k`-bit box.

Because the ancestor lies inside the `k`-bit box,

`M(a_0, b_0) <= k`.

Because `a >= b`, we also have

`M(a_s, b_s) = M(a, b) = bitlen(a)`.

Therefore the total drop along this forward trajectory satisfies

`M(a_0, b_0) - M(a_s, b_s) <= k - bitlen(a) = delta`.

But by Theorem 15, every such continuation drops by at least
`min_drop_for_steps_strong(s)`.

Therefore, whenever

`min_drop_for_steps_strong(s) > delta`,

no such ancestor can exist. So the reverse search may safely prune the current
node at reverse depth `s` in that case.

This is exactly the admissibility statement needed by the search.

## Summary

The proof rests on four facts:

1. On reduced states, normalization is always trivial because the gcd stays
   equal to `1`.
2. Every two steps drop the top bit-length by at least `1`.
3. Every five steps drop the top bit-length by at least `3`.
4. The only hypothetical five-step obstruction is the alternating pattern
   `0, 1, 0, 1, 0`, and that pattern is algebraically impossible.

Hence the strong pruning bound

`min_drop_for_steps_strong(s) = 3 * floor(s / 5) + rho(s mod 5)`

is admissible on the reduced reverse-search graph.
