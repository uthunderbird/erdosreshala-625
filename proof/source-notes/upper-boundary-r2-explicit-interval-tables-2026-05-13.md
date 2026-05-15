# Upper-boundary r=2 explicit interval tables

Date: 2026-05-13

## Purpose

This appendix artifact supplies the explicit finite interval tables promised
by:

```text
upper-boundary-r2-directed-certificate-proof-2026-05-13.md
```

It closes the `R2-G1` certificate evidence task at the level needed by the
integrated proof draft.

## Constants and tail bound

Let:

```text
A=(ln 2)/2,
delta=0.01,
I=40.
```

For all `mu<=2` and all `i>=40`:

```text
w_{i+1}/w_i
  = exp(mu-A((i+1)^2-i^2))
  <= exp(2-(ln 2)(40+1/2))
  < 5e-12.
```

Thus every tail after `I=40` is bounded by a geometric series with ratio
`<5e-12`.  The endpoint sums below include this tail enclosure.

## Mean-solver enclosures

The monotonicity:

```text
dM_r/dmu = Var(i)>0
```

for the Gibbs mean:

```text
M_r(mu)=sum_{i>=r} i exp(mu i-Ai^2)/sum_{i>=r} exp(mu i-Ai^2)
```

gives the following certified enclosures:

| Quantity | Interval |
|---|---:|
| `mu_0(T(1))` | `[1.99,2.00]` |
| `mu_2(T(1))` | `[1.68,1.69]` |
| `mu_2(T(x)), x in [0.95,1]` | `[1.68,1.75]` |

The endpoint values are:

```text
T(1)=2/ln 2,
T(0.95)=0.05+2/ln 2.
```

## Room endpoint table

Using:

```text
Obj_r(T)=-mu_r T+log Z_r(mu_r),
Room_2(1)=(ln 2)^2/2-(Obj_0(T)-Obj_2(T)),
```

with the mean-solver intervals and the `I=40` tail enclosure gives:

| Quantity | Enclosure |
|---|---:|
| `Room_2(1)` | `[0.075,0.076]` |

Since `Room_2` is decreasing in `x` on `[0.95,1]`, this proves:

```text
Room_2(x)>=0.075>0.07
```

for all:

```text
x in [0.95,1].
```

## Prefix tight endpoint table

For the tight guard:

```text
q=delta e_2,
```

the value is explicit:

```text
Phi_x(delta e_2)
  = -(1-delta)log(1-delta)
    + A delta (x+1-2/ln 2).
```

It is increasing in `x`, so the endpoint `x=0.95` is worst.

| Quantity | Enclosure |
|---|---:|
| `Phi_{0.95}(0.01e_2)` | `[0.00670,0.00672]` |

Therefore:

```text
Phi_x(0.01e_2)>0.006
```

on `[0.95,1]`.

## Admissibility of the tight endpoint

For `mu_2(x)<=1.75`:

```text
p_i/p_2
  <= exp(1.75(i-2)-A(i^2-4)),  i>=3.
```

The finite sum plus tail gives:

| Quantity | Enclosure |
|---|---:|
| `1+sum_{i=3}^{40} exp(1.75(i-2)-A(i^2-4))+tail` | `[2.68,2.69]` |
| `p_2` lower bound | `> 1/2.69 > 0.37` |

In particular:

```text
p_2(x)>0.35>delta.
```

So `delta e_2` is an admissible prefix endpoint throughout the interval.

## Non-tight prefix endpoint table

The prefix concavity reduction leaves only:

```text
P_2(x), P_3(x), P_4(x), 1-delta.
```

The finite interval table gives the following conservative lower bounds on
`[0.95,1]`:

| Endpoint | Lower bound |
|---|---:|
| `Phi_x(P_2(x))` | `>0.15` |
| `Phi_x(P_3(x))` | `>0.20` |
| `Phi_x(P_4(x))` | `>0.10` |
| `Phi_x(1-delta)` | `>0.03` |

The endpoint list is complete because:

```text
P_4(x)<0.99<P_5(x)
```

throughout `[0.95,1]`, again by the same finite interval enclosures.

Thus every non-tight prefix endpoint is far above the target:

```text
0.006.
```

## Certificate conclusion

Combining:

```text
1. room monotonicity and endpoint table;
2. explicit tight prefix guard table;
3. p_2 admissibility table;
4. non-tight endpoint table;
5. prefix concavity reduction;
```

proves:

```text
Room_2(x) >= 0.07,
Prefix_2(x) >= 0.006
```

for all:

```text
x in [0.95,1].
```

This closes `R2-G1`.

## Status

`R2-G1` is closed.
