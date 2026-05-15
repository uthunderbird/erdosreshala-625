# Upper-boundary alpha-anchor omitted-top scan result

Date: 2026-05-13

## Command

```text
python3 work/scripts/upper_boundary_alpha_anchor_omitted_top_scan.py \
  --x-left 0.95 \
  --x-right 0.999999 \
  --x-grid 80 \
  --imax 220 \
  --r-max 6
```

This is an exploratory floating-point scan, not proof evidence.

## Output

```text
r,min_room,x_room,min_prefix,x_prefix,p_r_min,p_r_max
1,0.219981127046,0.999999,0.00324228160263,0.95,0.100741626531,0.108598297718
2,0.0751819864119,0.999999,0.00670801750543,0.95,0.373937537237,0.395802646424
3,-1.09385638128,0.999999,0.0101737534082,0.95,1,1
4,-3.51987151324,0.999999,0.013639489311,0.95,1,1
5,-6.63903382576,0.999999,0.0171052252138,0.95,1,1
6,-10.4513433188,0.999999,0.0205709611166,0.95,1,1
```

## Interpretation

The alpha-anchor omitted-top route is numerically viable near `x=1` for:

```text
r=1,
r=2.
```

Both have:

```text
min_room > 0,
min_prefix > 0
```

on the tested interval `[0.95,0.999999]`.

The `r=1` profile gives the largest room:

```text
room >= about 0.21998,
prefix >= about 0.00324.
```

The `r=2` profile gives smaller but still positive room:

```text
room >= about 0.07518,
prefix >= about 0.00670.
```

The `r>=3` rows are not viable for the upper-boundary alpha-anchor route.
As `x -> 1`, the alpha-anchor mean deficit is:

```text
T_alpha(x)=1+2/ln2-x -> 2/ln2 ~= 2.885...
```

so support constrained to `i>=3` is already incompatible with the target
mean in the limit.  The script reports degenerate mass at the first
available index and negative room.

## Consequence

The upper-boundary proof should focus on `r=1` first:

```text
alpha-anchor, omit alpha-sized cocolour classes,
largest occupied size alpha-1.
```

This profile removes the problematic `alpha`-layer scrambled penalty while
retaining large first-moment room.

If source adaptation for `r=1` has hidden issues, `r=2` is a fallback with
stronger prefix margin but less first-moment room.

## Next proof-grade target

Develop:

```text
upper-boundary-alpha-anchor-r1-certificate-theorem
```

Current theorem target:

```text
upper-boundary-alpha-anchor-r1-certificate-theorem-2026-05-13.md
```

with:

```text
1. proof-grade interval certificate for room/prefix on x in [x1,1);
2. exact finite large-anchor transfer for the alpha-anchor r=1 profile;
3. first-moment shift theorem below boldk_alpha by c n/log^3 n;
4. C3/C5 source adaptation with active scrambled scale mu_{alpha-1};
5. ordinary lower-bound transfer from chi_alpha to chi using alpha+1 scarcity.
```

## Status

Exploratory route selection: positive.

This does not close the proof, but it converts the upper-boundary P0 from an
abstract open theorem into a concrete `r=1` alpha-anchor certificate and
source-adaptation task.
