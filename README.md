# NewCalculusLean

Machine-checked (Lean 4 + mathlib) formalization of the algebraic core of the
New Calculus derivative for polynomials, in the lineage Descartes (1637) →
Hudde → R. M. Range (Amer. Math. Monthly 118, 2011).

## Theorems (NewCalculusLean/Basic.lean)

| Theorem | Statement |
|---|---|
| `gabriel_identity` | ∀ polynomial f, point x: ∃ Q, Q(0)=0 ∧ f(x+h)−f(x) = h(f′(x)+Q(h)) ∀h — pure ring algebra, no limits |
| `gabriel_slope_unique` | the slope in such an identity is unique (infinite integral domain) — the NC derivative is well-defined without ε-δ |
| `parallel_secant_sq` | (x+m)² − (x−m)² = (2m)(2x): every symmetric secant of x² has exactly the tangent slope |
| `secant_cubed` | x³ secant slope in auxiliary-equation form |
| `aux_example_cubed` | worked instance: x=1, gaps m=1, n=√3−1 → slope exactly 3 |
| `nc_agrees_with_mainstream` | the algebraic NC slope equals mathlib's analytic `deriv` for every real polynomial |

## Scope (honest)

Covers polynomial (extensible: rational/algebraic) functions — the class where
the limit-free program is valid. It does NOT cover transcendental functions
(e^x, sin): producing the *magnitude* e by finite algebra is impossible
(Hermite 1873); the corpus e-derivation is valid only as formal power series.


## Self-audit (NewCalculusLean/Consistency.lean)

This project audits claims on both sides. Machine-checked:

| Theorem | Verdict |
|---|---|
| `field_axioms_consistent` | All field axioms hold in a 2-element model, checked by finite enumeration (`decide`). The axioms are NOT internally inconsistent — the corpus "pi ≠ pi × 1" argument is an equivocation between measurement semantics and the axioms' implicit definition of ×. |
| `zero_mul_from_axioms` | 0·x = 0 is derivable from distributivity + cancellation in two steps — a theorem, not a decree. |
| `gabriel_identity_rat` | **The finitist core**: the New Calculus polynomial derivative over ℚ — provably independent of the real line, completed infinity, and any set-theoretic superstructure. |

The honest position this repo defends: the New Calculus polynomial calculus is
rigorous, limit-free, and finitistically grounded (verified); the field axioms
are consistent (verified); producing the magnitude e by finite algebra is
impossible (Hermite 1873). Rigor is applied symmetrically, whichever way it cuts.

## Build

    lake build   # requires elan; mathlib cache via lake exe cache get
