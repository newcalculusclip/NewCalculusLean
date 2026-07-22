import Mathlib

/-!
# The New Calculus geometric identity, formalized

Machine-checked formalization of the core algebraic content of John Gabriel's
New Calculus derivative for polynomial functions, in the lineage of
Descartes' double-point method (1637) and R. M. Range, "Where Are Limits
Needed in Calculus?" (Amer. Math. Monthly 118, 2011).

Main results:

* `gabriel_identity`   : for every polynomial `f` and point `x` there is a
  polynomial `Q` with `Q(0) = 0` and
  `f(x+h) - f(x) = h * (f.derivative(x) + Q(h))` for ALL `h`.
  The proof is pure ring algebra: no limits, no ε-δ, no topology.
  `Q(0) = 0` is polynomial evaluation (substitution), not a limit.

* `gabriel_slope_unique` : the slope `s` in such an identity is unique
  (over an infinite integral domain). Hence the New Calculus derivative
  is well-defined with no limit concept.

* `parallel_secant_sq`, `secant_cubed` : the exact parallel-secant slope
  identities for x² and x³ (finite, nonzero gaps m, n).

* `nc_agrees_with_mainstream` : the algebraically-defined slope coincides
  with mathlib's analytic derivative `deriv` for every real polynomial —
  the two frameworks provably compute the same numbers.
-/
open Polynomial

namespace NewCalculus

variable {R : Type*} [CommRing R]

/-- **Gabriel's identity** (the "geometric theorem"): for every polynomial `f`
and point `x`, there exists a polynomial `Q` (the tangent/parallel-secant
slope gap) such that `Q(0) = 0` and

  `f(x+h) - f(x) = h * (f'(x) + Q(h))`  for all `h`.

Everything is finite ring algebra; setting `h = 0` in `Q` is substitution. -/
theorem gabriel_identity (f : R[X]) (x : R) :
    ∃ Q : R[X], Q.eval 0 = 0 ∧
      ∀ h : R, f.eval (x + h) - f.eval x
        = h * (f.derivative.eval x + Q.eval h) := by
  refine ⟨(taylor x f).divX - C (f.derivative.eval x), ?_, ?_⟩
  · -- Q(0) = (divX (taylor x f))(0) - f'(x) = coeff 1 (taylor x f) - f'(x) = 0
    have h1 : ((taylor x f).divX).eval 0 = (taylor x f).coeff 1 := by
      rw [← coeff_zero_eq_eval_zero, coeff_divX]
    simp [h1, taylor_coeff_one]
  · intro h
    have hgeval : (taylor x f).eval h = f.eval (x + h) := by
      rw [taylor_apply, eval_comp]; simp [add_comm]
    have hc0 : (taylor x f).coeff 0 = f.eval x := by
      simp
    have hsplit := X_mul_divX_add (taylor x f)
    have : (taylor x f).eval h
        = h * ((taylor x f).divX.eval h) + f.eval x := by
      conv_lhs => rw [← hsplit]
      simp [eval_add, eval_mul, hc0]
    rw [← hgeval, this]
    simp [eval_sub, eval_C]

/-- **Uniqueness of the slope**: over an infinite integral domain, if
`f(x+h) - f(x) = h * (s + Q(h))` with `Q(0) = 0`, then `s` must be
`f'(x)`. The New Calculus derivative is well-defined — no limits needed. -/
theorem gabriel_slope_unique {R : Type*} [CommRing R] [IsDomain R] [Infinite R]
    (f : R[X]) (x s : R) (Q : R[X]) (hQ0 : Q.eval 0 = 0)
    (hid : ∀ h : R, f.eval (x + h) - f.eval x = h * (s + Q.eval h)) :
    s = f.derivative.eval x := by
  obtain ⟨Q', hQ'0, hid'⟩ := gabriel_identity f x
  have key : ∀ h : R, h * (s + Q.eval h)
      = h * (f.derivative.eval x + Q'.eval h) := by
    intro h; rw [← hid h, hid' h]
  have hpoly : (X * (C s + Q) : R[X])
      = X * (C (f.derivative.eval x) + Q') := by
    apply Polynomial.funext
    intro r
    simpa [eval_mul, eval_add, eval_C] using key r
  have hcancel : (C s + Q : R[X]) = C (f.derivative.eval x) + Q' :=
    mul_left_cancel₀ X_ne_zero hpoly
  have := congrArg (Polynomial.eval 0) hcancel
  simpa [hQ0, hQ'0] using this

/-- **Parallel secant for x²**: the secant through `(x-m, (x-m)²)` and
`(x+m, (x+m)²)` satisfies rise = run · (2x) for EVERY gap `m` —
the tangent slope, exactly, with finite nonzero gaps. -/
theorem parallel_secant_sq (x m : R) :
    (x + m)^2 - (x - m)^2 = (2*m) * (2*x) := by ring

/-- **Secant slope for x³** in auxiliary-equation form: the secant through
`(x-m, (x-m)³)` and `(x+n, (x+n)³)` satisfies
rise = run · (3x² + aux) where `aux = 3x(n-m) + (n² - mn + m²)`.
The New Calculus auxiliary equation is `aux = 0`; on its solutions the
secant slope is exactly the tangent slope `3x²`. -/
theorem secant_cubed (x m n : R) :
    (x + n)^3 - (x - m)^3
      = (m + n) * (3*x^2 + (3*x*(n - m) + (n^2 - m*n + m^2))) := by ring

/-- The audited worked example: at `x = 1` with gaps `m = 1`, `n = √3 - 1`,
the auxiliary equation holds and the secant through `(0,0)` and `(√3, √3³)`
has rise = run · 3, i.e. slope exactly `3 = (x³)'` at `x = 1`. -/
theorem aux_example_cubed :
    (Real.sqrt 3)^3 - 0^3 = (Real.sqrt 3 - 0) * 3 := by
  have h : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  calc (Real.sqrt 3)^3 - 0^3 = (Real.sqrt 3)^2 * Real.sqrt 3 := by ring
    _ = 3 * Real.sqrt 3 := by rw [h]
    _ = (Real.sqrt 3 - 0) * 3 := by ring

/-- **Agreement theorem**: for every real polynomial, the algebraic
New Calculus slope `f.derivative.eval x` (defined with no limits, via
`gabriel_identity` + `gabriel_slope_unique`) equals mathlib's analytic
derivative `deriv`. The two frameworks compute the same numbers. -/
theorem nc_agrees_with_mainstream (f : ℝ[X]) (x : ℝ) :
    deriv (fun t => f.eval t) x = f.derivative.eval x :=
  f.deriv

end NewCalculus
