import Mathlib.Tactic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Taylor
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Basic
import Kloosterman.lemma_char_v4

-- import def2_v2_kloosterman

#check RatFunc
-- import Desktop.UCL.mary_lister.kloosterman.def2_v2_kloosterman.lean

-- wrote Kloosterman stuff

-- inductive
-- valuation ring
-- mathlib4/mathlib/numbertheory/lucasprimality.lean

/- # Caution
When you later decide to change the definiton of ratfunc we have, you need to make sure that it will be mapped to ZMod q 
otherwise we cannot put it in the characters we have defined previously

-/

/- source
Taylor series
1. Mathlib/Data/Polynomial/Taylor.lean
2. Mathlib/Analysis/Calculus/Taylor.lean
3. Mathlib/FieldTheory/Laurent.lean
4. Mathlib/Data/Polynomial/HasseDeriv.lean
5. FieldTheory/RatFunc.lean has the section Laurent series
-/

/- # Brainstorm
I think I need to use the theorem `taylor_mean_remainder_lagrange`

-/

/- # Overall proof
1. Obtain the taylor expansion with remainder for the denominator and numerator of a rational function 
2. Obtain the expressions for the denominator and numerator mod p^(2*α)
3. Obtain the expression for the rational function mod p^(2*α) by dividing the numerator and denominator
4. Write the expression in terms of the function f and its derivative

-/

/- # Potential troubles
1. Obtain the taylor expansion with remainder for the denominator and numerator of a rational function 
2. Obtain the expressions for the denominator and numerator mod p^(2*α):
   Showing the coefficients can be expressed as integers mod p^(2*α)
3. Obtain the expression for the rational function mod p^(2*α) by dividing the numerator and denominator:
   - Not sure how the division of polynomials work
   - Especially mod p^(2*α)
4. Write the expression in terms of the function f and its derivative:
   Need to look up how the derivative of the rational function is defined
5. Summing over the variables
   Q. Is it possible to sum over the variable X for the polynomial.X?
   A. Maybe p.sum f will do its job
   Also is it possible to make the expression X = y + z*p^α 
   I think polynomial.eval will do its job : Do something like ∑(i : ZMod q), f.denom.eval i
-/

/- # List of theorems we need
1. Proof that p doesn't divide f₀(y) by the assumption that p doesn't divide f₀(x)
2. 

-/

/- # TODO
1. IMPO : Need to make the statements for the whole proof before starting anything; need to make sure every theorem comes together seamlessly
2. Think about whether f : RatFunc ℚ is a good idea
3. Get rid of repetitive variables
4. Make sure no theorem will take in too many variables when calling for it
5. Deal with the theorem `poly_taylor_eval`
6. Think whether I have assigned the best type (i.e., ℤ, (ZMod q), (ZMod q)ˣ or ℕ in some cases) for each variable and the range of functions
7. 
-/

/- # Ask Kevin
1. How to import other files
2. Whether correct: my approach of having the polynomials as an input rather than a rational function
3. 

-/

/- # How fractions work
Fractions are reduced by clearing common denominators before evaluating:
`eval id 1 ((X^2 - 1) / (X - 1)) = eval id 1 (X + 1) = 2`, not `0 / 0 = 0`.
-/

open Complex Polynomial Int BigOperators Set

-- need to build up the definition
/- 
So I think that this condition about f0 and f1 and f0(x) being coprime to q boils down to the following. 
You have a rational function f : RatFunc \Q and the condition you want is that firstly f.denom x isn't zero 
and secondly that the rational number f(x) is "coprime to q" in the sense that the denominator is coprime to q

Then you can "reduce f(x) mod q" by inverting the denominator mod q and multiplying by the numerator
-/

-- (haq : ((a : ZMod q).val).gcd q = 1)

noncomputable section

variable {p : ℕ} {α : ℕ} (z : ZMod (p^α : ℕ)) (χ : MulChar (ZMod (p^(2*α) : ℕ)) ℂ) (ψ : AddChar (ZMod (p^(2*α) : ℕ)) ℂ) (q : ℕ)
-- (q : ℕ) (x : ZMod q) (y : ℤ) (z : ZMod q)

-- variable {C : Type v} [CommRing C]

variable (f₁ f₀ g₁ g₀ : Polynomial ℤ)
-- the denom is not equal to zero by the theorem `Ratfunc.denom_ne_zero`
-- numerator and denominator are coprime by the theorem `Ratfunc.is_coprime_num_denom`

-- f.denom.eval x ≠ 0 
-- RatFunc (ZMod q)ˣ doesn't work


def CharSum (q : ℕ) : ℂ :=
  ∑ x : (ZMod q)ˣ, χ x * ψ x

/- 
we need `.eval` because we're trying to evaluate the function f at specific value x
-/

/- # Old def
def is_good (f : RatFunc ℚ) (x : ℚ) (q : ℕ) : Prop := 
  f.denom.eval x ≠ 0 ∧ (f.eval (RingHom.id ℚ) (x)).den.gcd q = 1

def RatFunc.eval_prime (f : RatFunc ℚ) (x : ℚ) (q : ℕ) (h : is_good f x q) : ZMod q := 
  let r := f.eval (RingHom.id ℚ) (x) -- apparently, ignores the let statement according to kevin
  r.num*(r.den : ZMod q)⁻¹
-/

def rationalFunc (p₁ p₀ : Polynomial ℤ) (x₀ : ℤ) (q : ℕ) : ZMod q :=
  let r := p₀.eval x₀
  (p₁.eval x₀) * (r : ZMod q)⁻¹

/- 
# ASK KEVIN
whether there's more compact way to define the inverse of rationalFunc mod ZMod q
-/ 
def rationalFunc_inverse (p₀ : Polynomial ℤ) (x₀ : ℤ) (q : ℕ) : ZMod q :=
  let r := p₀.eval x₀
  (r : ZMod q)⁻¹

/- derivative of a rational function f₁/f₀ at x₀ under mod p^(2*α) 
-/
def rationalFunc_deriv (p₁ p₀ : Polynomial ℤ) (x₀ : ℤ) (q : ℕ) : ℤ :=
  (((Polynomial.derivative (R := ℤ)) p₁).eval x₀ * (rationalFunc_inverse (p₀) (x₀) (q)) 
  - ((rationalFunc_inverse (p₀) (x₀) (q))^2 : ZMod q) * ((Polynomial.derivative (R := ℤ)) p₀).eval x₀ * p₁.eval x₀)

/-
def RatFunc.eval_prime (f : RatFunc ℤ) (x : ℚ) (q : ℕ) (h : is_good f x q) : ZMod q := 
  let f₁ := f.num 
  let f₀ := f.denom
  let r := f.eval (RingHom.id ℚ) (x) -- apparently, ignores the let statement according to kevin
  r.num*(r.den : ZMod q)⁻¹
-/ 

/- 
theorem Int_to_Q (f : RatFunc ℚ) (q : ℤ) (x : ℤ): 
    ∃(r : ℤ) (f₁ f₀: Polynomial ℤ), f₁.eval x = r * (f.num.eval x) ∧ f₀ = r * f.denom := by
-/

/- 
theorem `taylor_mean_remainder_lagrange` {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ < x)
    (hf : ContDiffOn ℝ n f (Icc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc x₀ x)) (Ioo x₀ x)) :
    ∃ (x' : ℝ) (_ : x' ∈ Ioo x₀ x), f x - taylorWithinEval f n (Icc x₀ x) x₀ x =
      iteratedDerivWithin (n + 1) f (Icc x₀ x) x' * (x - x₀) ^ (n + 1) / (n + 1)! := by

In our case, x₀ = y and x = x

Or maybe power_series
-/

/-
might have to invert the polynomial and then coerce to ZMod q because of taylor series
Never mind. I think Laurent series is the only way. 
-/


/- 
theorem taylor_series (y z : ZMod (p^α : ℕ)) (h : x = y + z*p^α) 
    RatFunc.eval_prime (f) := by
  sorry
-/

/-
theorem RatFunc_well_defined :
    RatFunc.eval_prime (f) = (f.eval (RingHom.id ℚ) (x)).num*((f.eval (RingHom.id ℚ) (x)).den : ZMod q)⁻¹ := by 
  sorry
-/

/- 
 ratfunc.of_fraction_ring_div 
-/

/-
ratfunc.of_fraction_ring_inv
-/

/- might be a better proof
ratfunc as field of fractions of polynomial

`theorem ratfunc.is_coprime_num_denom`
-/



/- might be a good idea for taylor series
`theorem ratfunc.map_denom_ne_zero`

taylor's formula
`theorem sum_taylor_eq`

the denominator of a rational function is zero
`theorem ratfunc.denom_ne_zero`

Because of how `def RatFunc.eval_prime` is defined, we might be able to use the taylor series for polynomials here
-/

/- might be a better def
`def ratfunc.mk`
`ratfunc.mk (p q : K[X])` is `p / q` as a rational function.
-/


/- look at the definition 
`theorem ratfunc.mk_eq_mk`
-/

/- # Note to myself
It is better to keep the original definition of the rational function we'll use 
as a part of RatFunc

-- Mathlib/Data/Polynomial/Taylor.lean

-/



/- 
theorem `taylor_mean_remainder_lagrange` {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ < x)
    (hf : ContDiffOn ℝ n f (Icc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc x₀ x)) (Ioo x₀ x)) :
    ∃ (x' : ℝ) (_ : x' ∈ Ioo x₀ x), f x - taylorWithinEval f n (Icc x₀ x) x₀ x =
      iteratedDerivWithin (n + 1) f (Icc x₀ x) x' * (x - x₀) ^ (n + 1) / (n + 1)! := by

In our case, x₀ = y and x = x
-/


/- 
theorem sum_taylor_eq {R} [CommRing R] (f : R[X]) (r : R) :
    ((taylor r f).sum fun i a => C a * (X - C r) ^ i) = f := by
-/


theorem IDontThinkIWillEverNeedThis : RatFunc.mk (f₁) (f₀) = 1 := by
  sorry

theorem poly_taylor (p₀ : Polynomial ℤ) (y : ℤ) : 
    p₀ = ((taylor y p₀).sum fun i a => C a * (X - C y) ^ i) := by
  -- have H := taylor_coeff_one (y) (p₀)
  exact Eq.symm (sum_taylor_eq p₀ y)

-- consider whether to have z : ℤ instead of (ZMod q)ˣ
-- is this statement even true? 
-- polynomial.eval_geom_sum
-- eval_finset_sum
theorem poly_taylor_eval (p₀ : Polynomial ℤ) (x y : ℤ) {h : x = y + z * (p^α : ℕ)} :
    p₀.eval x = ((taylor y p₀).sum fun i a => a * ((z : ℤ) * (p^α : ℕ)) ^ i) := by
  nth_rw 1 [poly_taylor p₀ y] -- rewrites only lhs
  
  simp only [eval_finset_sum]
  -- polynomial.eval_X

  sorry

/- Proves that 
p₁ (x) ≡ p₁ (y) + p₁' (y) *z*p^α [ZMOD (p^(2*α))]

p₁.eval x ≡ p₁.eval y + (p₁.derivative.eval y) * z * (p^α) [ZMOD (p^(2*α))]
-/

-- Int.instSemiringInt

theorem poly_taylor_eval_ZMod (p₀ : Polynomial ℤ) (x y : ℤ) {h : x = y + z * (p^α : ℕ)} :
    p₀.eval x ≡ p₀.eval y + ((Polynomial.derivative (R := ℤ)) p₀).eval y * z * (p^α : ℕ) [ZMOD (p^(2*α))] := by
  sorry

-- similarly for denom
-- theorem denom_taylor 

/-
-- be extra careful with how you state this theorem
theorem RatFunc_eq_num_denom_ZMod (x y : ℤ) (h : x = y + z * (p^α : ℕ)) (H : r = p₂.eval x):
    1 ≡ p₁.eval x * ((p₂.eval x) : ZMod (p^α))⁻¹ [ZMOD (p^(2*α))] := by
  field_simp
  sorry
-/

theorem rationalFunc_well_defined_ZMod (x y : ℤ) {h : x = y + z * (p^α : ℕ)} :
    rationalFunc (p₁) (p₀) (x) (p^(2*α)) ≡ 
    (p₁.eval y + ((Polynomial.derivative (R := ℤ)) p₁).eval y * z * (p^α : ℕ)) 
    * ((p₀.eval y + ((Polynomial.derivative (R := ℤ)) p₀).eval y * z * (p^α : ℕ)) : ZMod (p^(2*α)))⁻¹ [ZMOD (p^(2*α))] := by
  sorry

-- fix
lemma rationalFunc_eq_ZMod (x y : ℤ) {h : x = y + z * (p^α : ℕ)} :
    rationalFunc (p₁) (p₀) (x) (p^(2*α)) ≡ rationalFunc (p₁) (p₀) (y) (p^(2*α)) 
    + (rationalFunc_deriv (p₁) (p₀) (y) (p^(2*α))) * z * (p^α : ℕ) [ZMOD (p^(2*α))] := by
  sorry

-- fix
lemma MulChar_in_y_and_z (x y : ℤ) {h : x = y + z * (p^α : ℕ)} :
    χ (rationalFunc (f₁) (f₀) (x) (p^(2*α))) = χ (rationalFunc (f₁) (f₀) (y) (p^(2*α))) 
    * χ (1 + (rationalFunc_deriv (f₁) (f₀) (y) (p^(2*α))) * (rationalFunc (f₁) (f₀) (x) (p^(2*α)) : ZMod (p^(2*α)))⁻¹ * z * (p^α : ℕ)) := by
  sorry

/- deleted the following:
(p : ℕ) (hp : Prime p) (α : ℕ) (z : ZMod (p^α : ℕ)) (χ : MulChar (ZMod (p^(2*α) : ℕ)) ℂ)
-/ 
theorem MulChar_eq_exp (x y : ℤ) :
    ∃(b : ℕ), b < p^α ∧ χ' (χ) ((rationalFunc_deriv (f₁) (f₀) (y) (p^(2*α))) * (rationalFunc (f₁) (f₀) (x) (p^(2*α)) : ZMod (p^(2*α)))⁻¹ * z) 
    = eZMod (p^α : ℕ) (b * (rationalFunc_deriv (f₁) (f₀) (y) (p^(2*α))) * (rationalFunc (f₁) (f₀) (x) (p^(2*α)) : ZMod (p^(2*α)))⁻¹ * z) := by
  sorry

/- the natural number b whose existence is guaranteed by MulChar_eq_exp -/
def MulChar_eq_exp_b (x y : ℤ) : ℕ := (MulChar_eq_exp z χ f₁ f₀ x y).choose

theorem MulChar_eq_exp_b_spec (x y : ℤ) :
    (MulChar_eq_exp_b z χ f₁ f₀ x y) < p ^ α ∧
    χ' (χ) ((rationalFunc_deriv (f₁) (f₀) (y) (p^(2*α))) * (rationalFunc (f₁) (f₀) (x) (p^(2*α)) : ZMod (p^(2*α)))⁻¹ * z) 
    = eZMod (p^α : ℕ) ((MulChar_eq_exp_b z χ f₁ f₀ x y) * (rationalFunc_deriv (f₁) (f₀) (y) (p^(2*α))) * (rationalFunc (f₁) (f₀) (x) (p^(2*α)) : ZMod (p^(2*α)))⁻¹ * z) := 
    (MulChar_eq_exp z χ f₁ f₀ x y).choose_spec

lemma AddChar_in_y_and_z (x y : ℤ) {h : x = y + z * (p^α : ℕ)} :
    ψ (rationalFunc (g₁) (g₀) (x) (p^(2*α))) = ψ (rationalFunc (g₁) (g₀) (y) (p^(2*α))) * ψ ((rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z * (p^α : ℕ)) := by
  sorry

theorem AddChar_eq_exp (y : ℤ) (h : x = y + z * (p^α : ℕ)) :
    ∃(a : ℕ), a < p^α ∧ ψ ((rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z * (p^α : ℕ)) = eZMod (p^α : ℕ) (a * (rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z) := by
  sorry

/- the natural number a whose existence is guaranteed by AddChar_eq_exp -/
def AddChar_eq_exp_a (y : ℤ) (h : x = y + z * (p^α : ℕ)) : ℕ := (AddChar_eq_exp z ψ g₁ g₀ y h).choose

theorem AddChar_eq_exp_a_spec (y : ℤ) (h : x = y + z * (p^α : ℕ)) :
    (AddChar_eq_exp_a z ψ g₁ g₀ y h) < p ^ α ∧
    ψ ((rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z * (p^α : ℕ)) =
    eZMod (p^α : ℕ) ((AddChar_eq_exp_a z ψ g₁ g₀ y h) * (rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z) :=
  (AddChar_eq_exp z ψ g₁ g₀ y h).choose_spec

-- delete this later
instance (q : ℕ) [NeZero q] : Fintype (ZMod q) := by
  -- exact False.elim is_good
  infer_instance

-- needs rewriting
-- a and b are from the characters ψ χ -- [MulChar_eq_exp] [AddChar_eq_exp]
-- should hFunc : ℤ or ZMod q
-- remember that we have the use the orthogonality property of char by setting hFunc ≡ 0 [ZMOD q]
def hFunc (x y x₀ : ℤ) (q : ℕ) (h : x = y + z * (p^α : ℕ)) : ℤ :=
  -- let ⟨b, hl, hr⟩ := MulChar_eq_exp (z) (χ) (f₁) (f₀) (x) (y) 
  (AddChar_eq_exp_a z ψ g₁ g₀ y h) * rationalFunc_deriv (g₁) (g₀) (x₀) (q) + (MulChar_eq_exp_b z χ f₁ f₀ x y) * rationalFunc_deriv (f₁) (f₀) (x₀) (q) * (rationalFunc (f₁) (f₀) (x₀) (q) : ZMod q)⁻¹

/- set of all solutions to hFunc-/
-- x₀ : ℤ or ZMod p^α or (ZMod (p^α : ℕ))ˣ 
-- need to make it reply on the variables `a` and `b` from MulChar_eq_exp and AddChar_eq_exp
def sol_hFunc (x y x₀ : ℤ) (q : ℕ) (h : x = y + z * (p^α : ℕ)) : Prop := 
  hFunc (z) (χ) (ψ) (f₁) (f₀) (g₁) (g₀) (x) (y) (x₀) (q) (h) ≡ 0 [ZMOD q]

/- proves `Fintype {r : (ZMod (p^α : ℕ))ˣ | sol_hFunc (z) (χ) (ψ) (f₁) (f₀) (g₁) (g₀) (x) (y) (r) (q) (h)}`-/
open Classical

/-
lemma (z : {r : (ZMod (p^α : ℕ))ˣ | sol_hFunc (z) (χ) (ψ) (f₁) (f₀) (g₁) (g₀) (x) (y) (r) (q) (h)}) :
    ∃(z₁ : (ZMod (p^α : ℕ))ˣ), 

def Set_χ : {r : (ZMod (p^α : ℕ))ˣ | sol_hFunc (z) (χ) (ψ) (f₁) (f₀) (g₁) (g₀) (x) (y) (r) (q) (h)} → ℂ := 
  fun z => χ (z)
-/

-- needs some rewriting
/- 
Set.image 
Set.mem_image_of_mem

χ '' {r : (ZMod (p^α : ℕ))ˣ | sol_hFunc (z) (χ) (ψ) (f₁) (f₀) (g₁) (g₀) (x) (y) (r) (q) (h)}
-/
theorem CharSum_in_two_sums (a b x y x₀ : ℤ) (h : x = y + z * (p^α : ℕ)) [NeZero (p^α : ℕ)]:
    CharSum (χ) (ψ) (p^(2*α)) = ∑ x : {r : (ZMod (p^α : ℕ)) | sol_hFunc (z) (χ) (ψ) (f₁) (f₀) (g₁) (g₀) (x) (y) (r) (q) (h)}, (χ x * ψ x * (∑ z₁ : (ZMod (p^α : ℕ)), eZMod (p^α) ((hFunc (z₁) (χ) (ψ) (f₁) (f₀) (g₁) (g₀) (x) (y) (x₀) (q) (h)) * z₁))) := by
  sorry

/- inner sum vanishes unless h (y) ≡ 0 (ZMod p^α) -/
theorem even_pow_final_formula (x y : ℤ) (h : x = y + z * (p^α : ℕ)) :
    CharSum (χ) (ψ) (p^(2*α)) = 
    if hFunc (z) (χ) (ψ) (f₁) (f₀) (g₁) (g₀) (x) (y) (x₀) (q) (h) ≡ 0 [ZMOD p^α] then (p^α : ℕ) * (∑ x : (ZMod (p^α : ℕ))ˣ, χ x * ψ x)
    else 0 := by
  sorry





/-
theorem bruh (g : ℝ → ℝ) (x x₀ : ℝ) (n : ℕ) (hx : x₀ < x) 
    (hf : ContDiffOn ℝ n g (Set.Icc x₀ x)) :
    1 = 1 := by
  have H : taylor_mean_remainder_lagrange f 
-/

/- Experiments

example (x : ℝ) : deriv (λ x => 1/(x^2+1)) = -2*x/(x^2+1)^2 := by
  sorry

/-
example (x : ℝ) : deriv (λ x => cos (sin x) * exp x) x = (cos(sin(x))- sin(sin(x))*cos(x))*exp(x) := by
-/

theorem bruh (f : ℤ → (ZMod q)) (g : ℤ → (ZMod q)) (x : ℤ): f (x) * (g (x))⁻¹ = 1 := by
  sorry

theorem bruh' (f : ℤ → (ZMod q)) (g : ℤ → (ZMod q)) (x : ℤ) (q : ℤ): x / q = 1 := by
  sorry

theorem rational_bruh (f : RatFunc ℚ) : (f.num/f.denom : ZMod q)= f.num * (f.denom : ZMod q) := by
  sorry

-/ 

/-
-- derivative : taylor series about the point y
-- (h_ne_dvd_q : ¬p ∣ (f.denom.eval x))
theorem taylor_series (y z : ZMod (p^α : ℕ)) (hxyz : x = y + z * (p^α : ℕ)) {hy : is_good f y (p^α : ℕ)}  :
    RatFunc.eval_prime (f) (x) (p^α : ℕ) (hx) ≡ RatFunc.eval_prime (f) (y) (p^α : ℕ) (hy) + z * (p^α : ℕ) [ZMOD (p^(2*α))]:= by 
  simp only [RatFunc.eval_prime]
  sorry
-/


-- laurent series of RatFunc


/-
theorem is_equal (f : RatFunc ℚ) (x : ℚ) (q : ℕ) (h : is_good f x q) : 
    RatFunc.eval_prime f x q h = 0 := by
  rw [RatFunc.eval_prime]
-/

