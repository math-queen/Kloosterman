import Mathlib
-- import def2_v2_kloosterman

#check RatFunc
-- import Desktop.UCL.mary_lister.kloosterman.def2_v2_kloosterman.lean

-- wrote Kloosterman stuff

-- inductive
-- valuation ring
-- mathlib4/mathlib/numbertheory/lucasprimality.lean

open Complex

-- need to build up the definition
/- 
So I think that this condition about f0 and f1 and f0(x) being coprime to q boils down to the following. 
You have a rational function f : RatFunc \Q and the condition you want is that firstly f.denom x isn't zero 
and secondly that the rational number f(x) is "coprime to q" in the sense that the denominator is coprime to q

Then you can "reduce f(x) mod q" by inverting the denominator mod q and multiplying by the numerator
-/

-- (haq : ((a : ZMod q).val).gcd q = 1)

noncomputable section

def eZMod (q : ℕ) (x : ZMod q) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x.val / q)

variable {p : ℕ} {α : ℕ} (z : ZMod (p^(2*α) : ℕ)) (χ : MulChar (ZMod (p^(2*α) : ℕ)) ℂ) (ζ : ℂˣ) (f : RatFunc ℚ) (x : ℚ) (q : ℕ) {h : is_good f x q} 
-- (q : ℕ) (x : ZMod q) (y : ℤ) (z : ZMod q)

-- variable {C : Type v} [CommRing C]

-- the denom is not equal to zero by the theorem `Ratfunc.denom_ne_zero`
-- numerator and denominator are coprime by the theorem `Ratfunc.is_coprime_num_denom`

def is_good (f : RatFunc ℚ) (x : ℚ) (q : ℕ) : Prop := 
  f.denom.eval x ≠ 0 ∧ (f.eval (RingHom.id ℚ) (x)).den.gcd q = 1

def RatFunc.eval_prime (f : RatFunc ℚ) (x : ℚ) (q : ℕ) {h : is_good f x q} : ZMod q := 
  let r := f.eval (RingHom.id ℚ) (x) -- apparently, ignores the let statement according to kevin
  r.num*(r.den : ZMod q)⁻¹

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



theorem taylor_series (y z : ZMod (p^α : ℕ)) (h : x = y + z*p^α) :
    RatFunc.eval_prime (f) = 1 := by 
  simp only [RatFunc.eval_prime]
  









-- laurent series of RatFunc













/-
theorem is_equal (f : RatFunc ℚ) (x : ℚ) (q : ℕ) (h : is_good f x q) : 
    RatFunc.eval_prime f x q h = 0 := by
  rw [RatFunc.eval_prime]
-/

