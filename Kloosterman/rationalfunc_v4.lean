import Mathlib.Tactic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Taylor
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Basic
import Kloosterman.lemma_char_v4
import Kloosterman.def2_v3_kloosterman

set_option autoImplicit false

open Complex Polynomial Int BigOperators Set

noncomputable section

/- # Note
We have to keep the variables `x` `y` as `ℤ` for the following theorems w.r.t taylor series
When dealing with Kloosterman sum, we will have to coerce the variable we're summing over rom ZMod q or (ZMod q)ˣ to ℤ 
Keep in mind 
when using the theorems for the taylor series and Kloosterman sum at the same time 
-/

variable {p : ℕ} {α : ℕ} (z : ZMod (p^α : ℕ)) (χ : MulChar (ZMod (p^(2*α) : ℕ)) ℂ) (ψ : AddChar (ZMod (p^(2*α) : ℕ)) ℂ) [pp : Fact p.Prime]
-- (q : ℕ) (x : ZMod q) (y : ℤ) (z : ZMod q)

variable (f₁ f₀ g₁ g₀ : Polynomial ℤ) (hα : 0 < α)

instance : NeZero (p ^ (2 * α)) := by

  sorry

instance : NeZero (p ^ α) := by
  sorry

-- the denom is not equal to zero by the theorem `Ratfunc.denom_ne_zero`
-- numerator and denominator are coprime by the theorem `Ratfunc.is_coprime_num_denom`

-- f.denom.eval x ≠ 0 
-- RatFunc (ZMod q)ˣ doesn't work

/- 
we need `.eval` because we're trying to evaluate the function f at specific value x
-/
def rationalFunc (p₁ p₀ : Polynomial ℤ) (x₀ : ℤ) (q : ℕ) : ZMod q :=
  let r := p₀.eval x₀
  (p₁.eval x₀) * (r : ZMod q)⁻¹

/- 
# ASK KEVIN
whether there's more compact way to define `rationalFunc_inverse`  which is the inverse of rationalFunc mod ZMod q and `poly_eval_ZMod`
-/ 
def rationalFunc_inverse (p₀ : Polynomial ℤ) (x₀ : ℤ) (q : ℕ) : ZMod q :=
  ((p₀.eval x₀ : ℤ) : ZMod q)⁻¹

/- derivative of a rational function f₁/f₀ at x₀ under mod p^(2*α) -/
/- Should I do `ℤ` or `ZMod q` for the function -/
def rationalFunc_deriv (p₁ p₀ : Polynomial ℤ) (x₀ : ℤ) (q : ℕ) : ZMod q :=
  (((Polynomial.derivative (R := ℤ)) p₁).eval x₀ * (rationalFunc_inverse (p₀) (x₀) (q)) 
  - ((rationalFunc_inverse (p₀) (x₀) (q))^2 : ZMod q) * ((Polynomial.derivative (R := ℤ)) p₀).eval x₀ * p₁.eval x₀)

def CharSum (q : ℕ) : ℂ :=
  ∑ x : (ZMod q)ˣ, χ (rationalFunc f₁ f₀ x q) * ψ (rationalFunc g₁ g₀ x q)

-- section PolyTaylorSeries

theorem poly_taylor (p₀ : Polynomial ℤ) (y : ℤ) : 
    p₀ = ((taylor y p₀).sum fun i a => C a * (X - C y) ^ i) := by
  -- have H := taylor_coeff_one (y) (p₀)
  exact Eq.symm (sum_taylor_eq p₀ y)

/- note to myself 
By definition, 
`((taylor y p₀).sum fun i a => a * ((z : ℤ) * (p^α : ℕ)) ^ i)`
`= ∑ n in support (↑(taylor y) p₀), coeff (↑(taylor y) p₀) n * (↑z * ↑(p ^ α)) ^ n`
-/
-- # ASK KEVIN
theorem poly_taylor_eval (p₀ : Polynomial ℤ) (x y : ℤ) (h : x = y + z * (p^α : ℕ)) :
    p₀.eval (x : ℤ) = ((taylor y p₀).sum fun i a => a * ((z : ℤ) * (p^α : ℕ)) ^ i) := by
  nth_rw 1 [poly_taylor p₀ y] -- rewrites only lhs
  rw [sum]
  simp only [eval_finset_sum, eval_mul, eq_intCast, eval_int_cast, cast_id, eval_pow, eval_sub, eval_X, Nat.cast_pow]
  rw [h]
  simp only [Nat.cast_pow, add_sub_cancel']
  rfl
  -- rw [Polynomial.eval_C]
  -- rw [Polynomial.eval_X]

/- # List
def support_add (i : ℕ) (x₀ : ℤ) (p₀ : Polynomial ℤ) : Finset ℕ :=
  ((taylor x₀ p₀).support.to_list 
  -/


/- maybe we could have something like 
`∑ i in (taylor y p₀).support + 2, ((taylor y p₀).coeff (i) * ((z : ℤ) * (p^α : ℕ)) ^ (i))`
-/

-- it already exists 
-- delete this later after I change the code for the theorems that use the below lemma
lemma support_coeff_zero (p₀ : Polynomial ℤ) (x₀ : ℤ) (i : ℕ) :
    (taylor x₀ p₀).coeff i = 0 ↔ i ∉ (taylor x₀ p₀).support := by
  exact Iff.symm not_mem_support_iff

/-
def finset.max  {α : Type u_2}  [linear_order α]  (s : finset α) :
with_bot α
-/ 

open Finset

lemma Finset_in_Range (p₀ : Polynomial ℤ) (y : ℤ) (H : (taylor y p₀).support.Nonempty) :
    (taylor y p₀).support ⊆ Finset.range ((taylor y p₀).support.max' H + 1) := by
  apply supp_subset_range
  rw [Nat.lt_succ_iff]
  apply Finset.le_max' 
  simp only [mem_support_iff]
  rw [← leadingCoeff]
  rw [leadingCoeff_ne_zero]
  exact Iff.mp nonempty_support_iff H

lemma Finset_eq_Range (p₀ : Polynomial ℤ) (y : ℤ) (H : (taylor y p₀).support.Nonempty) :
    Finset.range ((taylor y p₀).support.max' H + 1) = (taylor y p₀).support ∪ (Finset.range ((taylor y p₀).support.max' H + 1) \ (taylor y p₀).support) := by
  have rrange := Finset_in_Range p₀ y H 
  exact Eq.symm (Finset.union_sdiff_of_subset rrange)

lemma taylor_sum_eq_zero (p₀ : Polynomial ℤ) (y : ℤ) (H : (taylor y p₀).support.Nonempty) : 
    ∑ i in (Finset.range ((taylor y p₀).support.max' H + 1) \ (taylor y p₀).support), ((taylor y p₀).coeff i * ((z : ℤ) * (p^α : ℕ)) ^ i) = 0:= by  
  rw [← Finset.sum_const_zero (s := (Finset.range ((taylor y p₀).support.max' H + 1) \ (taylor y p₀).support))]
  apply Finset.sum_congr rfl
  intro i hi
  apply mul_eq_zero_of_left
  apply Iff.mp not_mem_support_iff
  exact (Iff.mp (Finset.mem_sdiff) hi).right
  
/- 
Equivalent to proving the following:
`p₀.eval x + ∑ i in (Finset.range ((taylor y p₀).support.max' H + 1) \ (taylor y p₀).support), ((taylor y p₀).coeff i * ((z : ℤ) * (p^α : ℕ)) ^ i)`
`= ∑ i in Finset.range ((taylor y p₀).support.max' H + 1), ((taylor y p₀).coeff i * ((z : ℤ) * (p^α : ℕ)) ^ i)`
-/
-- idea : using the theorem `not_mem_support_iff`, let's convert the sum over Finset into the sum over range
lemma sum_over_FinsetToRange (p₀ : Polynomial ℤ) (x y : ℤ) (H : (taylor y p₀).support.Nonempty) (h : x = y + z * (p^α : ℕ)) : 
    p₀.eval x = ∑ i in Finset.range ((taylor y p₀).support.max' H + 1), ((taylor y p₀).coeff i * ((z : ℤ) * (p^α : ℕ)) ^ i) := by 
  rw [← add_zero (p₀.eval x)]
  rw [← taylor_sum_eq_zero z p₀ y H]
  rw [poly_taylor_eval z p₀ x y h]
  rw [sum]
  rw [← Finset.sum_union (Finset.disjoint_sdiff)]
  rw [← Finset_eq_Range]

/- # Note 
It's perfectly up to me to decide whether to prove only v1 or both v1 & v2.
Need to choose the one that will allow us to easily prove the lemma `sum_higher_terms_in_poly`
-/
/- I need to rewrite a nicer looking proof. The simp only statements look awful -/ 
lemma poly_taylor_eval_term_by_term (p₀ : Polynomial ℤ) (x y : ℤ) (H : (taylor y p₀).support.Nonempty) (support_le : (taylor y p₀).support.max' H > 0) (h : x = y + z * (p^α : ℕ)) :
    p₀.eval x = p₀.eval y + ((Polynomial.derivative (R := ℤ)) p₀).eval y * z * (p^α : ℕ) 
    + ∑ i in (Finset.range ((taylor y p₀).support.max' H + 1) \ {0}) \ {1}, ((taylor y p₀).coeff i * ((z : ℤ) * (p^α : ℕ)) ^ i) := by
  rw [sum_over_FinsetToRange z p₀ x y H h]
  rw [← union_sdiff_of_subset (s := {0}) (t := Finset.range ((taylor y p₀).support.max' H + 1))]
  · rw [sum_union, sum_singleton, taylor_coeff_zero, pow_zero, mul_one]
    rw [← union_sdiff_of_subset (s := {1}) (t := Finset.range ((taylor y p₀).support.max' H + 1) \ {0})]
    · rw [sum_union, sum_singleton]
      · rw [taylor_coeff_one, pow_one]
        repeat rw [Finset.union_sdiff_cancel_left]
        · rw [mul_assoc]
          rw [add_assoc]
        · simp
        · simp
        -- rw [Finset.union_sdiff_cancel_left (s := {0}) (t := {1})]
      · simp only [Finset.mem_range, add_pos_iff, or_true, not_true, mem_sdiff, lt_add_iff_pos_left, and_true, not_lt,
        nonpos_iff_eq_zero, Finset.disjoint_singleton_left, and_false, not_false_eq_true]
    · simp only [Finset.mem_range, add_pos_iff, or_true, not_true, Finset.singleton_subset_iff, mem_sdiff,
      lt_add_iff_pos_left, and_true]
      exact support_le
    · simp only [Finset.mem_range, add_pos_iff, or_true, not_true, Finset.disjoint_singleton_left, mem_sdiff,
      and_false, not_false_eq_true]
  · simp only [Finset.singleton_subset_iff, Finset.mem_range, add_pos_iff, or_true]
  -- ends the calculation for the first term

/- for the lemma `sum_move_two` -/
lemma Nat.lt_right_cancel (a₁ a₂ a₃ : ℕ) (h : a₃ > a₂) : a₁ < a₃ → a₁ - a₂ < a₃ - a₂ := by 
  intro ha₁_lt_ha₃
  obtain (ha_lt | ha_le) := lt_or_le 0 (a₁ - a₂)
  · apply Nat.lt_of_add_lt_add_right (b := a₂)
    -- simp only [tsub_pos_iff_lt] at ha_lt 
    rw [tsub_pos_iff_lt] at ha_lt
    have ha_le := Nat.le_of_lt ha_lt
    -- have ha₁_le_ha₃ := Nat.le_of_lt ha₁_lt_ha₃
    rw [Nat.sub_add_cancel ha_le]
    have h_le := Nat.le_of_lt h
    rw [Nat.sub_add_cancel h_le]
    linarith
  · rw [Nat.le_zero] at ha_le
    rw [ha_le]
    exact Nat.sub_pos_of_lt h
  
lemma Nat.eq_cancel_right (a b c : ℕ) (ha : a ≥ c) (hb : b ≥ c) :
    a - c = b - c → a = b := by
  intro hab
  rw [Nat.sub_eq_iff_eq_add ha] at hab
  rw [Nat.sub_add_cancel hb] at hab
  exact hab

lemma aLargerTwo (p₀ : Polynomial ℤ) (y : ℤ) (H : (taylor y p₀).support.Nonempty) (a : ℕ) (ha : a ∈ (Finset.range ((taylor y p₀).support.max' H + 1) \ {0}) \ {1}) : a ≥ 2 := by
  simp only [mem_sdiff, lt_add_iff_pos_left] at ha
  rw [and_assoc] at ha
  rcases ha with ⟨h₁, h₂, h₃⟩ -- splits into 3 goals
  rw [not_mem_singleton] at h₂
  rw [← Nat.one_le_iff_ne_zero] at h₂
  rw [not_mem_singleton, ne_iff_lt_or_gt] at h₃
  simp only [Finset.mem_range] at h₁ ⊢
  have h₂Andh₃ : a ≥ 1 ∧ (a < 1 ∨ a > 1) → a ≥ 2
  { choose _ ha
    cases' ha with _ a_lt_one
    · linarith
    · exact a_lt_one  }
  exact h₂Andh₃ ⟨h₂, h₃⟩

lemma sum_move_two (p₀ : Polynomial ℤ) (y : ℤ) (H : (taylor y p₀).support.Nonempty) : 
    ∑ i in (Finset.range ((taylor y p₀).support.max' H + 1) \ {0}) \ {1}, ((taylor y p₀).coeff i * ((z : ℤ) * (p^α : ℕ)) ^ i)
    = ∑ i in Finset.range ((taylor y p₀).support.max' H - 1), ((taylor y p₀).coeff (i+2) * ((z : ℤ) * (p^α : ℕ)) ^ (i+2)) := by
  apply Finset.sum_bij (fun i _ ↦ i - 2)
  · intro a ha
    have aLargertwo := aLargerTwo p₀ y H a ha
    simp only [mem_sdiff, lt_add_iff_pos_left] at ha
    rw [and_assoc] at ha
    rcases ha with ⟨h₁, _, _⟩ -- splits into 3 goals
    simp only [Finset.mem_range] at h₁ ⊢
    obtain _ | _ | hLargerOne := lt_trichotomy ((taylor y p₀).support.max' H) 1
    · linarith
    · linarith
    · have hLargerTwo := Nat.succ_lt_succ hLargerOne
      exact Nat.lt_right_cancel a 2 ((taylor y p₀).support.max' H + 1) hLargerTwo h₁
  · intro a ha
    have useful := aLargerTwo p₀ y H a ha
    rw [Nat.sub_add_cancel useful]
  · intro a₁ a₂ ha₁ ha₂ ha₁a₂
    have usefulFora₁ := aLargerTwo p₀ y H a₁ ha₁
    have usefulFora₂ := aLargerTwo p₀ y H a₂ ha₂
    exact Nat.eq_cancel_right a₁ a₂ 2 usefulFora₁ usefulFora₂ ha₁a₂
  · intro b hb
    use (b + 2)
    have hb_two : b + 2 ∈ (Finset.range ((taylor y p₀).support.max' H + 1) \ {0}) \ {1}
    { repeat rw [Finset.mem_sdiff]
      repeat constructor -- # Ask Kevin: How to split it into three goals efficiently
      · rw [Finset.mem_range] at *
        exact Nat.add_lt_of_lt_sub hb
      · rw [not_mem_singleton]
        exact Nat.succ_ne_zero (b + 1)
      · rw [not_mem_singleton]
        exact Nat.succ_succ_ne_one b  }
    use hb_two
    rfl

-- once we convert the sum into Finset.range, then we can use the theorem `finset.sum_cons` or `finset.sum_disj_union` to sort this out

lemma sum_higher_terms_in_poly (p₀ : Polynomial ℤ) (y : ℤ) (H : (taylor y p₀).support.Nonempty) : 
    ∃(z₀ : ℤ), (p^(2*α) : ℕ) * z₀
    = ∑ i in (Finset.range ((taylor y p₀).support.max' H + 1) \ {0}) \ {1}, ((taylor y p₀).coeff i * ((z : ℤ) * (p^α : ℕ)) ^ i) := by
  -- rcases (taylor y p₀).support.max' H > 1 
  rw [sum_move_two z p₀ y H]
  use ∑ i in Finset.range ((taylor y p₀).support.max' H - 1), ((taylor y p₀).coeff (i+2) * (z : ℤ) ^ (i + 2) * ((p^α : ℕ) ^ i : ℤ))
  rw [mul_comm]
  rw [Finset.sum_mul]
  rw [pow_mul']
  apply Finset.sum_congr rfl
  intro x _
  -- rw [mul_pow (z : ℤ) (p^α : ℤ) x]
  rw [mul_assoc]
  push_cast
  rw [← pow_add ((p : ℤ)^α) x 2]
  rw [mul_pow]
  rw [mul_assoc]

theorem poly_taylor_eval_ZMod (p₀ : Polynomial ℤ) (x y : ℤ) (H : (taylor y p₀).support.Nonempty) (support_le : (taylor y p₀).support.max' H > 0) (h : x = y + z * (p^α : ℕ)) :
    ((p₀.eval x : ℤ) : ZMod (p^(2*α))) = ((p₀.eval y + ((Polynomial.derivative (R := ℤ)) p₀).eval y * z * (p^α : ℕ) : ℤ) : ZMod (p^(2*α))) := by
  rw [poly_taylor_eval_term_by_term z p₀ x y H support_le h]
  have hz := sum_higher_terms_in_poly z p₀ y H 
  cases' hz with z₀ hz₀
  rw [← hz₀]
  rw [cast_add]
  rw [cast_mul]
  rw [cast_ofNat]
  rw [ZMod.nat_cast_self]
  rw [zero_mul]
  rw [add_zero]

variable (p₁ p₀ : Polynomial ℤ)

theorem rationalFunc_well_defined_ZMod (x y : ℤ) (H₁ : (taylor y p₁).support.Nonempty) (H₀ : (taylor y p₀).support.Nonempty) (support_le_H₁ : (taylor y p₁).support.max' H₁ > 0) (support_le_H₀ : (taylor y p₀).support.max' H₀ > 0) (h : x = y + z * (p^α : ℕ)) :
    rationalFunc (p₁) (p₀) (x) (p^(2*α)) = 
    (p₁.eval y + ((Polynomial.derivative (R := ℤ)) p₁).eval y * z * (p^α : ℕ)) 
    * ((p₀.eval y + ((Polynomial.derivative (R := ℤ)) p₀).eval y * z * (p^α : ℕ)) : ZMod (p^(2*α)))⁻¹ := by
  simp only [rationalFunc]
  rw [poly_taylor_eval_ZMod z p₁ x y H₁ support_le_H₁ h]
  rw [poly_taylor_eval_ZMod z p₀ x y H₀ support_le_H₀ h]
  push_cast
  simp

/- corollary of theorem `poly_taylor_eval_ZMod` -/

lemma congr_IsUnit (q : ℕ) (a b : ZMod q) (hCongr : a ≡ b [ZMOD q]) (IsUnitFora : IsUnit a): IsUnit b := by
  rw [← ZMod.int_cast_eq_int_cast_iff] at hCongr
  simp only [ZMod.int_cast_cast, ZMod.cast_id', id_eq] at hCongr  -- try out simp?
  rw [← hCongr]
  exact IsUnitFora

lemma p_dvd_pPow (hα : 0 < α) : p ∣ p ^ α := by
  rw [Nat.pos_iff_ne_zero] at hα
  exact dvd_pow_self p hα

lemma poly_zmod_prime_ofPrimePow (a b : ℤ) (hα : 0 < α) (h : (a : ZMod (p^α)) = b) : 
    (a : ZMod p) = b := by 
  rw [← ZMod.cast_int_cast (p_dvd_pPow (p := p) hα) a]
  rw [← ZMod.cast_int_cast (p_dvd_pPow (p := p) hα) b]
  rw [h]

lemma NeZero_pPow : NeZero (p^(2*α)) := ⟨pow_ne_zero (2*α) <| Prime.ne_zero hp⟩

/- think about how to incorporate this into the proof for the lemma `nat_gcd_ZMod_prime_eq_one_iff_ZMod_primePow` -/
lemma nat_gcd_prime_eq_one_iff_primePow (a : ℤ) (hα : 0 < α) : 
    Nat.gcd ((a : ZMod (p^(2*α))).val) (p ^ (2 * α)) = 1 ↔ Nat.gcd (a : ZMod (p^(2*α))).val p = 1 := by
  have two_alpha_lt : 0 < 2 * α := by exact Nat.succ_mul_pos 1 hα
  exact Nat.coprime_pow_right_iff two_alpha_lt (ZMod.val (a : ZMod (p^(2*α)))) p

-- proof is quite repetitive bruh 
-- decide when to place this proof: the nat version of this proof is actually needed much later in this file 
lemma nat_val_congr_self (n q : ℕ) [NeZero q] : (n : ZMod q).val ≡ n [ZMOD q] := by
  rw [← ZMod.int_cast_eq_int_cast_iff]
  simp only [ZMod.nat_cast_val, ZMod.int_cast_cast, ZMod.cast_nat_cast', cast_ofNat]

lemma int_val_congr_self (n : ℤ) (q : ℕ) [NeZero q] : (n : ZMod q).val ≡ n [ZMOD q] := by
  rw [← ZMod.int_cast_eq_int_cast_iff]
  simp only [ZMod.nat_cast_val, ZMod.int_cast_cast, ZMod.cast_int_cast']

/- for `[MOD p]` -/
lemma val_congr_self_mod_prime_congr_primePow (a : ℤ) (hα : 0 < α) [NeZero (p^α)]: 
    (a : ZMod p).val ≡ (a : ZMod (p^α)).val [MOD p] := by 
  -- have : (((a : ZMod (p^α)).val : ℤ) : ZMod p) = (((a : ZMod p).val : ℤ) : ZMod p) := by sorry
  -- simp only [ZMod.nat_cast_val, ZMod.int_cast_cast, cast_ofNat] at this
  suffices ((a : ZMod p).val : ZMod p) = ((a : ZMod (p^α)).val : ZMod p) by
    rw [ZMod.eq_iff_modEq_nat] at this
    exact this
  rw [← cast_ofNat]
  rw [← cast_ofNat (a : ZMod (p^α)).val]
  have : NeZero p := by exact { out := Prime.ne_zero hp }
  rw [ZMod.int_cast_eq_int_cast_iff ((a : ZMod p).val) ((a : ZMod (p^α)).val) p]
  apply Int.ModEq.trans (b := a) (int_val_congr_self a p) _
  apply Int.ModEq.of_mul_left (p^(α - 1))
  rw [← Nat.cast_mul (p ^ (α -1)) p]
  nth_rw 2 [← pow_one p]
  rw [← pow_add]
  rw [Nat.sub_add_cancel hα]
  exact ModEq.symm (int_val_congr_self a (p ^ α))

instance (a c : ℕ) : Nat.gcd a p = 1 ↔ Nat.gcd (a + c * p) p = 1 := by
  exact Iff.symm (Nat.coprime_add_mul_right_left a p c)
  
lemma nat_gcd_ZMod_prime_eq_one_iff_ZMod_primePow (a : ℤ) (hα : 0 < α) : 
    Nat.gcd ((a : ZMod (p^(2*α))).val) (p ^ (2 * α)) = 1 ↔ Nat.gcd (a : ZMod p).val p = 1 := by
  repeat rw [← Nat.coprime_iff_gcd_eq_one]
  have two_alpha_lt : 0 < 2 * α := by exact Nat.succ_mul_pos 1 hα
  rw [Nat.coprime_pow_right_iff two_alpha_lt (ZMod.val (a : ZMod (p^(2*α)))) p]
  have : NeZero p := by exact { out := (Prime.ne_zero hp) }
  -- have : (a : ZMod p).val < p := by exact ZMod.val_lt (a : ZMod p)
  have hexists := exists_eq_of_nat_coe_mod_eq (a : ZMod p).val (a : ZMod (p^(2*α))).val p (ZMod.val_lt (a : ZMod p)) (val_congr_self_mod_prime_congr_primePow hp a two_alpha_lt)
  cases' hexists with c hcexists
  rw [hcexists]
  exact (Nat.coprime_add_mul_right_left (a : ZMod p).val p c)

/- for the lemma `poly_at_yIsUnit` -/
lemma NatSmallerZMod_Nat_eq (a b q : ℕ) (ha : a < q) (hb : b < q) (hab : (a : ZMod q) = (b : ZMod q)): a = b := by
  -- have eq_zmod_val : (a : ZMod q).val = (b : ZMod q).val := by exact congrArg ZMod.val hab
  have eq_zmod_val := congrArg ZMod.val hab
  rw [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] at eq_zmod_val
  exact eq_zmod_val

lemma one_lt_primePow (hα : 0 < α) : 1 < p ^ α := by
  rw [← Nat.prime_iff] at hp
  exact Nat.one_lt_pow α p hα (Nat.Prime.one_lt hp)

lemma one_lt_twoprimePow (hα : 0 < α) : 1 < p ^ (2 * α) := by
  have twoalpha : 0 < 2 * α := by exact Nat.succ_mul_pos 1 hα
  exact one_lt_primePow hp twoalpha

/- rewrite the proof later. Very messy -/
lemma poly_at_yIsUnit (p₀ : Polynomial ℤ) (x y : ℤ) (H : (taylor y p₀).support.Nonempty) (support_le : (taylor y p₀).support.max' H > 0) (p₀_at_xIsUnit : IsUnit ((p₀.eval x : ℤ) : ZMod (p^(2*α)))) [NeZero (p^α)] (h : x = y + z * (p^α : ℕ)) (hα : 0 < α) : 
    IsUnit ((p₀.eval y : ℤ) : ZMod (p^(2*α))) := by
  -- by_contra NeUnit
  -- zmod.mul_inv_of_unit
  rw [isUnit_iff_exists_inv]
  use ((p₀.eval y : ℤ) : ZMod (p^(2*α)))⁻¹
  suffices Nat.gcd (((p₀.eval y : ℤ) : ZMod (p ^ (2 * α))).val) (p ^ (2 * α)) = 1 by
    rw [ZMod.mul_inv_eq_gcd]
    rw [this]
    exact Nat.cast_one
  have poly_x_inv_one_PrimePow := ZMod.mul_inv_of_unit ((p₀.eval x : ℤ) : ZMod (p^(2*α))) p₀_at_xIsUnit
  have poly_x_inv_PrimePow := ZMod.mul_inv_eq_gcd ((p₀.eval x : ℤ) : ZMod (p^(2*α)))
  rw [poly_x_inv_PrimePow] at poly_x_inv_one_PrimePow
  rw [← Nat.cast_one] at poly_x_inv_one_PrimePow
  have pPowNeZero : p ^ (2 * α) ≠ 0 := by exact NeZero.ne (p ^ (2 * α))
  have pPowltZero : 0 < p ^ (2 * α) := by exact Nat.pos_of_ne_zero pPowNeZero
  have eval_at_x_val_lt : Nat.gcd (((p₀.eval x : ℤ) : ZMod (p ^ (2 * α))).val) (p ^ (2 * α)) < p ^ (2 * α)
  { obtain h₁ | h₂ | h₃ := lt_trichotomy (Nat.gcd (((p₀.eval x : ℤ) : ZMod (p ^ (2 * α))).val) (p ^ (2 * α))) (p ^ (2 * α))
    · exact h₁
    · rw [h₂] at poly_x_inv_one_PrimePow
      rw [ZMod.nat_cast_self] at poly_x_inv_one_PrimePow
      rw [← Nat.cast_zero] at poly_x_inv_one_PrimePow
      -- rw [Nat.cast_one] at poly_x_inv_one_PrimePow
      have := NatSmallerZMod_Nat_eq 0 1 (p ^ (2 * α)) pPowltZero (one_lt_twoprimePow hp hα) poly_x_inv_one_PrimePow
      tauto
    · have := Nat.gcd_le_right (m := (((p₀.eval x : ℤ) : ZMod (p ^ (2 * α))).val)) (p ^ (2 * α)) pPowltZero
      exfalso
      have := lt_of_lt_of_le (c := p ^ (2 * α)) h₃ this
      simp only [lt_self_iff_false] at this }
  have poly_x_inv_gcd_prime := ZMod.mul_inv_eq_gcd ((p₀.eval x : ℤ) : ZMod p) 
  have val_x_pPow := NatSmallerZMod_Nat_eq (Nat.gcd (((p₀.eval x : ℤ) : ZMod (p ^ (2 * α))).val) (p ^ (2 * α))) 1 (p ^ (2 * α)) eval_at_x_val_lt (one_lt_twoprimePow hp hα) poly_x_inv_one_PrimePow
  rw [nat_gcd_ZMod_prime_eq_one_iff_ZMod_primePow hp (p₀.eval x) hα] at val_x_pPow
  rw [val_x_pPow] at poly_x_inv_gcd_prime

  have hy_primePow := ZMod.mul_inv_eq_gcd ((p₀.eval y : ℤ) : ZMod (p^(2*α)))
  have two_alpha_lt : 0 < 2 * α := by exact Nat.succ_mul_pos 1 hα
  
  have poly_ZModPrimePow_eq := poly_taylor_eval_ZMod z p₀ x y H support_le h -- for `poly_ZModPrime`
  have poly_ZModPrime := poly_zmod_prime_ofPrimePow (α := 2 * α) (p₀.eval x) (p₀.eval y + ((Polynomial.derivative (R := ℤ)) p₀).eval y * z * (p^α : ℕ) : ℤ) two_alpha_lt poly_ZModPrimePow_eq
  -- rw [← cast_zero] at hy
  -- have eval_yZModPrime := poly_zmod_prime_ofPrimePow (α := 2 * α) (p₀.eval y) 0 two_alpha_lt this
  rw [cast_add] at poly_ZModPrime
  rw [mul_assoc] at poly_ZModPrime
  rw [cast_mul] at poly_ZModPrime
  rw [cast_mul] at poly_ZModPrime
  rw [ZMod.int_cast_cast] at poly_ZModPrime
  rw [Nat.cast_pow, cast_pow, cast_ofNat, CharP.cast_eq_zero] at poly_ZModPrime 
  rw [zero_pow hα] at poly_ZModPrime 
  rw [mul_zero] at poly_ZModPrime 
  rw [mul_zero] at poly_ZModPrime 
  rw [add_zero] at poly_ZModPrime 
  rw [poly_ZModPrime] at poly_x_inv_gcd_prime
  rw [Nat.cast_one] at poly_x_inv_gcd_prime
  have poly_y_inv_gcd_prime := ZMod.mul_inv_eq_gcd ((p₀.eval y : ℤ) : ZMod p)
  rw [poly_x_inv_gcd_prime] at poly_y_inv_gcd_prime
  /- will be used multiple times later -/
  have nat_hp := Iff.mpr Nat.prime_iff hp
  have hp_zero_lt : 0 < p := by exact Nat.Prime.pos nat_hp
  have eval_at_y_val_lt : Nat.gcd (((p₀.eval y : ℤ) : ZMod p).val) p < p
  { obtain h₁ | h₂ | h₃ := lt_trichotomy (Nat.gcd (((p₀.eval y : ℤ) : ZMod p).val) p) p
    · exact h₁
    · rw [h₂] at poly_y_inv_gcd_prime
      rw [ZMod.nat_cast_self] at poly_y_inv_gcd_prime
      rw [← Nat.cast_zero, ← Nat.cast_one] at poly_y_inv_gcd_prime
      have := NatSmallerZMod_Nat_eq 0 1 p hp_zero_lt (Nat.Prime.one_lt nat_hp) (Eq.symm poly_y_inv_gcd_prime)
      tauto
    · have := Nat.gcd_le_right (m := (((p₀.eval y : ℤ) : ZMod p).val)) p hp_zero_lt
      exfalso
      have := lt_of_lt_of_le (c := p) h₃ this
      simp only [lt_self_iff_false] at this }
  have hp_one_lt : 1 < p := by exact Nat.Prime.one_lt nat_hp
  rw [← Nat.cast_one] at poly_y_inv_gcd_prime
  have poly_y_prime_gcd_eq_one := NatSmallerZMod_Nat_eq (Nat.gcd (((p₀.eval y : ℤ) : ZMod p).val) p) 1 p eval_at_y_val_lt hp_one_lt (Eq.symm poly_y_inv_gcd_prime)
  exact Iff.mpr (nat_gcd_ZMod_prime_eq_one_iff_ZMod_primePow hp (p₀.eval y) hα) poly_y_prime_gcd_eq_one
  done

lemma ZMod_IsUnit_inv_eq_iff_eq_mul {a b c : ZMod (p^(2*α))} (h : IsUnit b): a * b⁻¹ = c ↔ a = c * b := by
  -- exact mul_inv_eq_iff_eq_mul (G := ZMod (p^(2*α)))
  apply Iff.intro
  · intro habc
    rw [← habc]
    rw [mul_assoc]
    rw [ZMod.inv_mul_of_unit b h]
    rw [mul_one]
  · intro hacb
    rw [hacb]
    rw [mul_assoc]
    rw [ZMod.mul_inv_of_unit b h]
    rw [mul_one]

/- corollary of theorem `poly_taylor_eval_ZMod` -/
-- Do something about the `IsUnit (p₀.eval x)` later
-- this should become the final boss for the power world
lemma rationalFunc_eq_ZMod (p₁ p₀ : Polynomial ℤ) (x y : ℤ) [NeZero (p ^ α)] (H₁ : (taylor y p₁).support.Nonempty) (H₀ : (taylor y p₀).support.Nonempty) (support_le_H₁ : (taylor y p₁).support.max' H₁ > 0) 
    (support_le_H₀ : (taylor y p₀).support.max' H₀ > 0) (h : x = y + z * (p^α : ℕ)) (p₀_at_xIsUnit : IsUnit ((p₀.eval x : ℤ) : ZMod (p^(2*α)))) (hα : 0 < α) :
    rationalFunc (p₁) (p₀) (x) (p^(2*α)) = rationalFunc (p₁) (p₀) (y) (p^(2*α)) 
    + (rationalFunc_deriv (p₁) (p₀) (y) (p^(2*α))) * z * (p^α : ℕ) := by
  simp only [rationalFunc_well_defined_ZMod]
  simp only [rationalFunc, rationalFunc_deriv]
  -- apply Iff.mp isUnit_iff_ne_zero
  rw [ZMod_IsUnit_inv_eq_iff_eq_mul p₀_at_xIsUnit]
  rw [poly_taylor_eval_ZMod z p₁ x y H₁ support_le_H₁ h]
  rw [poly_taylor_eval_ZMod z p₀ x y H₀ support_le_H₀ h]
  simp only [rationalFunc_inverse]
  repeat rw [cast_add]
  rw [cast_mul]
  rw [add_mul]
  simp only [mul_add]
  /- process of cancelling out `↑(eval y p₀)` with its inverse -/
  -- gets rid of the inverses in the first term of the rhs
  rw [mul_assoc]
  rw [ZMod.inv_mul_of_unit ((p₀.eval y : ℤ) : ZMod (p^(2*α))) (poly_at_yIsUnit z hp p₀ x y H₀ support_le_H₀ p₀_at_xIsUnit h hα)]
  -- moving around `↑(eval y p₀)` so that it will be cancelled with its inverse term
  rw [mul_assoc (((((Polynomial.derivative (R := ℤ)) p₁).eval y : ℤ) : ZMod (p^(2*α))) * ((p₀.eval y : ℤ) : ZMod (p^(2*α)))⁻¹ - ((p₀.eval y : ℤ) : ZMod (p^(2*α)))⁻¹ ^ 2 * ((((Polynomial.derivative (R := ℤ)) p₀).eval y : ℤ) : ZMod (p^(2*α))) * ((p₁.eval y : ℤ) : ZMod (p^(2*α))))]
  rw [mul_assoc (((((Polynomial.derivative (R := ℤ)) p₁).eval y : ℤ) : ZMod (p^(2*α))) * ((p₀.eval y : ℤ) : ZMod (p^(2*α)))⁻¹ - ((p₀.eval y : ℤ) : ZMod (p^(2*α)))⁻¹ ^ 2 * ((((Polynomial.derivative (R := ℤ)) p₀).eval y : ℤ) : ZMod (p^(2*α))) * ((p₁.eval y : ℤ) : ZMod (p^(2*α))))]
  rw [mul_assoc (z : ZMod (p^(2*α)))]
  rw [mul_comm (p^α : ZMod (p^(2*α)))]
  rw [← mul_assoc (z : ZMod (p^(2*α)))]
  rw [mul_comm (z : ZMod (p^(2*α)))]
  rw [mul_assoc ((p₀.eval y : ℤ) : ZMod (p^(2*α)))]
  rw [← mul_assoc]
  -- rearranging to make sure the inverse `↑(eval y p₀)⁻¹` will be cancelled 
  rw [mul_assoc (((p₀.eval y : ℤ) : ZMod (p^(2*α)))⁻¹ ^ 2)]
  nth_rw 1 [pow_two]
  rw [mul_assoc ((p₀.eval y : ℤ) : ZMod (p^(2*α)))⁻¹]
  rw [mul_comm ((p₀.eval y : ℤ) : ZMod (p^(2*α)))⁻¹]
  rw [sub_mul]
  -- we have expanded out the expression
  -- rearrange the third term after expansion for the inverse to be cancelled out
  rw [mul_assoc ((((Polynomial.derivative (R := ℤ)) p₁).eval y : ℤ) : ZMod (p^(2*α)))]
  -- rearrange the fourth term
  rw [mul_assoc ((p₀.eval y : ℤ) : ZMod (p^(2*α)))⁻¹]
  rw [mul_assoc ((p₀.eval y : ℤ) : ZMod (p^(2*α)))⁻¹]
  rw [mul_assoc ((((Polynomial.derivative (R := ℤ)) p₀).eval y : ℤ) : ZMod (p^(2*α)))]
  rw [mul_assoc ((((Polynomial.derivative (R := ℤ)) p₀).eval y : ℤ) : ZMod (p^(2*α)))]
  rw [mul_assoc (((p₁.eval y : ℤ) : ZMod (p^(2*α)))) ((p₀.eval y : ℤ) : ZMod (p^(2*α)))⁻¹ ((p₀.eval y : ℤ) : ZMod (p^(2*α)))]
  -- cancel out the inverse!
  rw [ZMod.inv_mul_of_unit ((p₀.eval y : ℤ) : ZMod (p^(2*α))) (poly_at_yIsUnit z hp p₀ x y H₀ support_le_H₀ p₀_at_xIsUnit h hα)]
  
  /- rearrange the fourth term to cancel out the second and fourth term -/
  simp only [mul_one]
  nth_rw 1 [mul_comm ((((Polynomial.derivative (R := ℤ)) p₀).eval y : ℤ) : ZMod (p^(2*α)))]
  rw [← mul_assoc ((p₀.eval y : ℤ) : ZMod (p^(2*α)))⁻¹]
  rw [mul_comm ((p₀.eval y : ℤ) : ZMod (p^(2*α)))⁻¹]
  -- expansion out of the brackets
  rw [sub_mul]
  -- more rearrangement done in the fourth term for the cancellation
  rw [mul_assoc (((p₁.eval y : ℤ) : ZMod (p^(2*α))) * ((p₀.eval y : ℤ) : ZMod (p^(2*α)))⁻¹)]
  rw [← mul_assoc ((((Polynomial.derivative (R := ℤ)) p₀).eval y : ℤ) : ZMod (p^(2*α)))]
  simp only [cast_mul]
  simp only [ZMod.int_cast_cast] 
  simp only [Nat.cast_pow, cast_pow, cast_ofNat]
  rw [← Nat.cast_pow] -- take the arrow out of the brackets

  /- rearranging the second term on the lhs to match it with the third term on the rhs -/
  rw [mul_assoc]

  /- rearranging ↑(p ^ α) to merge them together to have ↑(p ^ (2*α)) which will be zero -/
  rw [mul_assoc (((((Polynomial.derivative (R := ℤ)) p₁).eval y : ℤ) : ZMod (p^(2*α))) * ((p₀.eval y : ℤ) : ZMod (p^(2*α)))⁻¹ - (((p₀.eval y : ℤ) : ZMod (p^(2*α)))⁻¹) ^ 2 * (((((Polynomial.derivative (R := ℤ)) p₀).eval y : ℤ) : ZMod (p^(2*α))) * ((p₁.eval y : ℤ) : ZMod (p^(2*α)))))]
  -- rw [mul_assoc (((p₀.eval y : ℤ) : ZMod (p^(2*α)))⁻¹) ^ 2 * (((Polynomial.derivative (R := ℤ)) p₀).eval y : ZMod (p^(2*α))) * (p₁.eval y : ZMod (p^(2*α)))]
  rw [mul_assoc ((((Polynomial.derivative (R := ℤ)) p₀).eval y : ℤ) : ZMod (p^(2*α)))]
  rw [mul_comm (z : ZMod (p^(2*α)))]
  rw [mul_assoc (p^α : ZMod (p^(2*α)))]
  rw [mul_comm ((((Polynomial.derivative (R := ℤ)) p₀).eval y : ℤ) : ZMod (p^(2*α)))]
  repeat rw [← mul_assoc (z : ZMod (p^(2*α)))]
  rw [mul_comm (z : ZMod (p^(2*α)))]
  rw [← mul_assoc (p^α : ZMod (p^(2*α)))]
  rw [mul_assoc (p^α : ZMod (p^(2*α))) (z : ZMod (p^(2*α))) (z : ZMod (p^(2*α)))]
  rw [← mul_assoc (p^α : ZMod (p^(2*α)))]
  rw [← pow_two]
  push_cast
  rw [← pow_mul]
  rw [mul_comm α 2]
  norm_cast
  rw [ZMod.nat_cast_self]
  ring

/- necessary for the theorem inv_cancel -/
lemma rationalFunc_unit (x y : ℤ) (f₁_at_xIsUnit : IsUnit ((f₁.eval x : ℤ) : ZMod (p^(2*α)))) (f₀_at_xIsUnit : IsUnit ((f₀.eval x : ℤ) : ZMod (p^(2*α)))) :
    IsUnit (rationalFunc (f₁) (f₀) (x) (p^(2*α)) : ZMod (p^(2*α))) := by
  simp only [rationalFunc]
  apply IsUnit.mul
  · exact f₁_at_xIsUnit
  · rw [isUnit_iff_exists_inv]
    use ((f₀.eval x : ℤ) : ZMod (p^(2*α)))
    exact ZMod.inv_mul_of_unit ((f₀.eval x : ℤ) : ZMod (p^(2*α))) f₀_at_xIsUnit

/- note to myself
Figure out when and how to state the assumption rationalFunc_isunit at the start of this document
-/ 
lemma rationalFunc_inv_cancel (y : ℤ) (rationalFunc_isunit : IsUnit (rationalFunc (f₁) (f₀) (y) (p^(2*α)) : ZMod (p^(2*α)))):
    (rationalFunc f₁ f₀ y (p^(2*α)) : ZMod (p^(2*α))) * (rationalFunc (f₁) (f₀) (y) (p^(2*α)) : ZMod (p^(2*α)))⁻¹ = 1 := by
  exact ZMod.mul_inv_of_unit (rationalFunc f₁ f₀ y (p ^ (2 * α))) rationalFunc_isunit

lemma MulChar_in_y_and_z (x y : ℤ) (h : x = y + z * (p^α : ℕ)) (f₀_at_xIsUnit : IsUnit ((f₀.eval x : ℤ) : ZMod (p^(2*α)))) (rationalFunc_at_y_isunit : IsUnit (rationalFunc (f₁) (f₀) (y) (p^(2*α)) : ZMod (p^(2*α)))) 
    (H₁ : (taylor y f₁).support.Nonempty) (H₀ : (taylor y f₀).support.Nonempty) (support_le_H₁ : (taylor y f₁).support.max' H₁ > 0) (support_le_H₀ : (taylor y f₀).support.max' H₀ > 0) (hα : 0 < α) :
    χ (rationalFunc (f₁) (f₀) (x) (p^(2*α))) = χ (rationalFunc (f₁) (f₀) (y) (p^(2*α))) 
    * χ (1 + (rationalFunc_deriv (f₁) (f₀) (y) (p^(2*α))) * (rationalFunc (f₁) (f₀) (y) (p^(2*α)) : ZMod (p^(2*α)))⁻¹ * z * (p^α : ℕ)) := by
  -- have h := rationalFunc_eq_ZMod z f₁ f₀ x y h
  -- rw [h]
  rw [← map_mul]
  rw [mul_add]
  rw [mul_assoc]
  /- ) moves from the end of the equation to the end of the (rationalFunc f₁ f₀ y (p ^ (2 * α)))⁻¹ -/
  rw [← mul_assoc (rationalFunc (f₁) (f₀) (y) (p^(2*α))) (rationalFunc_deriv (f₁) (f₀) (y) (p^(2*α)) * (rationalFunc (f₁) (f₀) (y) (p^(2*α)) : ZMod (p^(2*α)))⁻¹) (z * (p^α : ℕ))]
  rw [← mul_assoc (rationalFunc (f₁) (f₀) (y) (p^(2*α))) (rationalFunc_deriv (f₁) (f₀) (y) (p^(2*α))) ((rationalFunc (f₁) (f₀) (y) (p^(2*α)) : ZMod (p^(2*α)))⁻¹)]
  rw [mul_comm (rationalFunc (f₁) (f₀) (y) (p^(2*α))) (rationalFunc_deriv (f₁) (f₀) (y) (p^(2*α)))]
  rw [mul_assoc (rationalFunc_deriv (f₁) (f₀) (y) (p^(2*α))) (rationalFunc (f₁) (f₀) (y) (p^(2*α))) (rationalFunc (f₁) (f₀) (y) (p^(2*α)) : ZMod (p^(2*α)))⁻¹]
  rw [rationalFunc_inv_cancel (p := p) (α := α) f₁ f₀ y rationalFunc_at_y_isunit]
  rw [rationalFunc_eq_ZMod z hp f₁ f₀ x y H₁ H₀ support_le_H₁ support_le_H₀ h f₀_at_xIsUnit hα]
  ring

theorem MulChar_eq_exp :
    ∃(b : ℕ), b < p^α ∧ ∀(x y : ℤ) (z : ZMod (p^α : ℕ)), χ' (χ) ((rationalFunc_deriv (f₁) (f₀) (y) (p^(2*α))) * (rationalFunc (f₁) (f₀) (x) (p^(2*α)) : ZMod (p^(2*α)))⁻¹ * z) 
    = eZMod (p^α : ℕ) (b * ((rationalFunc_deriv (f₁) (f₀) (y) (p^(2*α))) * (rationalFunc (f₁) (f₀) (x) (p^(2*α)) : ZMod (p^(2*α)))⁻¹ * z)) := by
  have : NeZero (p^α) := ⟨pow_ne_zero α <| Prime.ne_zero hp⟩
  have newExpression : ∃(ζ : ℂˣ), (ζ : ℂˣ) = (χ' (χ) (1) : ℂ)
  { have H := MulChar_one_Unit χ
    rw [IsUnit] at H
    exact H }
  have primepow_pos : ∃(q : ℕ+), q = p^α
  { apply CanLift.prf (p^α)
    exact Fin.size_positive' }
  cases' newExpression with ζ hζ
  cases' primepow_pos with q hq
  -- why do both ζ and q : ?m.1264417
  have ofunity : ζ ∈ rootsOfUnity q ℂ ↔ ((ζ : ℂˣ) : ℂ) ^ ((q : ℕ+) : ℕ) = 1 := by
    simp only [mem_rootsOfUnity']
    -- simp [Units.ext_iff] -- fixed after the bug in power notation in mathlib was found
  have root : ζ ∈ rootsOfUnity q ℂ
  { rw [ofunity, hζ, hq, MulChar_additive_pow, ZMod.nat_cast_self, mul_one]
    exact MulChar_zero χ  }
  rw [Complex.mem_rootsOfUnity, hq, hζ] at root
  have pow (n : ℕ) {a : ℂ} {b : ℂ} : a = b → a^n = b^n
  { intro h
    norm_cast
    exact congrFun (congrArg HPow.hPow h) n }
  cases' root with b hb
  refine' ⟨b, hb.left, _⟩
  intro x y z
  set c := (((rationalFunc_deriv (f₁) (f₀) (y) (p^(2*α))) * (rationalFunc (f₁) (f₀) (x) (p^(2*α)) : ZMod (p^(2*α)))⁻¹ : ZMod (p ^ α)) * z)
  rw [← MulChar_additive_pow_val]
  have hb_pow := pow c.val (hb.right)
  norm_cast at hb_pow
  rw [← Complex.exp_nat_mul] at hb_pow
  simp only [eZMod]

  have congr_val : ((b : ZMod (p^α : ℕ)) * c).val ≡ (b : ZMod (p^α)).val * c.val [ZMOD (p^α)]
  { rw [ZMod.val_mul (↑b) c]
    exact Int.mod_modEq ((b : ZMod (p^α)).val * ZMod.val c) (p ^ α) }

  have new_NeZero : p^α ≠ 0 := by exact NeZero.ne (p^α)
  have val_b : (b : ZMod (p^α)).val ≡ b [ZMOD (p^α)]
  { simp only [Nat.cast_pow, ZMod.nat_cast_val]
    norm_cast
    rw [← ZMod.int_cast_eq_int_cast_iff]
    simp  }
  rw [cexp_congr_eq (p^α : ℕ) (((b : ZMod (p^α : ℕ)) * c).val) ((b : ZMod (p^α)).val * c.val)]
  · have congr_b : (b : ZMod (p^α)).val * c.val ≡ b * c.val [ZMOD (p^α)] := by gcongr
    -- simp at congr_b ⊢
    rw [cexp_congr_eq (p^α : ℕ) ((b : ZMod (p^α)).val * c.val) (b * c.val)]
    · push_cast at hb_pow ⊢
      norm_cast
      symm at hb_pow
      rw [hb_pow]
      push_cast
      ring
    · exact congr_b
    · exact new_NeZero
  · exact congr_val
  · exact new_NeZero
  done

/- the natural number b whose existence is guaranteed by MulChar_eq_exp -/
def MulChar_eq_exp_b : ℕ := (MulChar_eq_exp χ hp f₁ f₀).choose

variable (x y : ℤ)

lemma MulChar_eq_exp_b_WellDefined : (MulChar_eq_exp χ hp f₁ f₀).choose = MulChar_eq_exp_b χ hp f₁ f₀ := rfl

theorem MulChar_eq_exp_b_spec :
   (MulChar_eq_exp_b χ hp f₁ f₀) < p^α ∧ ∀(x y : ℤ) (z : ZMod (p^α : ℕ)), χ' (χ) ((rationalFunc_deriv (f₁) (f₀) (y) (p^(2*α))) * (rationalFunc (f₁) (f₀) (x) (p^(2*α)) : ZMod (p^(2*α)))⁻¹ * z) 
    = eZMod (p^α : ℕ) ((MulChar_eq_exp_b χ hp f₁ f₀) * ((rationalFunc_deriv (f₁) (f₀) (y) (p^(2*α))) * (rationalFunc (f₁) (f₀) (x) (p^(2*α)) : ZMod (p^(2*α)))⁻¹ * z)) :=
  (MulChar_eq_exp χ hp f₁ f₀).choose_spec

open AddChar

lemma AddChar_in_y_and_z (x y : ℤ) (h : x = y + z * (p^α : ℕ)) (g₀_at_xIsUnit : IsUnit ((g₀.eval x : ℤ) : ZMod (p^(2*α)))) (H₁ : (taylor y g₁).support.Nonempty) (H₀ : (taylor y g₀).support.Nonempty) 
  (support_le_H₁ : (taylor y g₁).support.max' H₁ > 0) (support_le_H₀ : (taylor y g₀).support.max' H₀ > 0) (hα : 0 < α) :
    ψ (rationalFunc (g₁) (g₀) (x) (p^(2*α))) = ψ (rationalFunc (g₁) (g₀) (y) (p^(2*α))) * ψ ((rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z * (p^α : ℕ)) := by
  rw [rationalFunc_eq_ZMod z hp g₁ g₀ x y H₁ H₀ support_le_H₁ support_le_H₀ h g₀_at_xIsUnit hα]
  simp

lemma AddChar_one_pow (z₀ : ZMod (p^(2*α))) : (ψ 1)^z₀.val = ψ z₀ := by
  rw [← mulShift_spec' ψ z₀.val 1, mulShift_apply]
  simp only [ZMod.nat_cast_val, ZMod.cast_id', id_eq, mul_one]

lemma AddChar_isUnit : IsUnit (ψ 1) := by
  apply Ne.isUnit
  by_contra hψ
  have hψ_pow := complex_pow (p^(2*α)) (ψ 1) (0) hψ
  rw [← mulShift_spec'] at hψ_pow
  rw [mulShift_apply] at hψ_pow
  simp only [CharP.cast_eq_zero, mul_one, map_zero_one, ne_eq, CanonicallyOrderedCommSemiring.mul_pos, true_and] at hψ_pow 
  -- zero_pow'
  have pPow_ne_zero : p^(2*α) ≠ 0 := by exact NeZero.ne (p ^ (2 * α))
  rw [zero_pow' (p^(2*α)) pPow_ne_zero] at hψ_pow
  aesop
  -- tauto

/- previous version (weaker version without `(z₀ : ZMod (p^(2*α)))`)
-- Complex.mem_rootsOfUnity
/- very similar to the proof for the theorem `MulChar_additive_eq_exp` in the document lemma_char_v4.lean -/
theorem AddChar_eq_exp (z₀ : ZMod (p^(2*α))) :
    ∃(a : ℕ), a < p^(2*α) ∧ ψ z₀ = eZMod (p^(2*α)) (a * z₀) := by
  have : NeZero (p^(2*α)) := ⟨pow_ne_zero (2*α) <| Prime.ne_zero hp⟩ -- delete this later because we have the lemma
  -- rw [← mul_one z₀]
  have AddChar_one_pow : (ψ 1)^z₀.val = ψ z₀
  { rw [← mulShift_spec' ψ z₀.val 1, mulShift_apply]
    simp only [ZMod.nat_cast_val, ZMod.cast_id', id_eq, mul_one]  }
  rw [← AddChar_one_pow]
  have newExpression : ∃(ζ : ℂˣ), (ζ : ℂˣ) = (ψ 1 : ℂ)
  { have H := AddChar_isUnit ψ 
    rw [IsUnit] at H
    exact H }
  have primepow_pos : ∃(q : ℕ+), q = p^(2*α)
  { apply CanLift.prf (p^(2*α))
    exact Fin.size_positive' }
  cases' newExpression with ζ hζ
  cases' primepow_pos with q hq
  have ofunity : ζ ∈ rootsOfUnity q ℂ ↔ ((ζ : ℂˣ) : ℂ) ^ ((q : ℕ+) : ℕ) = 1 := by
    simp only [mem_rootsOfUnity']
  have root : ζ ∈ rootsOfUnity q ℂ
  { rw [ofunity, hζ, hq, ← mulShift_spec' ψ (p^(2 * α)) 1, ZMod.nat_cast_self, mulShift_zero, one_apply]  }
  rw [Complex.mem_rootsOfUnity, hq, hζ] at root
  cases' root with a ha
  have ha_pow := complex_pow (z₀.val) (exp (2 * ↑Real.pi * I * (↑a / ↑(p ^ (2 * α))))) (ψ 1) (ha.right)
  norm_cast at ha_pow
  rw [← Complex.exp_nat_mul] at ha_pow

  simp only [eZMod]
  use a
  apply And.intro
  exact ha.left
  have congr_val : ((a : ZMod (p^(2*α) : ℕ)) * z₀).val ≡ (a : ZMod (p^(2*α))).val * z₀.val [ZMOD (p^(2*α))]
  { rw [ZMod.val_mul (↑a) z₀]
    exact Int.mod_modEq ((a : ZMod (p^(2*α))).val * ZMod.val z₀) (p ^ (2*α)) }

  -- follows from the theorem `NeZero_pPow`
  have new_NeZero : p^(2*α) ≠ 0 := by exact NeZero.ne (p^(2*α))
  have val_a : (a : ZMod (p^(2*α))).val ≡ a [ZMOD (p^(2*α))]
  { simp only [Nat.cast_pow, ZMod.nat_cast_val]
    norm_cast
    rw [← ZMod.int_cast_eq_int_cast_iff]
    simp  }
  rw [cexp_congr_eq (p^(2*α) : ℕ) (((a : ZMod (p^(2*α) : ℕ)) * z₀).val) ((a : ZMod (p^(2*α))).val * z₀.val)]
  · have congr_a : (a : ZMod (p^(2*α))).val * z₀.val ≡ a * z₀.val [ZMOD (p^(2*α))] := by gcongr
    -- simp at congr_b ⊢
    rw [cexp_congr_eq (p^(2*α) : ℕ) ((a : ZMod (p^(2*α))).val * z₀.val) (a * z₀.val)]
    · push_cast at ha_pow ⊢
      norm_cast
      symm at ha_pow
      rw [ha_pow]
      push_cast
      ring
    · exact congr_a
    · exact new_NeZero
  · exact congr_val
  · exact new_NeZero
  done
 -/

/- the new version we need for `choose_spec` later -/
/- very similar to the proof for the theorem `MulChar_additive_eq_exp` in the document lemma_char_v4.lean -/

-- ψ ((rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z * (p^α : ℕ))

theorem AddChar_eq_exp :
    ∃(a : ℕ), a < p^(2*α) ∧ ∀(y : ℤ) (z : ZMod (p^(2*α))), ψ ((rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z * (p^α : ℕ)) = eZMod (p^(2*α)) (a * ((rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z * (p^α : ℕ))) := by
  have : NeZero (p^(2*α)) := ⟨pow_ne_zero (2*α) <| Prime.ne_zero hp⟩ -- delete this later because we have the lemma
  -- rw [← mul_one z₀]
  have newExpression : ∃(ζ : ℂˣ), (ζ : ℂˣ) = (ψ 1 : ℂ)
  { have H := AddChar_isUnit ψ 
    rw [IsUnit] at H
    exact H }
  have primepow_pos : ∃(q : ℕ+), q = p^(2*α)
  { apply CanLift.prf (p^(2*α))
    exact Fin.size_positive' }
  cases' newExpression with ζ hζ
  cases' primepow_pos with q hq

  have ofunity : ζ ∈ rootsOfUnity q ℂ ↔ ((ζ : ℂˣ) : ℂ) ^ ((q : ℕ+) : ℕ) = 1 := by
    simp only [mem_rootsOfUnity']
  have root : ζ ∈ rootsOfUnity q ℂ
  { rw [ofunity, hζ, hq, ← mulShift_spec' ψ (p^(2 * α)) 1, ZMod.nat_cast_self, mulShift_zero, one_apply]  }
  rw [Complex.mem_rootsOfUnity, hq, hζ] at root
  rcases root with ⟨a, ha, hexp⟩
  refine' ⟨a, ha, _⟩
  intro y z
  set c := ((rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z * (p^α : ℕ))
  have AddChar_one_pow : (ψ 1)^c.val = ψ c
  { rw [← mulShift_spec' ψ c.val 1, mulShift_apply]
    simp only [ZMod.nat_cast_val, ZMod.cast_id', id_eq, mul_one]  }
  rw [← AddChar_one_pow]
  
  have ha_pow := complex_pow (c.val) (exp (2 * ↑Real.pi * I * (↑a / ↑(p ^ (2 * α))))) (ψ 1) hexp
  norm_cast at ha_pow
  rw [← Complex.exp_nat_mul] at ha_pow

  simp only [eZMod]
  have congr_val : ((a : ZMod (p^(2*α) : ℕ)) * c).val ≡ (a : ZMod (p^(2*α))).val * c.val [ZMOD (p^(2*α))]
  { rw [ZMod.val_mul (↑a) c]
    exact Int.mod_modEq ((a : ZMod (p^(2*α))).val * ZMod.val c) (p ^ (2*α)) }

  -- follows from the theorem `NeZero_pPow`
  have new_NeZero : p^(2*α) ≠ 0 := by exact NeZero.ne (p^(2*α))
  have val_a : (a : ZMod (p^(2*α))).val ≡ a [ZMOD (p^(2*α))]
  { simp only [Nat.cast_pow, ZMod.nat_cast_val]
    norm_cast
    rw [← ZMod.int_cast_eq_int_cast_iff]
    simp  }
  rw [cexp_congr_eq (p^(2*α) : ℕ) (((a : ZMod (p^(2*α) : ℕ)) * c).val) ((a : ZMod (p^(2*α))).val * c.val)]
  · have congr_a : (a : ZMod (p^(2*α))).val * c.val ≡ a * c.val [ZMOD (p^(2*α))] := by gcongr
    -- simp at congr_b ⊢
    rw [cexp_congr_eq (p^(2*α) : ℕ) ((a : ZMod (p^(2*α))).val * c.val) (a * c.val)]
    · push_cast at ha_pow ⊢
      norm_cast
      symm at ha_pow
      nth_rw 1 [Nat.cast_pow]
      rw [ha_pow]
      push_cast
      ring
    · exact congr_a
    · exact new_NeZero
  · exact congr_val
  · exact new_NeZero
  done

/-
# later on we need this lemma complex_natural
lemma complex_natural (n₁ n₂: ℕ): ((n₁ * n₂ : ℕ) : ℂ) = (n₁ : ℂ) * (n₂ : ℂ) := by
  exact Nat.cast_mul n₁ n₂

later incoporate this in this the theorem hh' : `(p ^ α : ℂ) / (p ^ (2 * α) : ℂ) = 1 / (p ^ α : ℂ)`
but remember to use it as the theorem `Nat.cast_mul n₁ n₂`
-/

-- erase the assumption `h` and derive from the existing assumption
lemma foo' (h : (p^(2*α) : ℂ) ≠ 0): ∃(m : ℤ), (((p ^ α : ZMod (p ^ (2 * α))).val) : ℂ) / (p ^ (2 * α) : ℂ) = 1 / (p ^ α : ℂ) + m := by
  have H : ∃(m : ℤ), ((p ^ α : ZMod (p ^ (2 * α))).val : ℂ) = (p^α : ℕ) + m * (p ^ (2 * α) : ℕ) := by
    exact complex_eq_congr (p ^ (2*α)) (p ^ α : ZMod (p ^ (2 * α))).val (p ^ α) (nat_val_congr_self (p ^ α) (p ^ (2 * α)))
  cases' H with m Hm
  rw [Hm]
  use m
  simp only [ZMod.nat_cast_val]
  -- later on incorporate into the proof seamlessly without the `have` tactic
  have hh' : (p ^ α : ℂ) / (p ^ (2 * α) : ℂ) = 1 / (p ^ α : ℂ) := by
    rw [mul_comm, pow_mul, Nat.pow_two (p^α), Nat.cast_mul, Nat.cast_pow, div_self_mul_self', one_div]
  rw [add_div, hh', ← mul_div, div_self h, Nat.cast_pow, one_div, mul_one]
  
lemma valZModLarger_eq_ZModSmaller {a b : ℕ} (h : b ≤ a) [NeZero b] (n : ZMod b) : 
    (n : ZMod a).val = n.val := by
  rw [ZMod.cast_eq_val]
  rw [ZMod.val_cast_of_lt]
  suffices n.val < b by
    exact Nat.lt_of_lt_of_le this h
  exact ZMod.val_lt n

-- probably the assumption `(hα : α > 0)` will need to go on the top later
lemma pPow_lt_pTwoPow (hα : α > 0) : p^α < p^(2*α) := by
  apply pow_lt_pow
  rw [← Nat.prime_iff] at hp
  · exact Nat.Prime.one_lt hp
  · exact lt_two_mul_self hα

lemma dvd_pow_two : p^α ∣ p^(2*α) := ⟨p^α, by ring⟩

/- You're gonna have some headache reviewing the below proof -/
theorem AddChar_rationalFunc_deriv_eq_exp (hα : 0 < α) :
    ∃(a : ℕ), a < p^(2*α) ∧ ∀(y : ℤ) (z : ZMod (p ^ α)), ψ ((rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z * (p^α : ℕ)) = eZMod (p^α : ℕ) (a * ((rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z)) := by
  -- ∃(a : ℕ), a < p^(2*α) ∧ ψ z₀ = eZMod (p^(2*α)) (a * z₀) := by
  have eq_exp := AddChar_eq_exp ψ hp g₁ g₀
  simp only [eZMod] at *
  -- simp only [Nat.cast_pow, ZMod.nat_cast_val] at eq_exp 
  rcases eq_exp with ⟨a, ha, eq_exp⟩
  refine' ⟨a, ha, _⟩
  intro y z
  rw [eq_exp]
  rw [← mul_assoc (a : ZMod (p ^ (2 * α)))]
  rw [← mul_assoc (a : ZMod (p ^ (2 * α)))]
  have ha_lt := ZMod.val_lt ((a : ZMod (p ^ (2 * α))) * rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α)) * (z : ZMod (p ^ (2 * α))) * (p ^ α : ZMod (p ^ (2 * α))))
  have ha_modEq : ((a : ZMod (p ^ (2 * α))) * rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α)) * z * (p ^ α : ℕ)).val ≡ ((a : ZMod (p ^ (2 * α))) * (rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z).val * (p ^ α : ℕ) [MOD (p ^ (2 * α))]
  { rw [ZMod.val_mul]
    rw [ZMod.val_cast_of_lt (pPow_lt_pTwoPow hp hα)]
    exact Nat.mod_modEq (((a : ZMod (p ^ (2 * α))) * rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α)) * z).val * (p ^ α : ℕ)) (p ^ (2 * α)) }
  have exists_ha_modEq := exists_eq_of_nat_coe_mod_eq ((a : ZMod (p ^ (2 * α))) * rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α)) * z * (p ^ α : ℕ)).val (((a : ZMod (p ^ (2 * α))) * (rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z).val * (p ^ α : ℕ)) (p ^ (2 * α)) ha_lt ha_modEq
  cases' exists_ha_modEq with n exists_ha_modEq 
  -- for `Nat.sub_eq_iff_eq_ad` and `Nat.cast_sub`
  have diff_lt_zmod : n * (p ^ (2 * α)) ≤ ((a : ZMod (p ^ (2 * α))) * (rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z).val * (p ^ α : ℕ)
  { -- have := Nat.zero_le ((a : ZMod (p ^ (2 * α))) * rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α)) * z * (p ^ α : ℕ)).val
    rw [exists_ha_modEq]
    exact Nat.le_add_left (n * (p ^ (2 * α))) ((a : ZMod (p ^ (2 * α))) * rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α)) * z * (p ^ α : ℕ)).val }
  rw [← Nat.sub_eq_iff_eq_add diff_lt_zmod] at exists_ha_modEq
  rw [← exists_ha_modEq]
  /- attempt to get rid of the term `n * p ^ (2 * α)` in the exp -/
  rw [Nat.cast_sub diff_lt_zmod]
  rw [mul_div_assoc]
  rw [Nat.cast_mul]
  rw [Nat.cast_mul]
  rw [sub_div]
  rw [mul_div_assoc]
  rw [mul_div_assoc]
  rw [div_self (NeZero.natCast_ne (p ^ (2 * α)) ℂ)]
  simp_rw [mul_comm 2 α]
  simp_rw [pow_mul] -- why does it behave differently from `rw`? 
  rw [pow_two]
  rw [Nat.cast_mul]
  rw [div_mul_right (p ^ α : ℂ) (NeZero.natCast_ne (p ^ α) ℂ)]
  rw [mul_sub]
  rw [exp_sub]
  rw [mul_one]
  rw [mul_comm (2 * Real.pi * I) (n : ℂ)]
  rw [← cast_ofNat n]
  rw [exp_int_mul_two_pi_mul_I n]
  rw [div_one]
  -- got rid of the term
  -- show the congruence of the 
  have zmod_mod_zmod :  (((a : ZMod (p ^ α)) * (rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α)) : ZMod (p ^ α))) * z).val ≡ ((a : ZMod (p ^ (2 * α))) * (rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z).val [MOD (p ^ α)]
  { rw [mul_assoc]
    have hc₁_lhs := congr_val (p ^ α) (a : ZMod (p ^ α)) (((rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α)) : ZMod (p ^ α))) * z)
    have hc₂_lhs := congr_val (p ^ α) ((rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α)) : ZMod (p ^ α))) z
    have hc₂_lhs_mul := Nat.ModEq.mul_left (a : ZMod (p ^ α)).val hc₂_lhs
    have hc₁_rhs := congr_val (p ^ (2 * α)) (a : ZMod (p ^ (2 * α))) (rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α)) * (z : ZMod (p ^ (2 * α))))
    have hc₂_rhs := congr_val (p ^ (2 * α)) (rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) (z : ZMod (p ^ (2 * α)))
    have hc₂_rhs_mul := Nat.ModEq.mul_left (a : ZMod (p ^ (2 * α))).val hc₂_rhs
    have hc₁_rhs_dvd := Nat.ModEq.of_dvd dvd_pow_two hc₁_rhs
    rw [← mul_assoc] at hc₁_rhs_dvd
    have hc₂_rhs_dvd := Nat.ModEq.of_dvd dvd_pow_two hc₂_rhs_mul
    apply Nat.ModEq.trans hc₁_lhs _
    apply Nat.ModEq.trans hc₂_lhs_mul _
    apply Nat.ModEq.trans _ (Nat.ModEq.symm (hc₁_rhs_dvd)) -- don't forget `Nat.`
    apply Nat.ModEq.trans _ (Nat.ModEq.symm (hc₂_rhs_dvd))
    repeat' apply Nat.ModEq.mul -- is this the best way to split the goal into 3?
    · rw [← ZMod.eq_iff_modEq_nat]
      simp only [ZMod.nat_cast_val, ZMod.cast_nat_cast']
      rw [ZMod.cast_nat_cast dvd_pow_two a]
    · rw [← ZMod.eq_iff_modEq_nat]
      simp only [ZMod.nat_cast_val, ZMod.cast_nat_cast']
      exact ZMod.cast_id (p ^ α) ↑(rationalFunc_deriv g₁ g₀ y (p ^ (2 * α))) 
    · rw [← ZMod.eq_iff_modEq_nat]
      -- rw [← ZMod.nat_cast_val]
      -- rw [ZMod.val_nat_cast]
      rw [valZModLarger_eq_ZModSmaller (le_of_lt (pPow_lt_pTwoPow hp hα))] }
  have zmod_val_lt : (((a : ZMod (p ^ α)) * (rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α)) : ZMod (p ^ α))) * z).val < p ^ α  := by 
    exact ZMod.val_lt (((a : ZMod (p ^ α)) * (rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α)) : ZMod (p ^ α))) * z)
  have exists_zmod_mod_zmod := exists_eq_of_nat_coe_mod_eq (((a : ZMod (p ^ α)) * (rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α)) : ZMod (p ^ α))) * z).val ((a : ZMod (p ^ (2 * α))) * (rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z).val (p ^ α) zmod_val_lt zmod_mod_zmod
  cases' exists_zmod_mod_zmod with n exists_zmod_mod_zmod
  rw [exists_zmod_mod_zmod]
  rw [← mul_div_assoc]
  rw [mul_one]
  rw [Nat.cast_add]
  rw [Nat.cast_mul]
  rw [← div_add_div_same]
  rw [mul_div_assoc]
  rw [div_self (NeZero.natCast_ne (p ^ (α)) ℂ)]
  rw [mul_one]
  rw [mul_add]
  rw [exp_add]
  rw [mul_comm (2 * Real.pi * I) (n : ℂ)]
  rw [← cast_ofNat n]
  rw [exp_int_mul_two_pi_mul_I n]
  rw [mul_one]
  rw [← mul_assoc]
  rw [mul_div_assoc]

def AddChar_eq_exp_a : ℕ := (AddChar_rationalFunc_deriv_eq_exp ψ hp g₁ g₀ hα).choose

theorem AddChar_eq_exp_a_spec :
    (AddChar_eq_exp_a ψ hp g₁ g₀ hα) < p^(2*α) ∧ ∀(y : ℤ) (z : ZMod (p ^ α)), ψ ((rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z * (p^α : ℕ)) = eZMod (p^α : ℕ) ((AddChar_eq_exp_a ψ hp g₁ g₀ hα) * ((rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z)) :=
  (AddChar_rationalFunc_deriv_eq_exp ψ hp g₁ g₀ hα).choose_spec

/- # Final sentences of lemma 12.2: The Challenge -/

lemma ZModLarger_eq_ZModSmaller (a b : ℕ) (h : b ≤ a) [NeZero b] (n : ZMod b) : 
    ((n : ZMod a) : ZMod b) = n := by
  have : 0 < b := by exact Fin.size_positive' -- changed this bit from Kevin's code
  have : NeZero a := ⟨by linarith⟩
  rw [← ZMod.nat_cast_comp_val]
  rw [← ZMod.nat_cast_comp_val]
  dsimp
  rw [ZMod.val_cast_of_lt]
  · exact ZMod.nat_cast_zmod_val n
  · apply lt_of_lt_of_le ?_ h
    exact ZMod.val_lt n

def aux_fun (x : ZMod (p^(2*α))) : ZMod (p^α) := x.val / p^α

def val_mod (n : ℕ) [NeZero n] (x : ZMod n) : (x.val : ZMod n) = x := by
  exact ZMod.nat_cast_zmod_val x

/- we don't need this anymore for now; erase this later when completed -/
/- for the `right_inv` of def `UnitEquivUnitProdZMod` -/
lemma sub_lt_add_lt {a b c d : ℕ} (hac : a < c) (hbdc : b < d - c) (hdc : d > c) : 
    a + b < d := by 
  have hdc_le := Nat.le_of_lt hdc
  rw [← Nat.sub_add_cancel hdc_le]
  rw [add_comm (d-c) c]
  exact add_lt_add hac hbdc

lemma sub_lt_add_le {a b c d : ℕ} (hac : a < c) (hbdc : b ≤ d - c) (hdc : d > c) :
    a + b < d := by 
  have hdc_le := Nat.le_of_lt hdc
  rw [← Nat.sub_add_cancel hdc_le]
  rw [add_comm (d-c) c]
  exact add_lt_add_of_lt_of_le hac hbdc

-- Originally for WTF statement 
instance : (ZMod (p^(2*α))) = (ZMod (p^α * p^α)) := by
  rw [mul_comm]
  rw [pow_mul] -- infer_instance doesn't work
  rw [pow_two]

def UnitEquivUnitProdZMod (hα : 0 < α) : (ZMod (p^(2*α)))ˣ ≃ (ZMod (p^α))ˣ × ZMod (p^α) where
  toFun x := ⟨Units.map (ZMod.castHom dvd_pow_two _).toMonoidHom x, aux_fun x⟩
  invFun yz := ZMod.unitOfCoprime (yz.1.val.val + yz.2.val * p^α) <| by
    rw [← Nat.prime_iff] at hp
    cases' yz with y z; dsimp
    apply Nat.Prime.coprime_pow_of_not_dvd hp
    intro hp'
    rw [Nat.dvd_add_left] at hp'
    · have := ZMod.val_coe_unit_coprime y
      rw [Nat.Prime.dvd_iff_not_coprime (by assumption)] at hp'
      apply hp'
      apply Nat.coprime.coprime_dvd_left _ this.symm
      exact dvd_pow (dvd_refl p) hα.ne'
    · apply dvd_mul_of_dvd_right
      exact dvd_pow (dvd_refl p) hα.ne'
  left_inv := by
    intro x
    ext
    simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe, ZMod.castHom_apply, ZMod.coe_unitOfCoprime,
      Nat.cast_add, Nat.cast_mul, Nat.cast_pow, aux_fun]
    /- this part is my proof -/ -- eew
    rw [ZMod.val_cast_of_lt]
    · norm_cast
      rw [ZMod.cast_eq_val]
      rw [ZMod.val_nat_cast]
      suffices (x : ZMod (p^(2*α))).val % p ^ α + (x : ZMod (p^(2*α))).val / p ^ α * p ^ α = (x : ZMod (p^(2*α))).val by
        rw [this]
        exact val_mod (p ^ (2 * α)) ↑x
      exact Nat.mod_add_div' (x : ZMod (p^(2*α))).val (p ^ α)
    · rw [Nat.div_lt_iff_lt_mul]
      · rw [← pow_two]
        rw [← pow_mul]
        rw [mul_comm α 2]
        exact ZMod.val_lt (x : ZMod (p^(2*α)))
      · rw [← Nat.prime_iff] at hp
        exact Nat.pos_pow_of_pos α (Nat.Prime.pos hp)
  right_inv := by
    have hNatp := Iff.mpr Nat.prime_iff hp
    rintro ⟨y, z⟩
    have : NeZero (p^α : ℕ) := ⟨pow_ne_zero α <| Nat.Prime.ne_zero hNatp⟩
    ext <;> simp
    · convert mul_zero z -- changed this bit from Kevin's code
      norm_cast
      exact ZMod.nat_cast_self (p ^ α)
    · simp only [aux_fun]
      rw [ZMod.val_add] -- the calculation of evil coercion starts here
      rw [Nat.mod_eq_of_lt] 
      · rw [ZMod.val_mul] -- very similar to the proof I need to prove later on
        rw [Nat.mod_eq_of_lt]
        · norm_cast
          rw [ZMod.val_cast_of_lt, Nat.add_mul_div_right]
          · simp only [Nat.cast_add, ZMod.nat_cast_val]
            rw [Nat.div_eq_zero]
            · norm_cast
              rw [ZModLarger_eq_ZModSmaller]; simp
              exact Nat.le_of_lt (pPow_lt_pTwoPow hp hα)
              /- alternate proof before we stated the lemma `pPow_lt_pTwoPow`
              apply pow_le_pow
              linarith [Nat.Prime.pos hNatp]
              linarith
              -/
            · rw [valZModLarger_eq_ZModSmaller]
              exact ZMod.val_lt (y : ZMod (p^α))
              exact Nat.le_of_lt (pPow_lt_pTwoPow hp hα)
          · exact Fin.size_positive'
          · exact pPow_lt_pTwoPow hp hα
        · norm_cast
          rw [ZMod.val_cast_of_lt]
          · suffices : (z : ZMod (p^(2*α))).val < p ^ α
            · /- WTF this should work honestly -/
              have hpos := Nat.zero_lt_of_lt this
              rw [pow_mul']
              rw [pow_two]
              have foo : p ^ α * p ^ α = p ^ (2 * α) := by ring
              apply Nat.mul_lt_mul_of_pos_right ?_ hpos
              rw [foo]
              exact this
            · rw [valZModLarger_eq_ZModSmaller (Nat.le_of_lt (pPow_lt_pTwoPow hp hα))]
              exact ZMod.val_lt z
          · exact pPow_lt_pTwoPow hp hα
      · suffices (y : ZMod (p^(2*α))).val < p ^ α ∧ ((z : ZMod (p^(2*α))) * (p : ZMod (p^(2*α)))^α).val ≤ p ^ (2 * α) - 1 * p ^ α by
          rw [one_mul] at this
          exact sub_lt_add_le this.left this.right (pPow_lt_pTwoPow hp hα)
        constructor
        · rw [valZModLarger_eq_ZModSmaller (Nat.le_of_lt (pPow_lt_pTwoPow hp hα))]
          exact ZMod.val_lt (y : ZMod (p^α))
        · rw [ZMod.val_mul]
          rw [Nat.mod_eq_of_lt] -- becomes 2 goals after this point
          · norm_cast -- corollary of this result will prove the WTF part above 
            rw [ZMod.val_cast_of_lt (pPow_lt_pTwoPow hp hα)]
            rw [valZModLarger_eq_ZModSmaller (Nat.le_of_lt (pPow_lt_pTwoPow hp hα))]
            have hz_lt := ZMod.val_lt z
            have hz_le := Nat.le_pred_of_lt hz_lt
            rw [mul_comm 2 α]
            rw [pow_mul]
            rw [pow_two]
            rw [← Nat.mul_sub_right_distrib (p ^ α) 1 (p ^ α)]
            -- rw [← mul_one (- p^α)]
            -- rw [← Nat.mul_sub_right_distrib]
            -- rw [one_mul]
            exact Nat.mul_le_mul_right (p^α) hz_le 
          · norm_cast
            rw [ZMod.val_cast_of_lt (pPow_lt_pTwoPow hp hα)]
            -- equivalent statement to the WTF above
            -- this: ZMod.val ↑z < p ^ α
            rw [pow_mul']
            rw [pow_two]
            have foo : p ^ α * p ^ α = p ^ (2 * α) := by ring
            apply Nat.mul_lt_mul_of_pos_right 
            rw [foo]
            rw [valZModLarger_eq_ZModSmaller (Nat.le_of_lt (pPow_lt_pTwoPow hp hα))]
            · exact ZMod.val_lt z
            · exact Fin.size_positive'

lemma NeZeroForSmaller {a b : ℕ} (h : b ≤ a) [NeZero b] : NeZero a := by
  exact NeZero.of_gt (Nat.lt_of_lt_of_le (Fin.size_positive') h)

/- for the first goal of the goal case h for the theorem `sum_bijection` -/
lemma IntcoeZModLarger_eq_ZModSmaller (a b : ℕ) (h : b ≤ a) [NeZero b] (n : ZMod a) : 
    ((n : ZMod b) : ℤ) = (((n : ZMod b) : ZMod a) : ℤ) := by
  -- suffices : ((n : ZMod b) : ℤ) < b 
  suffices (n : ZMod b).val = ((n : ZMod b) : ZMod a).val by
    -- rw [ZMod.cast_eq_val]
    have NeZeroFora := NeZeroForSmaller h
    rw [← ZMod.nat_cast_val]
    rw [← ZMod.nat_cast_val ((n : ZMod b) : ZMod a)]
    rw [this]
  exact Eq.symm (valZModLarger_eq_ZModSmaller h ↑n)

lemma valZModLarger_eq_ZModSmaller' {a b : ℕ} (h : b ≤ a) [NeZero b] (n : ZMod b) : 
    (n : ZMod a).val = n.val := by
  rw [ZMod.cast_eq_val]
  rw [ZMod.val_cast_of_lt]
  suffices n.val < b by
    exact Nat.lt_of_lt_of_le this h
  exact ZMod.val_lt n

lemma ZMod_val_cast_mul {q : ℕ} (a b : ZMod q) [NeZero q] (h : a.val * b.val < q): 
    ((a * b : ZMod q).val) = (a.val * b.val) := by
  rw [ZMod.val_mul]
  exact Nat.mod_eq_of_lt h

/- for the second goal of the second goal from the theorem `sum_bijection` -/
lemma ZMod_int_cast_mul (q : ℕ) (a b : ZMod q) [NeZero q] (h : (a * b : ℤ) < q):
   ((a * b : ZMod q) : ℤ) = (a * b : ℤ) := by
  suffices ((a * b : ZMod q).val) = (a.val * b.val) by
    repeat rw [← ZMod.nat_cast_val]
    rw [this]
    rfl
  have hval : a.val * b.val < q
  { repeat rw [← ZMod.nat_cast_val] at h
    exact Iff.mp ofNat_lt h }
  exact ZMod_val_cast_mul a b hval

/- for the second goal of the second goal for the theorem `sum_bijection` -/
lemma NatcoeZModLarger_eq_ZModSmaller_to_val {a b n : ℕ} (h : b ≤ a) [NeZero b] : 
    ((n : ZMod b) : ZMod a).val = (n : ZMod b).val := by
  have NeZeroFora := NeZeroForSmaller h -- although shadowed, we need this variable (Note to kevin : wait until the letters change from blue to grey after you comment this line out)
  exact valZModLarger_eq_ZModSmaller' h ↑n

/- for the second goal of the second goal for the theorem `sum_bijection` -/
lemma NatcoeZModLarger_eq_ZModSmaller_to_Int (a b n : ℕ) (h : b ≤ a) [NeZero b] : 
    (((n : ZMod b) : ZMod a) : ℤ) = ((n : ZMod b) : ℤ) := by
  suffices ((n : ZMod b) : ZMod a).val = (n : ZMod b).val by
    have NeZeroFora := NeZeroForSmaller h
    rw [← ZMod.nat_cast_val ((n : ZMod b) : ZMod a)] 
    rw [this]
    rw [← ZMod.nat_cast_val (n : ZMod b)]
  exact NatcoeZModLarger_eq_ZModSmaller_to_val h
    
/- for the 2nd - 2nd goal of the theorem `sum_bijection` -/
lemma lt_nat_coe_zmod_coe_int_eq_coe_int (n q : ℕ) [NeZero q] (h : n < q) : ((n : ZMod q) : ℤ) = (n : ℤ) := by 
  rw [← ZMod.nat_cast_val (n : ZMod q)]
  nth_rw 2 [← ZMod.val_cast_of_lt h]

/- for the 2nd - 2nd - 2nd goal of the theorem `sum_bijection` -/
lemma zmod_coe_int_lt (q : ℕ) (n : ZMod q) [NeZero q] : (n : ℤ) < q := by 
  rw [← ZMod.nat_cast_val n]
  exact Iff.mpr ofNat_lt (ZMod.val_lt n)

/- originally for the last - 2nd goal of the theorem `sum_bijection`
useless, delete this later 
-/
lemma val_div_primePow_le [NeZero (p^α : ℕ)] (a : ZMod (p ^ (2 * α))) : a.val / p ^ α ≤ p ^ α - 1 := by
  apply Nat.lt_succ.mp
  rw [Nat.div_lt_iff_lt_mul Fin.size_positive']
  rw [Nat.succ_eq_add_one]
  rw [Nat.sub_add_cancel (Fin.size_positive')]
  rw [← pow_two]
  rw [← pow_mul]
  rw [mul_comm α 2]
  exact ZMod.val_lt a

-- it seems like sum_bijection_v1 is not applicable to the below theorems
-- later I need to rewrite the proof for the below theorem 
theorem sum_bijection_v2 (f₁ f₂ : ZMod (p^(2*α)) → ℂ) (g₁ g₂ : ℤ → ZMod (p^(2*α))) [NeZero (p^α : ℕ)] (hα : 0 < α) :
    ∑ x : (ZMod (p^(2*α)))ˣ, f₁ (g₁ x) * f₂ (g₂ x) = ∑ yz : (ZMod (p^α))ˣ × ZMod (p^α), f₁ (g₁ (yz.1 + yz.2 * (p^α : ℕ))) * f₂ (g₂ (yz.1 + yz.2 * (p^α : ℕ))) := by
  apply Finset.sum_bij' (fun i _ => (UnitEquivUnitProdZMod hp hα).toFun i) (j := fun j _ => (UnitEquivUnitProdZMod hp hα).invFun j) -- map `i` is toFun and map `j` must be invFun
  · intro a ha
    exact Finset.mem_univ ((fun i _ => Equiv.toFun (UnitEquivUnitProdZMod hp hα) i) a ha)
    -- (i := UnitEquivUnitProdZMod.toFun i) (j := UnitEquivUnitProdZMod.invFun j)
    -- refine fun a ha => ?_ a ha
  · intro a ha
    suffices (f : ZMod (p^(2*α)) → ℂ) (g : ℤ → ZMod (p^(2*α))) : 
    f (g ((a : ZMod (p^(2*α))) : ℤ)) = f (g (↑↑((fun i _ => Equiv.toFun (UnitEquivUnitProdZMod hp hα) i) a ha).fst 
    + ↑((fun i _ => Equiv.toFun (UnitEquivUnitProdZMod hp hα) i) a ha).snd * ↑(p ^ α)))
    { rw [this f₁ g₁, this f₂ g₂] }
    apply congr_arg
    apply congr_arg
    simp only [Equiv.toFun_as_coe_apply]
    -- I think I need Kevin's help: Read the following code later
    have := (UnitEquivUnitProdZMod hp hα).left_inv a
    unfold UnitEquivUnitProdZMod aux_fun at this ⊢
    simp [ZMod.unitOfCoprime] at this
    nth_rewrite 1 [← this]
    dsimp at this ⊢ 
    rw [ZMod.coe_add_eq_ite]
    rw [if_neg]
    simp
    norm_cast
    congr 1
    · rw [← IntcoeZModLarger_eq_ZModSmaller]
      exact Nat.le_of_lt (pPow_lt_pTwoPow hp hα)
      -- rw [ZModLarger_eq_ZModSmaller]
    · rw [ZMod_int_cast_mul]
      · rw [NatcoeZModLarger_eq_ZModSmaller_to_Int (h := Nat.le_of_lt (pPow_lt_pTwoPow hp hα))]
        -- rw [ZMod.coe_int_cast (p^α)]
        rw [lt_nat_coe_zmod_coe_int_eq_coe_int (p ^ α) (p ^ (2 * α)) (pPow_lt_pTwoPow hp hα)] 
      · rw [lt_nat_coe_zmod_coe_int_eq_coe_int (p ^ α) (p ^ (2 * α)) (pPow_lt_pTwoPow hp hα)]
        rw [NatcoeZModLarger_eq_ZModSmaller_to_Int (h := Nat.le_of_lt (pPow_lt_pTwoPow hp hα))]
        -- rw [mul_comm 2 α] -- why motive is not type correct
        conv => -- otherwise, gets the error : motive is not type correct
          rhs
          rw [mul_comm]
          rw [pow_mul]
          rw [pow_two]
          rw [Nat.cast_mul]
        rw [← Int.lt_ediv_iff_mul_lt (p ^ α : ℤ) (Iff.mpr ofNat_pos (Fin.size_positive' (n := (p ^ α)))) (Int.dvd_mul_left ↑(p ^ α) ↑(p ^ α))]
        rw [Int.mul_ediv_assoc' (p ^ α : ℤ) (Int.dvd_refl (p ^ α : ℤ))]
        rw [Int.ediv_self (NeZero.natCast_ne (p ^ α) ℤ)]
        rw [one_mul]
        exact zmod_coe_int_lt (p ^ α) ((a : ZMod (p ^ (2 * α))).val / p ^ α : ZMod (p ^ α))
    · contrapose!
      intro _
      rw [← IntcoeZModLarger_eq_ZModSmaller (h := Nat.le_of_lt (pPow_lt_pTwoPow hp hα))]
      norm_cast
      rw [ZMod_int_cast_mul]
      · rw [NatcoeZModLarger_eq_ZModSmaller_to_Int (h := Nat.le_of_lt (pPow_lt_pTwoPow hp hα))]
        rw [lt_nat_coe_zmod_coe_int_eq_coe_int (p ^ α) (p ^ (2 * α)) (pPow_lt_pTwoPow hp hα)] 
        have val_div_lt := zmod_coe_int_lt (p ^ α) ↑((a : ZMod (p ^ (2 * α))).val / p ^ α)
        have val_div_primePow_le : (((a : ZMod (p ^ (2 * α))).val / p ^ α : ZMod (p ^ α)) : ℤ) ≤ (p ^ α : ℕ) - 1 := by 
          exact Iff.mpr le_sub_one_iff val_div_lt
        rw [← mul_le_mul_right (a := (p ^ α : ℤ)) (Iff.mpr ofNat_pos Fin.size_positive')] at val_div_primePow_le
        rw [sub_mul, one_mul, ← Nat.cast_mul, ← pow_two, ← pow_mul, mul_comm α 2] at val_div_primePow_le
        conv =>
          rhs
          rw [eq_sub_of_add_eq' (a := (p ^ (2 * α) : ℤ)) (c := (p ^ α : ℤ)) rfl]
        rw [add_sub_assoc]
        have ha_pPow_lt := zmod_coe_int_lt (p ^ α) (a : ZMod ((p ^ α)))
        exact Int.add_lt_add_of_lt_of_le ha_pPow_lt val_div_primePow_le
      · rw [NatcoeZModLarger_eq_ZModSmaller_to_Int (h := Nat.le_of_lt (pPow_lt_pTwoPow hp hα))]
        rw [lt_nat_coe_zmod_coe_int_eq_coe_int (p ^ α) (p ^ (2 * α)) (pPow_lt_pTwoPow hp hα)] 
        conv => -- otherwise, gets the error : motive is not type correct
          rhs
          rw [mul_comm]
          rw [pow_mul]
          rw [pow_two]
          rw [Nat.cast_mul]
        rw [← Int.lt_ediv_iff_mul_lt (p ^ α : ℤ) (Iff.mpr ofNat_pos (Fin.size_positive' (n := (p ^ α)))) (Int.dvd_mul_left ↑(p ^ α) ↑(p ^ α))]
        rw [Int.mul_ediv_assoc' (p ^ α : ℤ) (Int.dvd_refl (p ^ α : ℤ))]
        rw [Int.ediv_self (NeZero.natCast_ne (p ^ α) ℤ)]
        rw [one_mul]
        exact zmod_coe_int_lt (p ^ α) ↑((a : ZMod (p ^ (2 * α))).val / p ^ α)
  · exact fun a _ => Finset.mem_univ (Equiv.invFun (UnitEquivUnitProdZMod hp hα) a)
  · intro a _
    exact (UnitEquivUnitProdZMod hp hα).left_inv a
  · intro a _
    exact (UnitEquivUnitProdZMod hp hα).right_inv a -- it worked!
  
/- # Version 2 -/
-- needs rewriting
-- a and b are from the characters ψ χ -- [MulChar_eq_exp] [AddChar_eq_exp]
-- should hFunc : ℤ or ZMod q
-- remember that we have the use the orthogonality property of char by setting hFunc ≡ 0 [ZMOD q]
def hFunc (r : ZMod (p^α)) (q : ℕ) (hp : Prime p) : ZMod (p ^ α) :=
  -- let ⟨b, hl, hr⟩ := MulChar_eq_exp (z) (χ) (f₁) (f₀) (x) (y) 
  (AddChar_eq_exp_a ψ hp g₁ g₀ hα) * (rationalFunc_deriv g₁ g₀ r q) + (MulChar_eq_exp_b χ hp f₁ f₀) * (rationalFunc_deriv f₁ f₀ r q) * (rationalFunc f₁ f₀ r q : ZMod q)⁻¹

-- (MulChar_eq_exp_b z χ hp f₁ f₀ x y)

/- set of all solutions to hFunc-/
-- x₀ : ℤ or ZMod p^α or (ZMod (p^α : ℕ))ˣ 
-- need to make it reply on the variables `a` and `b` from MulChar_eq_exp and AddChar_eq_exp
def sol_hFunc (r : (ZMod (p^α))ˣ) (q : ℕ) : Prop := 
  hFunc χ ψ f₁ f₀ g₁ g₀ hα r q hp = 0 

-- delete this later
def IntToZMod (q : ℕ) : ℕ → ZMod q :=
  fun r => (r : ZMod q)

def map_sol_hFunc_v2 : (ZMod (p^α))ˣ → Prop := 
  fun r => sol_hFunc χ ψ hp f₁ f₀ g₁ g₀ hα r (p^α)

/- lets lean prove `Fintype {r : (ZMod (p^α : ℕ))ˣ | sol_hFunc (z) (χ) (ψ) (f₁) (f₀) (g₁) (g₀) (x) (y) (r) (q) (h)}`-/
open Classical

theorem Sum_into_two_sums_v2 (f₁ f₂ : ZMod (p^(2*α)) → ℂ) (g₁ g₂ : ℤ → ZMod (p^(2*α))) [NeZero (p^α : ℕ)] (hα : 0 < α) :
    ∑ x : (ZMod (p^(2*α)))ˣ, f₁ (g₁ x) * f₂ (g₂ x) = ∑ y : ((ZMod (p^α))ˣ), ∑ z : (ZMod (p^α : ℕ)), f₁ (g₁ (y + z * (p^α : ℕ))) * f₂ (g₂ (y + z * (p^α : ℕ))) := by
  rw [sum_bijection_v2 hp f₁ f₂ g₁ g₂ hα]
  -- Finset.sum_product'
  rw [Finset.sum_finset_product]
  simp only [Finset.mem_univ, and_self, Prod.forall, forall_const]

/- for the lemma `MulChar_ZMod_twoPow_coe_onePow` -/
lemma le_of_add_eq (a b c : ℕ) (h : a = b + c) : c ≤ a := by 
  have h₁ : b + c ≤ a := by exact Nat.le_of_eq (id (Eq.symm h)) 
  have h₂ : c ≤ b + c := by exact Nat.le_add_left c b
  exact Nat.le_trans h₂ h₁
  
-- rewrite the proof to a nicer looking one
/- for the latter lemma -/
lemma MulChar_ZMod_twoPow_coe_onePow (p : ℕ) (hp : Prime p) (α : ℕ) (z : ZMod (p^(2*α) : ℕ)) (χ : MulChar (ZMod (p^(2*α) : ℕ)) ℂ) [NeZero (p^α)]:
    χ' (χ) (z : ZMod (p^α)) = χ (1 + z * (p^α : ℕ)) := by
  rw [well_defined]
  apply congr_arg
  rw [ZMod.cast_eq_val]
  rw [add_right_inj 1]
  have H : NeZero (p ^ (2 * α)) := by exact NeZero_pPow hp
  rw [ZMod.cast_eq_val]
  rw [ZMod.val_nat_cast]
  have val_remainder_lt : z.val % p ^ α < p ^ α
  { rw [← ZMod.val_nat_cast]
    exact ZMod.val_lt (ZMod.val z : ZMod (p ^ α)) }
  have val_remainder_mod : z.val % p ^ α ≡ z.val [MOD p ^ α] := by exact Nat.mod_modEq (ZMod.val z) (p ^ α)
  have exists_eq : ∃(c : ℕ), z.val = z.val % p ^ α + c * (p ^ α) := by exact exists_eq_of_nat_coe_mod_eq (z.val % p ^ α) (z.val) (p ^ α) val_remainder_lt val_remainder_mod
  cases' exists_eq with c hc
  have hc_le : c * p ^ α ≤ z.val := by exact le_of_add_eq (z.val) (z.val % p ^ α) (c * p ^ α) hc
  rw [← Nat.sub_eq_iff_eq_add hc_le] at hc
  rw [← hc]
  rw [Nat.cast_sub hc_le]
  rw [Nat.cast_mul]
  rw [sub_mul]
  rw [mul_assoc]
  rw [← Nat.cast_mul (p ^ α) (p ^ α)]
  rw [← pow_two]
  rw [← pow_mul]
  rw [mul_comm α 2]
  rw [ZMod.nat_cast_self]
  rw [mul_zero]
  rw [sub_zero]
  rw [ZMod.nat_cast_val]
  rw [ZMod.cast_id]

/- previous version -/
set_option maxHeartbeats 235000 in
lemma double_sum_in_deriv_and_exp [NeZero (p^α : ℕ)] (hα : 0 < α) (f₀_at_xIsUnit : ∀(x : ℤ), IsUnit ((f₀.eval x : ℤ) : ZMod (p^(2*α)))) (rationalFunc_at_y_isunit : ∀(y : ℤ), IsUnit (rationalFunc (f₁) (f₀) (y) (p^(2*α)) : ZMod (p^(2*α))))
    (H₁Forf₁ : ∀(y : ℤ), (taylor y f₁).support.Nonempty) (H₀Forf₀ : ∀(y : ℤ), (taylor y f₀).support.Nonempty) (support_le_H₁Forf₁ : ∀(y : ℤ), (taylor y f₁).support.max' (H₁Forf₁ y) > 0) (support_le_H₀Forf₀ : ∀(y : ℤ), (taylor y f₀).support.max' (H₀Forf₀ y) > 0) 
    (g₀_at_xIsUnit : ∀(y : ℤ), IsUnit ((g₀.eval y : ℤ) : ZMod (p^(2*α)))) (H₁Forg₁ : ∀(y : ℤ), (taylor y g₁).support.Nonempty) (H₀Forg₀ : ∀(y : ℤ), (taylor y g₀).support.Nonempty) (support_le_H₁Forg₁ : ∀(y : ℤ), (taylor y g₁).support.max' (H₁Forg₁ y) > 0) (support_le_H₀Forg₀ : ∀(y : ℤ), (taylor y g₀).support.max' (H₀Forg₀ y) > 0) :
  ∑ y : (ZMod (p ^ α))ˣ, ∑ z : ZMod (p ^ α), χ (rationalFunc f₁ f₀ (↑↑y + ↑z * ↑(p ^ α)) (p ^ (2 * α))) * ψ (rationalFunc g₁ g₀ (↑↑y + ↑z * ↑(p ^ α)) (p ^ (2 * α))) 
    = ∑ y : (ZMod (p ^ α))ˣ, ∑ z : ZMod (p ^ α), χ (rationalFunc f₁ f₀ y (p ^ (2 * α))) * eZMod (p^α : ℕ) ((MulChar_eq_exp_b χ hp f₁ f₀) * ((rationalFunc_deriv (f₁) (f₀) (y) (p^(2*α))) * (rationalFunc (f₁) (f₀) (y) (p^(2*α)) : ZMod (p^(2*α)))⁻¹ * z)) 
    * ψ (rationalFunc (g₁) (g₀) (y) (p^(2*α))) * eZMod (p^α : ℕ) ((AddChar_eq_exp_a ψ hp g₁ g₀ hα) * ((rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z)) := by
    apply congr_arg
    funext y
    apply congr_arg
    funext z
    -- if I let MulChar_in_y_and_z eat all of its variables, times out
    rw [MulChar_in_y_and_z z χ hp f₁ f₀ (((y : ZMod (p^α)) : ℤ) + (z : ℤ) * (p ^ α : ℤ)) ((y : ZMod (p^α)) : ℤ) rfl (f₀_at_xIsUnit (↑↑y + ↑z * ↑(p ^ α))) (rationalFunc_at_y_isunit ↑↑y)]
    · rw [AddChar_in_y_and_z z ψ hp g₁ g₀ (((y : ZMod (p^α)) : ℤ) + (z : ℤ) * (p ^ α : ℤ)) ((y : ZMod (p^α)) : ℤ) rfl (g₀_at_xIsUnit (↑↑y + ↑z * ↑(p ^ α)))]
      · rw [(AddChar_eq_exp_a_spec ψ hp g₁ g₀ hα).right]
        rw [← MulChar_ZMod_twoPow_coe_onePow p hp α (rationalFunc_deriv f₁ f₀ (↑↑y) (p ^ (2 * α)) * (rationalFunc f₁ f₀ (↑↑y) (p ^ (2 * α)))⁻¹ * (z : ZMod (p^(2*α)))) χ]
        rw [mul_assoc (rationalFunc_deriv f₁ f₀ (↑↑y) (p ^ (2 * α)))]
        repeat rw [ZMod.cast_mul (dvd_pow_two)]
        rw [ZModLarger_eq_ZModSmaller (h := (Nat.le_of_lt (pPow_lt_pTwoPow hp hα)))]
        rw [← mul_assoc (rationalFunc_deriv f₁ f₀ (↑↑y) (p ^ (2 * α)) : ZMod (p^α))]
        rw [(MulChar_eq_exp_b_spec χ hp f₁ f₀).right]
        rw [← mul_assoc]
      · exact H₁Forg₁ ↑↑y
      · exact H₀Forg₀ ↑↑y
      · exact support_le_H₁Forg₁ ↑↑y
      · exact support_le_H₀Forg₀ ↑↑y
      · exact hα
    · exact H₁Forf₁ ↑↑y
    · exact H₀Forf₀ ↑↑y
    · exact support_le_H₁Forf₁ ↑↑y
    · exact support_le_H₀Forf₀ ↑↑y
    · exact hα
    done

/- separated this proof out from the previous theorem because it times out 

### NEED TO PROVE
-/
theorem double_sum_in_deriv_and_exp_after_rearrang [NeZero (p^α : ℕ)] (hα : 0 < α) (f₀_at_xIsUnit : ∀(x : ℤ), IsUnit ((f₀.eval x : ℤ) : ZMod (p^(2*α)))) (rationalFunc_at_y_isunit : ∀(y : ℤ), IsUnit (rationalFunc (f₁) (f₀) (y) (p^(2*α)) : ZMod (p^(2*α))))
    (H₁Forf₁ : ∀(y : ℤ), (taylor y f₁).support.Nonempty) (H₀Forf₀ : ∀(y : ℤ), (taylor y f₀).support.Nonempty) (support_le_H₁Forf₁ : ∀(y : ℤ), (taylor y f₁).support.max' (H₁Forf₁ y) > 0) (support_le_H₀Forf₀ : ∀(y : ℤ), (taylor y f₀).support.max' (H₀Forf₀ y) > 0) 
    (g₀_at_xIsUnit : ∀(y : ℤ), IsUnit ((g₀.eval y : ℤ) : ZMod (p^(2*α)))) (H₁Forg₁ : ∀(y : ℤ), (taylor y g₁).support.Nonempty) (H₀Forg₀ : ∀(y : ℤ), (taylor y g₀).support.Nonempty) (support_le_H₁Forg₁ : ∀(y : ℤ), (taylor y g₁).support.max' (H₁Forg₁ y) > 0) (support_le_H₀Forg₀ : ∀(y : ℤ), (taylor y g₀).support.max' (H₀Forg₀ y) > 0) :
  ∑ y : (ZMod (p ^ α))ˣ, ∑ z : ZMod (p ^ α), χ (rationalFunc f₁ f₀ (↑↑y + ↑z * ↑(p ^ α)) (p ^ (2 * α))) * ψ (rationalFunc g₁ g₀ (↑↑y + ↑z * ↑(p ^ α)) (p ^ (2 * α))) 
    = ∑ y : (ZMod (p ^ α))ˣ, χ (rationalFunc f₁ f₀ y (p ^ (2 * α))) * ψ (rationalFunc (g₁) (g₀) (y) (p^(2*α))) 
    * ∑ z : ZMod (p ^ α), eZMod (p^α : ℕ) ((hFunc χ ψ f₁ f₀ g₁ g₀ hα y (p ^ (2 * α)) hp) * z) := by
    -- eZMod (p^α : ℕ) ((AddChar_eq_exp_a z ψ hp g₁ g₀ y) * ((rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z))
    rw [double_sum_in_deriv_and_exp χ ψ hp f₁ f₀ g₁ g₀ hα f₀_at_xIsUnit rationalFunc_at_y_isunit H₁Forf₁ H₀Forf₀ support_le_H₁Forf₁ support_le_H₀Forf₀ g₀_at_xIsUnit H₁Forg₁ H₀Forg₀ support_le_H₁Forg₁ support_le_H₀Forg₀]
    apply congr_arg
    funext y
    rw [Finset.mul_sum]
    apply congr_arg
    funext z
    rw [mul_assoc (χ (rationalFunc f₁ f₀ (↑↑y) (p ^ (2 * α))) : ℂ)]
    rw [mul_comm (eZMod (p ^ α) (↑(MulChar_eq_exp_b χ hp f₁ f₀) * (↑(rationalFunc_deriv f₁ f₀ (↑↑y) (p ^ (2 * α))) * ↑(rationalFunc f₁ f₀ (↑↑y) (p ^ (2 * α)))⁻¹ * z)))]
    rw [mul_assoc]
    rw [mul_assoc]
    rw [mul_comm (eZMod (p ^ α) (↑(MulChar_eq_exp_b χ hp f₁ f₀) * (↑(rationalFunc_deriv f₁ f₀ (↑↑y) (p ^ (2 * α))) * ↑(rationalFunc f₁ f₀ (↑↑y) (p ^ (2 * α)))⁻¹ * z)))]
    rw [← eZMod_add]
    rw [hFunc]
    rw [add_mul]
    repeat rw [← mul_assoc]
    
/- there must be an easier proof -/
instance (n : ℕ) (h : n ≥ 1): ZMod (n) = Fin (n) := by
  have h := Nat.exists_eq_add_of_le h 
  cases' h with k hk
  rw [hk]
  rw [add_comm]
  rfl

-- I don't need this anymore. I think. 
lemma ZMod_eq_Fin_NeZero (n : ℕ) [NeZero n] : ZMod (n) = Fin (n) := by
  have h := Nat.exists_eq_add_of_le (Fin.size_positive' (n := n))
  cases' h with k hk
  rw [hk]
  rw [add_comm]
  rfl
 
/- required for the second goal of the below theorem `eZMod_orthogonality`-/
lemma val_dvd_iff_eq_zero (q : ℕ) (m : ZMod q) [NeZero q] : 
    q ∣ m.val ↔ m = 0 := by
  rw [← ZMod.val_eq_zero]
  -- rw [dvd_iff_exists_eq_mul_left]
  apply Iff.intro
  · intro hc
    exact Nat.eq_zero_of_dvd_of_lt hc (ZMod.val_lt m)
  · intro hm
    rw [hm]
    use 0
    rfl

lemma eZMod_orthogonality (m : ZMod (p^α)) [NeZero (p^α)] : 
    ∑ z : ZMod (p ^ α), eZMod (p^α : ℕ) (m * z) = if m = 0 then (p^α : ℂ) else (0 : ℂ) := by
  split_ifs with hm
  · simp only [eZMod]
    rw [hm]
    simp only [zero_mul, ZMod.val_zero, CharP.cast_eq_zero, mul_zero, Nat.cast_pow, zero_div, exp_zero, sum_const,
      nsmul_eq_mul, mul_one]
    rw [← Nat.cast_pow]
    norm_cast
    rw [Finset.card_univ]
    exact ZMod.card (p ^ α)
  · -- simp only [eZMod]
    have eZModNeZero: eZMod (p ^ α) m ≠ 1 
    { simp only [eZMod]
      intro hexp
      -- rw [ne_eq]
      -- rw [← false_iff] -- do I need this?
      rw [Complex.exp_eq_one_iff] at hexp
      rw [mul_div_assoc] at hexp
      rw [mul_comm] at hexp
      cases' hexp with n hmn
      -- have : 2 * Real.pi * Complex.I ≠ 0 := by exact two_pi_I_ne_zero -- delete this later 
      rw [mul_left_inj' (two_pi_I_ne_zero)] at hmn
      have hdvd : p ^ α ∣ m.val
      { rw [div_eq_iff (NeZero.natCast_ne (p ^ α) ℂ)] at hmn -- nice, NeZero (p ^ α) knows that (p ^ α : ℂ) ≠ 0
        norm_cast at hmn
        have exists_hmn : ∃(c : ℤ), (m.val : ℤ) = c * (p ^ α : ℤ)
        { use n
          exact hmn }
        have := Iff.mpr dvd_iff_exists_eq_mul_left exists_hmn
        norm_cast at this }
      rw [val_dvd_iff_eq_zero] at hdvd
      tauto }
    have cexp_mul_eZMod_eq_eZMod : eZMod (p ^ α) m * ∑ z : ZMod (p ^ α), eZMod (p^α : ℕ) (m * z) = ∑ z : ZMod (p ^ α), eZMod (p^α : ℕ) (m * z)
    { rw [Finset.mul_sum]
      apply Finset.sum_bij (fun i _ ↦ i + 1)
      · intro a _
        exact Finset.mem_univ (a + 1)
      · intro a _
        rw [← eZMod_add (p ^ α) m]
        ring
      · intro a₁ a₂ _ _ ha
        rw [add_left_inj] at ha 
        exact ha
      · intro b _ 
        use b - 1
        have ha : b - 1 ∈ Finset.univ := by exact Finset.mem_univ (b - 1) 
        use ha
        ring  }
    rw [← sub_eq_zero] at cexp_mul_eZMod_eq_eZMod
    nth_rw 2 [← one_mul (∑ z : ZMod (p ^ α), eZMod (p^α : ℕ) (m * z))] at cexp_mul_eZMod_eq_eZMod
    rw [← sub_mul] at cexp_mul_eZMod_eq_eZMod
    rw [mul_eq_zero] at cexp_mul_eZMod_eq_eZMod
    rw [sub_eq_zero] at cexp_mul_eZMod_eq_eZMod
    tauto

example [NeZero (p^α)] : 
  ∑ z : ZMod (p ^ α), z = ∑ z_1 : ZMod (p ^ α), z_1 := by
  refine congrArg (Finset.sum Finset.univ) rfl

/- I need to find a way to have ∀(z : ZMod (p^α)), hFunc and all related lemmas hold so that those lemmas don't need to eat a variable z 
Answer : Use theorem `MulChar_additive_eq_exp_for_all` 
-/
lemma eZMod_hFunc_orthogonality (y : ZMod (p ^ α)) [NeZero (p^α)] : 
    ∑ z : ZMod (p ^ α), eZMod (p^α : ℕ) (hFunc χ ψ f₁ f₀ g₁ g₀ hα y (p ^ (2 * α)) hp * z) 
    = if (hFunc χ ψ f₁ f₀ g₁ g₀ hα y (p ^ (2 * α)) hp : ZMod (p^α)) = 0 then (p^α : ℂ) else (0 : ℂ) := by
  exact eZMod_orthogonality (hFunc χ ψ f₁ f₀ g₁ g₀ hα y (p ^ (2 * α)) hp : ZMod (p^α))

/- 
inner sum vanishes unless h (y) ≡ 0 [ZMOD p^α] 
By the theorem `Finset.sum_empty` the sum equals zero when h (y) ≡ 0 [ZMOD p^α] has no solution
-/
-- (hFunc z₁ χ ψ f₁ f₀ g₁ g₀ x y x₀ (p^α) hp)
-- (h : x = y + z * (p^α : ℕ))
theorem even_pow_final_formula [NeZero (p^α : ℕ)] (hα : 0 < α) (f₀_at_xIsUnit : ∀(x : ℤ), IsUnit ((f₀.eval x : ℤ) : ZMod (p^(2*α)))) (rationalFunc_at_y_isunit : ∀(y : ℤ), IsUnit (rationalFunc (f₁) (f₀) (y) (p^(2*α)) : ZMod (p^(2*α))))
    (H₁Forf₁ : ∀(y : ℤ), (taylor y f₁).support.Nonempty) (H₀Forf₀ : ∀(y : ℤ), (taylor y f₀).support.Nonempty) (support_le_H₁Forf₁ : ∀(y : ℤ), (taylor y f₁).support.max' (H₁Forf₁ y) > 0) (support_le_H₀Forf₀ : ∀(y : ℤ), (taylor y f₀).support.max' (H₀Forf₀ y) > 0) 
    (g₀_at_xIsUnit : ∀(y : ℤ), IsUnit ((g₀.eval y : ℤ) : ZMod (p^(2*α)))) (H₁Forg₁ : ∀(y : ℤ), (taylor y g₁).support.Nonempty) (H₀Forg₀ : ∀(y : ℤ), (taylor y g₀).support.Nonempty) (support_le_H₁Forg₁ : ∀(y : ℤ), (taylor y g₁).support.max' (H₁Forg₁ y) > 0) (support_le_H₀Forg₀ : ∀(y : ℤ), (taylor y g₀).support.max' (H₀Forg₀ y) > 0) :
    CharSum χ ψ f₁ f₀ g₁ g₀ (p^(2*α)) = (p^α : ℕ) * (∑ r in ((Finset.univ : Finset (ZMod (p^α))ˣ).filter (fun r => sol_hFunc χ ψ hp f₁ f₀ g₁ g₀ hα r (p^ (2 * α)))), 
    χ (rationalFunc f₁ f₀ ((r : (ZMod (p^α))ˣ) : ℤ) (p ^ (2 * α))) * ψ (rationalFunc g₁ g₀ ((r : (ZMod (p^α))ˣ) : ℤ) (p ^ (2 * α)))) := by
  rw [CharSum]
  simp only [ZMod.cast_id', id_eq]
  rw [Sum_into_two_sums_v2 hp (fun n => χ n) (fun n => ψ n) (fun n => rationalFunc f₁ f₀ n (p^(2*α))) (fun n => rationalFunc g₁ g₀ n (p^(2*α))) hα] 
  -- rw [MulChar_in_y_and_z z χ f₁ f₀ (((y : ZMod (p^α)) : ℤ) + (z : ℤ) * (p ^ α : ℤ)) ((y : ZMod (p^α)) : ℤ)]
  rw [double_sum_in_deriv_and_exp_after_rearrang χ ψ hp f₁ f₀ g₁ g₀ hα f₀_at_xIsUnit rationalFunc_at_y_isunit H₁Forf₁ H₀Forf₀ support_le_H₁Forf₁ support_le_H₀Forf₀ g₀_at_xIsUnit H₁Forg₁ H₀Forg₀ support_le_H₁Forg₁ support_le_H₀Forg₀]
  rw [Finset.sum_filter]
  rw [Finset.mul_sum]
  apply congr_arg
  funext y
  simp only [sol_hFunc]
  rw [eZMod_hFunc_orthogonality]
  split_ifs
  · ring
  · ring
