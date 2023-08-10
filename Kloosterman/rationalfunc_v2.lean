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

/- Note
We have to keep the variables `x` `y` as `ℤ` for the following theorems w.r.t taylor series
When dealing with Kloosterman sum, I think we have to coerce the variables from ZMod q to ℤ 
when using the theorems for the taylor series and Kloosterman sum at the same time 
-/

variable {p : ℕ} {α : ℕ} (z : ZMod (p^α : ℕ)) (χ : MulChar (ZMod (p^(2*α) : ℕ)) ℂ) (ψ : AddChar (ZMod (p^(2*α) : ℕ)) ℂ) [NeZero (p^(2*α) : ℕ)] (hp : Prime p)
-- (q : ℕ) (x : ZMod q) (y : ℤ) (z : ZMod q)

variable (f₁ f₀ g₁ g₀ : Polynomial ℤ)

-- the denom is not equal to zero by the theorem `Ratfunc.denom_ne_zero`
-- numerator and denominator are coprime by the theorem `Ratfunc.is_coprime_num_denom`

-- f.denom.eval x ≠ 0 
-- RatFunc (ZMod q)ˣ doesn't work


/-
def poly_eval_ZMod (p₀ : Polynomial ℤ) (x₀ : ℤ) (q : ℕ) : ZMod q :=
  let r := p₀.eval x₀
  (r : ZMod q)

  -- my answer: use `((p₀.eval x : ℤ) : ZMod (p^(2*α)))` instead 

-/ 


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


theorem poly_taylor (p₀ : Polynomial ℤ) (y : ℤ) : 
    p₀ = ((taylor y p₀).sum fun i a => C a * (X - C y) ^ i) := by
  -- have H := taylor_coeff_one (y) (p₀)
  exact Eq.symm (sum_taylor_eq p₀ y)

-- consider whether to have z : ℤ instead of (ZMod q)ˣ
-- is this statement even true? 
-- polynomial.eval_geom_sum
-- eval_finset_sum

/- note to myself 
By definition, 
`((taylor y p₀).sum fun i a => a * ((z : ℤ) * (p^α : ℕ)) ^ i)`
`= ∑ n in support (↑(taylor y) p₀), coeff (↑(taylor y) p₀) n * (↑z * ↑(p ^ α)) ^ n`
-/
-- # ASK KEVIN
theorem poly_taylor_eval (p₀ : Polynomial ℤ) (x y : ℤ) (h : x = y + z * (p^α : ℕ)) :
    p₀.eval (x : ℤ)  = ((taylor y p₀).sum fun i a => a * ((z : ℤ) * (p^α : ℕ)) ^ i) := by
  nth_rw 1 [poly_taylor p₀ y] -- rewrites only lhs
  rw [sum]
  simp only [eval_finset_sum, eval_mul, eq_intCast, eval_int_cast, cast_id, eval_pow, eval_sub, eval_X, Nat.cast_pow]
  rw [h]
  simp only [Nat.cast_pow, add_sub_cancel']
  exact rfl
  -- rw [Polynomial.eval_C]
  -- rw [Polynomial.eval_X]

/- Proves that 
p₁ (x) ≡ p₁ (y) + p₁' (y) *z*p^α [ZMOD (p^(2*α))]

p₁.eval x ≡ p₁.eval y + (p₁.derivative.eval y) * z * (p^α) [ZMOD (p^(2*α))]
-/


/- expressed only as a sum 
idea : calculate the first two terms of the lhs and cancel them out with the terms on the rhs
Then we can sum the variable over the Finset ℕ instead of Finset ℤ 

potential solution 1 : maybe use erase and insert or filter
  note: insert recognizes the set as Finset ℕ as long as the element inserted is : ℕ 

potential solution 2 : I think it's better to just add 2 to every element in `(taylor y p₀).support`
which should be possible since Finset is constructed in a way that it enumerates all its elements 

potential solution 3: maybe use def `list.to_finset` and def `finset.to_list`
We need to create a list which has the elements of `(taylor y p₀).support` and add 2 to them. 
Then create the Finset ℕ from the list with elements + 2


list.modify_nth_tail
list.lookmap
list.of_fn  -- Nope
list.map_with_prefix_suffix
-/

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
        · simp only [Finset.mem_range, add_pos_iff, or_true, not_true, mem_sdiff, lt_add_iff_pos_left, and_true,
          not_lt, nonpos_iff_eq_zero, union_sdiff_self_eq_union, Finset.disjoint_union_right,
          Finset.disjoint_singleton_left, and_false, not_false_eq_true, and_self]
        · simp only [Finset.mem_range, add_pos_iff, or_true, not_true, mem_sdiff, lt_add_iff_pos_left, and_true,
          not_lt, nonpos_iff_eq_zero, union_sdiff_self_eq_union, Finset.disjoint_union_right,
          Finset.disjoint_singleton_left, and_false, not_false_eq_true, and_self]
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
  



  /-
  have H : (Finset.range ((taylor y p₀).support.max' H + 1) \ {0}) = {1} ∪ ((Finset.range ((taylor y p₀).support.max' H + 1) \ {0}) \ {1}) := by
    rw [Finset.union_sdiff_of_subset]
    simp only [Finset.mem_range, add_pos_iff, or_true, not_true, Finset.singleton_subset_iff, mem_sdiff,
      lt_add_iff_pos_left, and_true]
    exact support_le
  -/


  -- apply Finset.sum_bij (s := (taylor y p₀).support) (fun i _ ↦ i)

/- first version
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
-/

/- lemma we don't need anymore
lemma h₂Andh₃ (a : ℕ): a ≥ 1 ∧ (a < 1 ∨ a > 1) → a ≥ 2 := by
  choose _ ha
  cases' ha with _ a_lt_one
  · linarith
  · exact a_lt_one
-/

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

lemma sum_move_two (p₀ : Polynomial ℤ) (x y : ℤ) (H : (taylor y p₀).support.Nonempty) (support_lt : (taylor y p₀).support.max' H > 0) (h : x = y + z * (p^α : ℕ)) : 
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
    exact rfl

-- once we convert the sum into Finset.range, then we can use the theorem `finset.sum_cons` or `finset.sum_disj_union` to sort this out

lemma sum_higher_terms_in_poly (p₀ : Polynomial ℤ) (x y : ℤ) (H : (taylor y p₀).support.Nonempty) (support_le : (taylor y p₀).support.max' H > 0) (h : x = y + z * (p^α : ℕ)) : 
    ∃(z₀ : ℤ), (p^(2*α) : ℕ) * z₀
    = ∑ i in (Finset.range ((taylor y p₀).support.max' H + 1) \ {0}) \ {1}, ((taylor y p₀).coeff i * ((z : ℤ) * (p^α : ℕ)) ^ i) := by
  -- rcases (taylor y p₀).support.max' H > 1 
  rw [sum_move_two z p₀ x y H support_le h]
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

/- previous version
theorem poly_taylor_eval_ZMod (p₀ : Polynomial ℤ) (x y : ℤ) (H : (taylor y p₀).support.Nonempty) (support_le : (taylor y p₀).support.max' H > 0) (h : x = y + z * (p^α : ℕ)) :
    p₀.eval x ≡ p₀.eval y + ((Polynomial.derivative (R := ℤ)) p₀).eval y * z * (p^α : ℕ) [ZMOD (p^(2*α))] := by
  rw [poly_taylor_eval_term_by_term z p₀ x y H support_le h]
  have hz := sum_higher_terms_in_poly z p₀ x y H support_le h
  cases' hz with z₀ hz₀
  rw [← hz₀]
  exact modEq_add_fac z₀ rfl
-/ 

theorem poly_taylor_eval_ZMod (p₀ : Polynomial ℤ) (x y : ℤ) (H : (taylor y p₀).support.Nonempty) (support_le : (taylor y p₀).support.max' H > 0) (h : x = y + z * (p^α : ℕ)) :
    ((p₀.eval x : ℤ) : ZMod (p^(2*α))) =  ((p₀.eval y + ((Polynomial.derivative (R := ℤ)) p₀).eval y * z * (p^α : ℕ) : ℤ) : ZMod (p^(2*α))) := by
  rw [poly_taylor_eval_term_by_term z p₀ x y H support_le h]
  have hz := sum_higher_terms_in_poly z p₀ x y H support_le h
  cases' hz with z₀ hz₀
  rw [← hz₀]
  rw [cast_add]
  rw [cast_mul]
  rw [cast_ofNat]
  rw [ZMod.nat_cast_self]
  rw [zero_mul]
  rw [add_zero]

/-
-- be extra careful with how you state this theorem
theorem RatFunc_eq_num_denom_ZMod (x y : ℤ) (h : x = y + z * (p^α : ℕ)) (H : r = p₂.eval x):
    1 ≡ p₁.eval x * ((p₂.eval x) : ZMod (p^α))⁻¹ [ZMOD (p^(2*α))] := by
  field_simp
  sorry
-/

/- previous version 
theorem rationalFunc_well_defined_ZMod (x y : ℤ) {h : x = y + z * (p^α : ℕ)} :
    rationalFunc (p₁) (p₀) (x) (p^(2*α)) ≡ 
    (p₁.eval y + ((Polynomial.derivative (R := ℤ)) p₁).eval y * z * (p^α : ℕ)) 
    * ((p₀.eval y + ((Polynomial.derivative (R := ℤ)) p₀).eval y * z * (p^α : ℕ)) : ZMod (p^(2*α)))⁻¹ [ZMOD (p^(2*α))] := by
  simp only [rationalFunc]
  rw [poly_taylor_eval_ZMod p₁ x y]
  sorry
-/

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

/- Previous version
lemma rationalFunc_eq_ZMod (p₁ p₀ : Polynomial ℤ) (x y : ℤ) (h : x = y + z * (p^α : ℕ)) :
    rationalFunc (p₁) (p₀) (x) (p^(2*α)) ≡ rationalFunc (p₁) (p₀) (y) (p^(2*α)) 
    + (rationalFunc_deriv (p₁) (p₀) (y) (p^(2*α))) * z * (p^α : ℕ) [ZMOD (p^(2*α))] := by
-/

/- corollary of theorem `poly_taylor_eval_ZMod` -/

lemma congr_IsUnit (q : ℕ) (a b : ZMod q) (hCongr : a ≡ b [ZMOD q]) (IsUnitFora : IsUnit a): IsUnit b := by
  rw [← ZMod.int_cast_eq_int_cast_iff] at hCongr
  simp at hCongr -- try out simp?
  rw [← hCongr]
  exact IsUnitFora

/- -/
lemma poly_at_yIsUnit (p₀ : Polynomial ℤ) (x y : ℤ) (H : (taylor y p₀).support.Nonempty) (support_le : (taylor y p₀).support.max' H > 0) (p₀_at_xIsUnit : IsUnit ((p₀.eval x : ℤ) : ZMod (p^(2*α)))) (h : x = y + z * (p^α : ℕ)) : 
    IsUnit ((p₀.eval y : ℤ) : ZMod (p^(2*α))) := by
  -- by_contra NeUnit
  
  rw [← isCoprime_zero_left]
  have HH : ¬ (((p₀.eval y : ℤ) : ZMod (p^(2*α))) : ZMod p) = 0 ↔ IsCoprime 0 ((p₀.eval y : ℤ) : ZMod (p^(2*α))) := by

    -- rw [ZMod.int_cast_zmod_eq_zero_iff_dvd]
    
    -- zmod.int_coe_zmod_eq_zero_iff_dvd
    
    sorry
  rw [← HH]
  have poly_ZModPrimePow := poly_taylor_eval_ZMod z p₀ x y H support_le h

  -- p₀.eval x ≡ p₀.eval y + ((Polynomial.derivative (R := ℤ)) p₀).eval y * z * (p^α : ℕ)
  have poly_ZModPrime : p₀.eval x ≡ p₀.eval y [ZMOD p]
  { 
      -- zmod.cast_add
    sorry
  }
  rw [← ZMod.int_cast_eq_int_cast_iff] at poly_ZModPrime
  
  push_cast at poly_ZModPrime
  -- rw [ZMod.cast_int_cast]
  -- rw [← poly_ZModPrime]




  /- 
  -- by_contra NeUnit
  rw [← isCoprime_zero_left]
  have HH : ((poly_eval_ZMod p₀ y (p ^ (2 * α))) : ZMod p) = 0 → IsCoprime 0 (poly_eval_ZMod p₀ y (p ^ (2 * α))) := by
    intro hy
    
    rw [ZMod.int_cast_zmod_eq_zero_iff_dvd]
    
    -- zmod.int_coe_zmod_eq_zero_iff_dvd
    
    sorry
  apply HH
  have poly_ZModPrimePow := poly_taylor_eval_ZMod z p₀ x y H support_le h

  -- p₀.eval x ≡ p₀.eval y + ((Polynomial.derivative (R := ℤ)) p₀).eval y * z * (p^α : ℕ)
  have poly_ZModPrime : p₀.eval x ≡ p₀.eval y [ZMOD p]
  { 
      -- zmod.cast_add
    sorry
  }
  rw [← ZMod.int_cast_eq_int_cast_iff] at poly_ZModPrime
  
  push_cast at poly_ZModPrime
  simp only [poly_eval_ZMod]
  rw [ZMod.cast_int_cast]
  rw [← poly_ZModPrime]
  
  
  -/




  -- simp only [isCoprime_zero_left (x := poly_eval_ZMod p₀ y (p^(2*α)))]
  
  /-
  rw [isUnit_iff_exists_inv] at *
  cases' p₀_at_xIsUnit with c hc
  have poly_ZMod := poly_taylor_eval_ZMod z p₀ x y H support_le h
  rw [← ZMod.int_cast_eq_int_cast_iff] at poly_ZMod
  simp only [poly_eval_ZMod] at hc
  push_cast at poly_ZMod
  simp only [poly_eval_ZMod]
  -/ 
  
  -- apply Iff.mpr isUnit_iff_exists_inv 
  
  
  -- rw [← isCoprime_self]
  -- `poly_taylor_eval_ZMod` is the one 
  -- refine Iff.mp isCoprime_self (?_ (id (Eq.symm h)))
  sorry


/- 
lemma poly_eval_ZMod_IsUnit_inv_one (p₀ : Polynomial ℤ) (x y : ℤ) (h : x = y + z * (p^α : ℕ)) (p₀_at_xIsUnit : IsUnit ((p₀.eval x : ℤ) : ZMod (p^(2*α)))) : 
    ((p₀.eval y : ℤ) : ZMod (p^(2*α))) * rationalFunc_inverse p₀ y (p^(2*α)) = 1 := by

  sorry
  /-
  have yIsUnit := poly_at_yIsUnit z p₀ x y h p₀_at_xIsUnit
  simp only [poly_eval_ZMod] at *
  simp only [rationalFunc_inverse]
  exact ZMod.mul_inv_of_unit (↑(eval y p₀)) yIsUnit
   -/
-/

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
  
  -- exact False.elim IsUnit

/- 
theorem poly_taylor_eval_ZMod (p₀ : Polynomial ℤ) (x y : ℤ) (H : (taylor y p₀).support.Nonempty) (support_le : (taylor y p₀).support.max' H > 0) (h : x = y + z * (p^α : ℕ)) :
    p₀.eval x ≡ p₀.eval y + ((Polynomial.derivative (R := ℤ)) p₀).eval y * z * (p^α : ℕ) [ZMOD (p^(2*α))] := by
-/
/- corollary of theorem `poly_taylor_eval_ZMod` -/
-- Do something about the `IsUnit (p₀.eval x)` later
-- this should become the final boss for the power world
lemma rationalFunc_eq_ZMod (p₁ p₀ : Polynomial ℤ) (x y : ℤ) (H₁ : (taylor y p₁).support.Nonempty) (H₀ : (taylor y p₀).support.Nonempty) (support_le_H₁ : (taylor y p₁).support.max' H₁ > 0) 
    (support_le_H₀ : (taylor y p₀).support.max' H₀ > 0) (h : x = y + z * (p^α : ℕ)) (p₀_at_xIsUnit : IsUnit ((p₀.eval x : ℤ) : ZMod (p^(2*α)))) :
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
  repeat rw [mul_add]
  /- process of cancelling out `↑(eval y p₀)` with its inverse -/
  -- gets rid of the inverses in the first term of the rhs
  rw [mul_assoc]
  rw [ZMod.inv_mul_of_unit ((p₀.eval y : ℤ) : ZMod (p^(2*α))) (poly_at_yIsUnit z p₀ x y H₀ support_le_H₀ p₀_at_xIsUnit h)]
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
  rw [ZMod.inv_mul_of_unit ((p₀.eval y : ℤ) : ZMod (p^(2*α))) (poly_at_yIsUnit z p₀ x y H₀ support_le_H₀ p₀_at_xIsUnit h)]
  
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

  /-
  simp only [rationalFunc_well_defined_ZMod]
  simp only [rationalFunc, rationalFunc_deriv] 
  simp only [rationalFunc_inverse]
  repeat rw [← poly_eval_ZMod] -- instead of having this, consider whether it's better to make the definitions using `poly_eval_ZMod`
  


  have poly_evalForp₁ := (poly_taylor_eval_ZMod z p₁ x y H₁ support_le_H₁ h)
  have ZModCastForp₁ := Iff.mpr (ZMod.int_cast_eq_int_cast_iff (p₁.eval x) (p₁.eval y + ((Polynomial.derivative (R := ℤ)) p₁).eval y * z * (p^α : ℕ)) (p^(2*α))) poly_evalForp₁
  rw [ZModCastForp₁]
  have poly_evalForp₀ := (poly_taylor_eval_ZMod z p₀ x y H₀ support_le_H₀ h)
  have ZModCastForp₀ := Iff.mpr (ZMod.int_cast_eq_int_cast_iff (p₀.eval x) (p₀.eval y + ((Polynomial.derivative (R := ℤ)) p₀).eval y * z * (p^α : ℕ)) (p^(2*α))) poly_evalForp₀
  rw [ZModCastForp₀]
  have p₀_in_yIsUnit : IsUnit ((p₀.eval y + (((Polynomial.derivative (R := ℤ)) p₀).eval y * z * (p^α : ℕ)) : ℤ) : ZMod (p^(2*α)))
  { 
    sorry
  }
  rw [← poly_eval_ZMod]
  simp only [poly_eval_ZMod] at p₀_in_yIsUnit
  rw [ZMod.mul_inv]

  -/

  /- 
  rw [mul_left_inj ((p₀.eval y + ((Polynomial.derivative (R := ℤ)) p₀).eval y * z * (p^α : ℕ)) : ZMod (p^(2*α)))]
  rw [ZMod.mul]
  rw [inv_assoc]
  -/
  
  
/- # lemma needed
need a lemma that shows that the denominator is unit → rationalFunc is unit
or vice versa 
-/


/- necessary for the theorem inv_cancel -/
lemma rationalFunc_unit (x y : ℤ) :
    IsUnit (rationalFunc (f₁) (f₀) (x) (p^(2*α)) : ZMod (p^(2*α))) := by
  sorry

/- note to myself
Figure out when and how to state the assumption rationalFunc_isunit at the start of this document
-/ 
lemma rationalFunc_inv_cancel (y : ℤ) (rationalFunc_isunit : IsUnit (rationalFunc (f₁) (f₀) (y) (p^(2*α)) : ZMod (p^(2*α)))):
    (rationalFunc (f₁) (f₀) (y) (p^(2*α)) : ZMod (p^(2*α))) * (rationalFunc (f₁) (f₀) (y) (p^(2*α)) : ZMod (p^(2*α)))⁻¹ = 1 := by
  exact ZMod.mul_inv_of_unit (rationalFunc f₁ f₀ y (p ^ (2 * α))) rationalFunc_isunit

-- fix
lemma MulChar_in_y_and_z (x y : ℤ) (h : x = y + z * (p^α : ℕ)) (f₀_at_xIsUnit : IsUnit ((f₀.eval x : ℤ) : ZMod (p^(2*α)))) (rationalFunc_at_y_isunit : IsUnit (rationalFunc (f₁) (f₀) (y) (p^(2*α)) : ZMod (p^(2*α)))) 
    (H₁ : (taylor y f₁).support.Nonempty) (H₀ : (taylor y f₀).support.Nonempty) (support_le_H₁ : (taylor y f₁).support.max' H₁ > 0) (support_le_H₀ : (taylor y f₀).support.max' H₀ > 0) :
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
  rw [rationalFunc_eq_ZMod z f₁ f₀ x y H₁ H₀ support_le_H₁ support_le_H₀ h f₀_at_xIsUnit]
  ring

/- deleted the following:
(p : ℕ) (hp : Prime p) (α : ℕ) (z : ZMod (p^α : ℕ)) (χ : MulChar (ZMod (p^(2*α) : ℕ)) ℂ)
-/ 
theorem MulChar_eq_exp (x y : ℤ) :
    ∃(b : ℕ), b < p^α ∧ χ' (χ) ((rationalFunc_deriv (f₁) (f₀) (y) (p^(2*α))) * (rationalFunc (f₁) (f₀) (x) (p^(2*α)) : ZMod (p^(2*α)))⁻¹ * z) 
    = eZMod (p^α : ℕ) (b * ((rationalFunc_deriv (f₁) (f₀) (y) (p^(2*α))) * (rationalFunc (f₁) (f₀) (x) (p^(2*α)) : ZMod (p^(2*α)))⁻¹ * z)) := by
  exact MulChar_additive_eq_exp p hp α ((rationalFunc_deriv (f₁) (f₀) (y) (p^(2*α))) * (rationalFunc (f₁) (f₀) (x) (p^(2*α)) : ZMod (p^(2*α)))⁻¹ * z) χ 

/- the natural number b whose existence is guaranteed by MulChar_eq_exp -/
def MulChar_eq_exp_b (x y : ℤ) : ℕ := (MulChar_eq_exp z χ hp f₁ f₀ x y).choose

variable (x y : ℤ)

lemma MulChar_eq_exp_b_WellDefined : (MulChar_eq_exp z χ hp f₁ f₀ x y).choose = MulChar_eq_exp_b z χ hp f₁ f₀ x y := rfl

theorem MulChar_eq_exp_b_spec (x y : ℤ) :
   (MulChar_eq_exp_b z χ hp f₁ f₀ x y) < p^α ∧ χ' (χ) ((rationalFunc_deriv (f₁) (f₀) (y) (p^(2*α))) * (rationalFunc (f₁) (f₀) (x) (p^(2*α)) : ZMod (p^(2*α)))⁻¹ * z) 
    = eZMod (p^α : ℕ) ((MulChar_eq_exp_b z χ hp f₁ f₀ x y) * ((rationalFunc_deriv (f₁) (f₀) (y) (p^(2*α))) * (rationalFunc (f₁) (f₀) (x) (p^(2*α)) : ZMod (p^(2*α)))⁻¹ * z)) :=
  (MulChar_eq_exp z χ hp f₁ f₀ x y).choose_spec

open AddChar

lemma AddChar_in_y_and_z (x y : ℤ) (H₁ : (taylor y g₁).support.Nonempty) (H₀ : (taylor y g₀).support.Nonempty) (support_le_H₁ : (taylor y g₁).support.max' H₁ > 0) (support_le_H₀ : (taylor y g₀).support.max' H₀ > 0) {h : x = y + z * (p^α : ℕ)} (g₀_at_xIsUnit : IsUnit ((g₀.eval x : ℤ) : ZMod (p^(2*α)))):
    ψ (rationalFunc (g₁) (g₀) (x) (p^(2*α))) = ψ (rationalFunc (g₁) (g₀) (y) (p^(2*α))) * ψ ((rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z * (p^α : ℕ)) := by
  rw [rationalFunc_eq_ZMod z g₁ g₀ x y H₁ H₀ support_le_H₁ support_le_H₀ h g₀_at_xIsUnit]
  simp

lemma AddChar_one_pow (z₀ : ZMod (p^(2*α))) : (ψ 1)^z₀.val = ψ z₀ := by
  rw [← mulShift_spec' ψ z₀.val 1, mulShift_apply]
  simp only [ZMod.nat_cast_val, ZMod.cast_id', id_eq, mul_one]

lemma NeZero_pPow : NeZero (p^(2*α)) := ⟨pow_ne_zero (2*α) $ Prime.ne_zero hp⟩

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

    -- Complex.mem_rootsOfUnity
/- very similar to the proof for the theorem `MulChar_additive_eq_exp` in the document lemma_char_v4.lean -/
theorem AddChar_eq_exp (z₀ : ZMod (p^(2*α))) :
    ∃(a : ℕ), a < p^(2*α) ∧ ψ z₀ = eZMod (p^(2*α)) (a * z₀) := by
  have : NeZero (p^(2*α)) := ⟨pow_ne_zero (2*α) $ Prime.ne_zero hp⟩ -- delete this later because we have the lemma
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

/- 
# later on we need this lemma complex_natural
later incoporate this in this the theorem hh' : `(p ^ α : ℂ) / (p ^ (2 * α) : ℂ) = 1 / (p ^ α : ℂ)`
but remember to use it as the theorem `Nat.cast_mul n₁ n₂`
-/
lemma complex_natural (n₁ n₂: ℕ): ((n₁ * n₂ : ℕ) : ℂ) = (n₁ : ℂ) * (n₂ : ℂ) := by
  exact Nat.cast_mul n₁ n₂

lemma congr_self (n q : ℕ) [NeZero q] : (n : ZMod q).val ≡ n [ZMOD q] := by
  rw [← ZMod.int_cast_eq_int_cast_iff]
  simp only [ZMod.nat_cast_val, ZMod.int_cast_cast, ZMod.cast_nat_cast', cast_ofNat]

/- 
lemma foofoo (n q : ℕ): ∃(m : ℤ), ((n : ZMod (q)).val) = (n : ℕ) + m * (q : ℕ) := by
  sorry 
  /- 
  lemma bar (a b : ℕ) (q : ℕ) (hq : q ≠ 0) (ha : a < q) (hab : a ≡ b [MOD q]) :
    ∃ n, b = a + n * q := by
  simp [Nat.ModEq] at hab
  rw [Nat.mod_eq_of_lt ha] at hab
  rw [hab]
  use b / q
  exact Eq.symm (Nat.mod_add_div' b q)
  -/
-/

-- erase the assumption `h` and derive from the existing assumption
lemma foo' (h : (p^(2*α) : ℂ) ≠ 0): ∃(m : ℤ), (((p ^ α : ZMod (p ^ (2 * α))).val) : ℂ) / (p ^ (2 * α) : ℂ) = 1 / (p ^ α : ℂ) + m := by
  have H : ∃(m : ℤ), ((p ^ α : ZMod (p ^ (2 * α))).val : ℂ) = (p^α : ℕ) + m * (p ^ (2 * α) : ℕ) := by
    exact complex_eq_congr (p ^ (2*α)) (p ^ α : ZMod (p ^ (2 * α))).val (p ^ α) (congr_self (p ^ α) (p ^ (2 * α)))
  cases' H with m Hm
  rw [Hm]
  use m
  simp only [ZMod.nat_cast_val]
  -- later on incorporate into the proof seamlessly without the `have` tactic
  have hh' : (p ^ α : ℂ) / (p ^ (2 * α) : ℂ) = 1 / (p ^ α : ℂ) := by
    rw [mul_comm, pow_mul, Nat.pow_two (p^α), Nat.cast_mul, Nat.cast_pow, div_self_mul_self', one_div]
  rw [add_div, hh', ← mul_div, div_self h, Nat.cast_pow, one_div, mul_one]
  
theorem AddChar_rationalFunc_deriv_eq_exp (y : ℤ) :
    ∃(a : ℕ), a < p^(2*α) ∧ ψ ((rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z * (p^α : ℕ)) = eZMod (p^α : ℕ) (a * ((rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z)) := by
  -- ∃(a : ℕ), a < p^(2*α) ∧ ψ z₀ = eZMod (p^(2*α)) (a * z₀) := by
  have eq_exp := AddChar_eq_exp ψ hp (rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α)) * z * (p ^ α : ℕ))
  simp only [eZMod] at *
  -- simp only [Nat.cast_pow, ZMod.nat_cast_val] at eq_exp 

  /- strategy of proof
  for eq_exp :
  1. Show ZMod.val (↑a * (↑(rationalFunc_deriv g₁ g₀ y (p ^ (2 * α))) * ↑z * ↑(p ^ α))) = ZMod.val (↑a * (↑(rationalFunc_deriv g₁ g₀ y (p ^ (2 * α))) * z) *  ZMod.val (↑(p ^ α))) + m * p ^ (2 * α) for some integer b
     use the following lemma from lemma_char_v4.lean
     1. 
     lemma congr_val (q : ℕ) (x₁ x₂ : ZMod q) : 
      (x₁ * x₂).val ≡ x₁.val * x₂.val [MOD q] := by
     rw [ZMod.val_mul x₁ x₂]
     exact Nat.mod_modEq (x₁.val * x₂.val) (q)

     2. 
     have congr_val : ((b : ZMod (p^α : ℕ)) * z).val ≡ (b : ZMod (p^α)).val * z.val [ZMOD (p^α)]
    { rw [ZMod.val_mul (↑b) z]
      exact Int.mod_modEq ((b : ZMod (p^α)).val * ZMod.val z) (p ^ α) }

     3. 
     have congr_b : (b : ZMod (p^α)).val * z.val ≡ b * z.val [ZMOD (p^α)] := by gcongr

     Need to choose later 
 
  2. Cancel out the m * p ^ (2 * α) term in the exponential
  3. Show that for A B : ℕ, (A : ℂ) * (B : ℂ) = (A * B : ℕ) 
     Update: the proof is `by exact Eq.symm (complex_natural A B)`
     Then with the above, ↑(ZMod.val (↑a * (↑(rationalFunc_deriv g₁ g₀ y (p ^ (2 * α))) * z) *  ZMod.val (↑(p ^ α)))) = ↑(ZMod.val (↑a * (↑(rationalFunc_deriv g₁ g₀ y (p ^ (2 * α))) * z)) *  ↑(ZMod.val (↑(p ^ α))))
  
  
  
  4. Then need to deal with `↑(ZMod.val (↑(p ^ α))) / ↑(p ^ (2 * α)) = 1 / ↑(p ^ α) + m` for some integer
  5. Then the term `m` will disappear inside the exponential
   -/
  

  sorry 

-- decide whether we really want to do it for the variable `z` not another variable
/- the natural number a whose existence is guaranteed by AddChar_eq_exp -/
/- 
It is okay to have the variable as `x` and `y` as long as they are just arbitrary variables without any condition on it
like `h : x = y + z * p^α`
-/

/- previous version
def AddChar_eq_exp_a : ℕ := (AddChar_eq_exp ψ hp z).choose

--AddChar_eq_exp_a z ψ hp
theorem AddChar_eq_exp_a_spec :
    AddChar_eq_exp_a z ψ hp < p^(2*α) ∧ ψ z = eZMod (p^(2*α)) (AddChar_eq_exp_a z ψ hp * z) :=
  (AddChar_eq_exp ψ hp z).choose_spec
-/

def AddChar_eq_exp_a : ℕ := (AddChar_rationalFunc_deriv_eq_exp z ψ hp g₁ g₀ y).choose

theorem AddChar_eq_exp_a_spec :
    (AddChar_eq_exp_a z ψ hp g₁ g₀ y) < p^(2*α) ∧ ψ ((rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z * (p^α : ℕ)) = eZMod (p^α : ℕ) ((AddChar_eq_exp_a z ψ hp g₁ g₀ y) * ((rationalFunc_deriv (g₁) (g₀) (y) (p^(2*α))) * z)) :=
  (AddChar_rationalFunc_deriv_eq_exp z ψ hp g₁ g₀ y).choose_spec

-- delete this later
instance (q : ℕ) [NeZero q] : Fintype (ZMod q) := by
  -- exact False.elim is_good
  infer_instance

-- needs rewriting
-- a and b are from the characters ψ χ -- [MulChar_eq_exp] [AddChar_eq_exp]
-- should hFunc : ℤ or ZMod q
-- remember that we have the use the orthogonality property of char by setting hFunc ≡ 0 [ZMOD q]
def hFunc (x y r : ℤ) (q : ℕ) (hp : Prime p) : ℤ :=
  -- let ⟨b, hl, hr⟩ := MulChar_eq_exp (z) (χ) (f₁) (f₀) (x) (y) 
  (AddChar_eq_exp_a z ψ hp g₁ g₀ y) * (rationalFunc_deriv g₁ g₀ r q) + (MulChar_eq_exp_b z χ hp f₁ f₀ x y) * (rationalFunc_deriv f₁ f₀ r q) * (rationalFunc f₁ f₀ r q : ZMod q)⁻¹

-- (MulChar_eq_exp_b z χ hp f₁ f₀ x y)

/- set of all solutions to hFunc-/
-- x₀ : ℤ or ZMod p^α or (ZMod (p^α : ℕ))ˣ 
-- need to make it reply on the variables `a` and `b` from MulChar_eq_exp and AddChar_eq_exp
def sol_hFunc (x y r : ℤ) (q : ℕ) : Prop := 
  hFunc z χ ψ f₁ f₀ g₁ g₀ x y r q hp ≡ 0 [ZMOD q] ∧ IsUnit ((r : ZMod (p^(2*α))))

def map_sol_hFunc (x y : ℤ) : ℕ → Prop := 
  fun r => sol_hFunc z χ ψ hp f₁ f₀ g₁ g₀ x y r (p^α)

/- lets lean prove `Fintype {r : (ZMod (p^α : ℕ))ˣ | sol_hFunc (z) (χ) (ψ) (f₁) (f₀) (g₁) (g₀) (x) (y) (r) (q) (h)}`-/
open Classical

def ZMod_sol_hFunc (x y : ℤ) : Finset ℕ :=
  (Finset.range (p^(2*α))).filter (map_sol_hFunc z χ ψ hp f₁ f₀ g₁ g₀ x y)

-- needs some rewriting
/- 
Set.image 
Set.mem_image_of_mem

χ '' {r : (ZMod (p^α : ℕ))ˣ | sol_hFunc (z) (χ) (ψ) (f₁) (f₀) (g₁) (g₀) (x) (y) (r) (q) (h)}
-/

/- previous version
theorem CharSum_in_two_sums (a b x y x₀ : ℤ) (h : x = y + z * (p^α : ℕ)) [NeZero (p^α : ℕ)]:
    CharSum (χ) (ψ) (p^(2*α)) = ∑ x : {r : (ZMod (p^α : ℕ)) | sol_hFunc z χ ψ hp f₁ f₀ g₁ g₀ x y r (p^α)}, (χ x * ψ x * (∑ z₁ : (ZMod (p^α : ℕ)), eZMod (p^α) ((hFunc z₁ χ ψ f₁ f₀ g₁ g₀ x y x₀ (p^α) hp) * z₁))) := by
  simp only [CharSum]
-/

/-
it might be better to define a Finset ℕ equivalent of `{r : (ZMod (p^α : ℕ)) | sol_hFunc z χ ψ hp f₁ f₀ g₁ g₀ x y r (p^α)}` using Finset.filter
Should I do it using the sum over range?
-/ 

/- Previous version using Set instead of Finset
theorem CharSum_in_two_sums (a b x y x₀ : ℤ) (h : x = y + z * (p^α : ℕ)) [NeZero (p^α : ℕ)]:
    CharSum (χ) (ψ) (p^(2*α)) = ∑ x : {r : (ZMod (p^α : ℕ)) | sol_hFunc z χ ψ hp f₁ f₀ g₁ g₀ x y r (p^α)}, (χ x * ψ x * (∑ z₁ : (ZMod (p^α : ℕ)), eZMod (p^α) ((hFunc z₁ χ ψ f₁ f₀ g₁ g₀ x y x₀ (p^α) hp) * z₁))) := by
  sorry
-/

/- previous (wrong) versions
theorem CharSum_in_two_sums (a b x y x₀ : ℤ) (h : x = y + z * (p^α : ℕ)) [NeZero (p^α : ℕ)] :
    CharSum χ ψ f₁ f₀ g₁ g₀ (p^(2*α)) = ∑ r : (ZMod_sol_hFunc z χ ψ hp f₁ f₀ g₁ g₀ x y), (χ (rationalFunc f₁ f₀ r (p^α)) * ψ (rationalFunc g₁ g₀ r (p^α))) * (∑ z₁ : (ZMod (p^α : ℕ)), eZMod (p^α) ((hFunc z₁ χ ψ f₁ f₀ g₁ g₀ x y x₀ (p^α) hp) * z₁)) := by
  rw [CharSum]
  
  sorry

/- inner sum vanishes unless h (y) ≡ 0 (ZMod p^α) -/
-- (hFunc z₁ χ ψ f₁ f₀ g₁ g₀ x y x₀ (p^α) hp)
theorem even_pow_final_formula (x y x₀ : ℤ) (h : x = y + z * (p^α : ℕ)) :
    CharSum χ ψ f₁ f₀ g₁ g₀ (p^(2*α)) = 
    if hFunc z χ ψ f₁ f₀ g₁ g₀ x y x₀ (p^α) hp ≡ 0 [ZMOD p^α] then (p^α : ℕ) * (∑ r : (ZMod (p^α : ℕ))ˣ, χ (rationalFunc f₁ f₀ r (p^α)) * ψ (rationalFunc g₁ g₀ r (p^α)))
    else 0 := by
  sorry
-/

def ZModIsUnit (q : ℕ): ℕ → Prop :=
  fun r => IsUnit (r : ZMod q)

lemma bruh :
    ∑ x : (ZMod (p^(2*α))), χ (rationalFunc f₁ f₀ x (p^(2*α))) * ψ (rationalFunc g₁ g₀ x (p^(2*α))) = ∑ x : (Finset.range (p^(2*α))), χ (rationalFunc f₁ f₀ x (p^(2*α))) * ψ (rationalFunc g₁ g₀ x (p^(2*α))) := by
  sorry

/- rewrite the sum over (ZMod p^(2*α))ˣ to over Finset ℕ -/
/- Goal One -/
lemma CharSum_over_ZMod_to_Range (a b x y x₀ : ℤ) :
    CharSum χ ψ f₁ f₀ g₁ g₀ (p^(2*α)) = ∑ x : (Finset.range (p^(2*α))).filter (ZModIsUnit (p^(2*α))), χ (rationalFunc f₁ f₀ x (p^(2*α))) * ψ (rationalFunc g₁ g₀ x (p^(2*α))) := by
  rw [CharSum]
  
  sorry






theorem CharSum_in_two_sums (a b x y : ℤ) (h : x = y + z * (p^α : ℕ)) [NeZero (p^α : ℕ)] :
    CharSum χ ψ f₁ f₀ g₁ g₀ (p^(2*α)) = ∑ y₀ : (ZMod (p^α))ˣ, (χ (rationalFunc f₁ f₀ y₀ (p^α)) * ψ (rationalFunc g₁ g₀ y₀ (p^α))) * (∑ z₀ : (ZMod (p^α : ℕ)), eZMod (p^α) ((hFunc z χ ψ f₁ f₀ g₁ g₀ x y y₀ (p^α) hp) * z₀)) := by
  rw [CharSum]
  sorry

/- 
inner sum vanishes unless h (y) ≡ 0 [ZMOD p^α] 
By the theorem `Finset.sum_empty` the sum equals zero when h (y) ≡ 0 [ZMOD p^α] has no solution
-/
-- (hFunc z₁ χ ψ f₁ f₀ g₁ g₀ x y x₀ (p^α) hp)
theorem even_pow_final_formula (x y x₀ : ℤ) (h : x = y + z * (p^α : ℕ)) :
    CharSum χ ψ f₁ f₀ g₁ g₀ (p^(2*α)) = (p^α : ℕ) * (∑ r : (ZMod_sol_hFunc z χ ψ hp f₁ f₀ g₁ g₀ x y), χ (rationalFunc f₁ f₀ r (p^α)) * ψ (rationalFunc g₁ g₀ r (p^α))) := by
  sorry



/- # Strategy
1. Show that the Finset created by the variable `x : (ZMod (p^(2*α)))ˣ` and the Finset of `y + z * p^α` generated by `y : (ZMod p^α)ˣ` and `z : ZMod p^α`
2. To achieve Goal 1, need to show that the sum over the Finset generated by `x : (ZMod (p^(2*α)))ˣ` is equal to the sum over `x : (ZMod (p^(2*α)))ˣ`
   Show something similar for the sum over the Finset of `y + z * p^α`
3. 


-/












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
