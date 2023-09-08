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

variable {p α : ℕ} (χ : MulChar (ZMod (p ^ (2 * α))) ℂ) (ψ : AddChar (ZMod (p ^ (2 * α))) ℂ)
-- (q : ℕ) (x : ZMod q) (y : ℤ) (z : ZMod q)

variable (f₁ f₀ g₁ g₀ : Polynomial ℤ) (hα : 0 < α) [pp : Fact p.Prime]

instance : NeZero p := NeZero.of_gt'

instance : NeZero (p ^ α) := by exact NeZero.pow

instance : NeZero (p ^ (2 * α)) := by exact NeZero.pow

open Polynomial

theorem support_nonempty_iff_nonZero_polynomial (p₀ : Polynomial ℤ) (y : ℤ) : (taylor y p₀).support.Nonempty ↔ p₀ ≠ C 0 := by
  apply Iff.intro
  · contrapose!
    rw [nonempty_support_iff]
    rw [ne_eq, not_not, map_zero]
    intro hp₀
    rw [hp₀]
    rw [map_zero]
    -- exact LinearMap.map_zero (taylor y)
  · contrapose!
    rw [nonempty_support_iff]
    rw [ne_eq, not_not]
    rw [map_zero]
    rw [taylor_apply]
    intro hp₀
    rw [← zero_comp (p := X + C y)] at hp₀
    rw [← taylor_apply] at hp₀
    rw [← taylor_apply] at hp₀
    exact (taylor_injective y) hp₀

/- all these theorems for the case when f and g are the constant funciton-/