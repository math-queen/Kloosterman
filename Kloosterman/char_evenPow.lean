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

/- change the name later -/
theorem MulChar_additive_eq_exp_for_all (p : ℕ) (hp : Prime p) (α : ℕ) (χ : MulChar (ZMod (p^(2*α) : ℕ)) ℂ) :
    ∃(b : ℕ), b < p^α ∧ ∀(z : ZMod (p^α : ℕ)), χ' (χ) (z) = eZMod (p^α : ℕ) (b*z) := by
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
  use b
  apply And.intro (hb.left)
  intro z
  rw [← MulChar_additive_pow_val]
  have hb_pow := pow (z.val) (hb.right)
  norm_cast at hb_pow
  rw [← Complex.exp_nat_mul] at hb_pow

  simp only [eZMod]
  have congr_val : ((b : ZMod (p^α : ℕ)) * z).val ≡ (b : ZMod (p^α)).val * z.val [ZMOD (p^α)]
  { rw [ZMod.val_mul (↑b) z]
    exact Int.mod_modEq ((b : ZMod (p^α)).val * ZMod.val z) (p ^ α) }

  have new_NeZero : p^α ≠ 0 := by exact NeZero.ne (p^α)
  have val_b : (b : ZMod (p^α)).val ≡ b [ZMOD (p^α)]
  { simp only [Nat.cast_pow, ZMod.nat_cast_val]
    norm_cast
    rw [← ZMod.int_cast_eq_int_cast_iff]
    simp  }
  rw [cexp_congr_eq (p^α : ℕ) (((b : ZMod (p^α : ℕ)) * z).val) ((b : ZMod (p^α)).val * z.val)]
  · have congr_b : (b : ZMod (p^α)).val * z.val ≡ b * z.val [ZMOD (p^α)] := by gcongr
    -- simp at congr_b ⊢
    rw [cexp_congr_eq (p^α : ℕ) ((b : ZMod (p^α)).val * z.val) (b * z.val)]
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