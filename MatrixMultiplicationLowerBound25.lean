import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Field.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.NormNum

/-!
# Theorem 1: R_K(<3,2,m>) > 24m/5 over every field, for m > 0

Pinned environment: Lean 4.19.0; mathlib v4.19.0.
Main theorem: MatrixMultiplicationLowerBound.theorem_one_rational.
Equivalent integer form: MatrixMultiplicationLowerBound.theorem_one.
Arbitrary-decomposition form: MatrixMultiplicationLowerBound.matrix_algorithm_rank_strict.
-/

/-! ## Decomposition -/
/-! Coordinatewise model of exact bilinear algorithms for (3,2,m)
matrix multiplication.  A is represented by its two columns and B by
its two rows.  The intermediate space K^r stores the r products. -/

namespace MatrixMultiplicationLowerBound

variable {mcols : ℕ}

abbrev Col (K : Type*) := Fin 3 → K
abbrev Row (K : Type*) (mcols : ℕ) := Fin mcols → K
abbrev LeftInput (K : Type*) := Col K × Col K
abbrev RightInput (K : Type*) (mcols : ℕ) := Row K mcols × Row K mcols
abbrev Output (K : Type*) (mcols : ℕ) := Fin 3 → Row K mcols
abbrev Products (K : Type*) (r : ℕ) := Fin r → K

variable {K : Type*} [Field K]

def matrixMul (a : LeftInput K) (b : RightInput K mcols) : Output K mcols :=
  fun i j => a.1 i * b.1 j + a.2 i * b.2 j

/-- An exact algorithm using r scalar products of linear forms. -/
structure Decomposition (K : Type*) [Field K] (mcols r : ℕ) where
  alpha : LeftInput K →ₗ[K] Products K r
  beta : RightInput K mcols →ₗ[K] Products K r
  output : Products K r →ₗ[K] Output K mcols
  correct : ∀ a b, output (alpha a * beta b) = matrixMul a b

noncomputable def diag {r : ℕ} (s : Products K r) :
    Products K r →ₗ[K] Products K r where
  toFun v := s * v
  map_add' v w := mul_add s v w
  map_smul' c v := by ext i; simp [mul_left_comm]

@[simp] theorem diag_apply {r : ℕ} (s v : Products K r) : diag s v = s * v := rfl

theorem diag_commute {r : ℕ} (s t : Products K r) (v : Products K r) :
    diag s (diag t v) = diag t (diag s v) := by
  ext i
  simp [mul_left_comm]

def rowInsert (i : Fin 3) : Row K mcols →ₗ[K] Output K mcols where
  toFun v := fun k => if k = i then v else 0
  map_add' v w := by ext k j; by_cases h : k = i <;> simp [h]
  map_smul' c v := by ext k j; by_cases h : k = i <;> simp [h]

def colUnit (i : Fin 3) : Col K := Pi.single i 1

def firstRow : Row K mcols →ₗ[K] RightInput K mcols :=
  LinearMap.inl K (Row K mcols) (Row K mcols)

def secondRow : Row K mcols →ₗ[K] RightInput K mcols :=
  LinearMap.inr K (Row K mcols) (Row K mcols)

@[simp] theorem matrixMul_first (i : Fin 3) (v : Row K mcols) :
    matrixMul (colUnit i, 0) (v, 0) = rowInsert i v := by
  ext k j
  by_cases h : k = i <;> simp [matrixMul, colUnit, rowInsert, Pi.single_apply, h]

@[simp] theorem matrixMul_second (i : Fin 3) (v : Row K mcols) :
    matrixMul (0, colUnit i) (0, v) = rowInsert i v := by
  ext k j
  by_cases h : k = i <;> simp [matrixMul, colUnit, rowInsert, Pi.single_apply, h]

@[simp] theorem matrixMul_cross (i : Fin 3) (v : Row K mcols) :
    matrixMul (colUnit i, 0) (0, v) = 0 := by
  ext k j
  simp [matrixMul]

theorem row_independent (a v w : Row K mcols)
    (h : rowInsert (0 : Fin 3) a = rowInsert 1 v + rowInsert 2 w) :
    v = 0 ∧ w = 0 := by
  constructor
  · have hv := congrFun h (1 : Fin 3)
    simpa [rowInsert] using hv.symm
  · have hw := congrFun h (2 : Fin 3)
    simpa [rowInsert] using hw.symm

namespace Decomposition

variable {r : ℕ} (D : Decomposition K mcols r)

theorem beta_injective : Function.Injective D.beta := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro b hb
  have hc (a : LeftInput K) : matrixMul a b = 0 := by
    rw [← D.correct, hb, mul_zero, map_zero]
  apply Prod.ext
  · ext j
    have h := congrFun (congrFun (hc (colUnit 0, 0)) (0 : Fin 3)) j
    simpa [matrixMul, colUnit, Pi.single_apply] using h
  · ext j
    have h := congrFun (congrFun (hc (0, colUnit 0)) (0 : Fin 3)) j
    simpa [matrixMul, colUnit, Pi.single_apply] using h

theorem output_surjective : Function.Surjective D.output := by
  intro o
  refine ⟨∑ i : Fin 3, D.alpha (colUnit i, 0) * D.beta (o i, 0), ?_⟩
  simp only [map_sum, D.correct, matrixMul_first]
  ext i j
  simp [rowInsert, ite_apply, eq_comm]

def X : Row K mcols →ₗ[K] Products K r := D.beta.comp firstRow
def Y : Row K mcols →ₗ[K] Products K r := D.beta.comp secondRow

theorem Y_injective : Function.Injective D.Y := by
  intro v w h
  have hh := D.beta_injective h
  exact congrArg Prod.snd hh

def s : Products K r := D.alpha (colUnit 1, 0)
def t : Products K r := D.alpha (colUnit 2, 0)
def z : Products K r := D.alpha (0, colUnit 0)

theorem output_X (h : D.alpha (colUnit 0, 0) = 1) (v : Row K mcols) :
    D.output (D.X v) = rowInsert 0 v := by
  have hh := D.correct (colUnit 0, 0) (v, 0)
  simpa [h, X, firstRow] using hh

theorem output_Y (h : D.alpha (colUnit 0, 0) = 1) (v : Row K mcols) :
    D.output (D.Y v) = 0 := by
  have hh := D.correct (colUnit 0, 0) (0, v)
  simpa [h, Y, secondRow] using hh

theorem output_sX (v : Row K mcols) :
    D.output (diag D.s (D.X v)) = rowInsert 1 v := by
  simpa [diag, s, X, firstRow] using D.correct (colUnit 1, 0) (v, 0)

theorem output_tX (v : Row K mcols) :
    D.output (diag D.t (D.X v)) = rowInsert 2 v := by
  simpa [diag, t, X, firstRow] using D.correct (colUnit 2, 0) (v, 0)

theorem output_sY (v : Row K mcols) : D.output (diag D.s (D.Y v)) = 0 := by
  simpa [diag, s, Y, secondRow] using D.correct (colUnit 1, 0) (0, v)

theorem output_tY (v : Row K mcols) : D.output (diag D.t (D.Y v)) = 0 := by
  simpa [diag, t, Y, secondRow] using D.correct (colUnit 2, 0) (0, v)

theorem output_zY (v : Row K mcols) :
    D.output (diag D.z (D.Y v)) = rowInsert 0 v := by
  simpa [diag, z, Y, secondRow] using D.correct (0, colUnit 0) (0, v)

end Decomposition
end MatrixMultiplicationLowerBound


/-! ## CoordinateChange -/
namespace MatrixMultiplicationLowerBound

variable {mcols : ℕ}

variable {K : Type*} [Field K]

def shearCol (w : Col K) : Col K →ₗ[K] Col K where
  toFun u i := u i + w i * u 0
  map_add' u v := by ext i; simp; ring
  map_smul' c u := by ext i; simp; ring

def shearLeft (t : K) (w : Col K) : LeftInput K →ₗ[K] LeftInput K where
  toFun a := (shearCol w a.1, t • shearCol w a.1 + shearCol w a.2)
  map_add' a b := by ext i <;> simp [shearCol] <;> ring
  map_smul' c a := by ext i <;> simp [shearCol] <;> ring

def shearRight (t : K) : RightInput K mcols →ₗ[K] RightInput K mcols where
  toFun b := (b.1 - t • b.2, b.2)
  map_add' a b := by ext i <;> simp <;> ring
  map_smul' c b := by ext i <;> simp <;> ring

def unshearOutput (w : Col K) : Output K mcols →ₗ[K] Output K mcols where
  toFun o i j := o i j - w i * o 0 j
  map_add' o p := by ext i j; simp; ring
  map_smul' c o := by ext i j; simp; ring

theorem change_matrixMul (t : K) (w : Col K) (hw : w 0 = 0)
    (a : LeftInput K) (b : RightInput K mcols) :
    unshearOutput w (matrixMul (shearLeft t w a) (shearRight t b)) =
      matrixMul a b := by
  ext i j
  simp [unshearOutput, shearLeft, shearRight, shearCol, matrixMul, hw]
  ring

namespace Decomposition

variable {r : ℕ} (D : Decomposition K mcols r)

/-- Replace unused zero first forms by a fixed nonzero form, with the
corresponding second form set to zero. The number of products is unchanged. -/
noncomputable def removeZeroForms : Decomposition K mcols r := by
  classical
  let active (i : Fin r) : Prop := ∃ a, D.alpha a i ≠ 0
  refine
    { alpha :=
        { toFun := fun a i => if active i then D.alpha a i else a.1 0
          map_add' := ?_
          map_smul' := ?_ }
      beta :=
        { toFun := fun b i => if active i then D.beta b i else 0
          map_add' := ?_
          map_smul' := ?_ }
      output := D.output
      correct := ?_ }
  · intro a b; ext i; by_cases h : active i <;> simp [h]
  · intro c a; ext i; by_cases h : active i <;> simp [h]
  · intro a b; ext i; by_cases h : active i <;> simp [h]
  · intro c a; ext i; by_cases h : active i <;> simp [h]
  · intro a b
    have heq : (fun i => if active i then D.alpha a i else a.1 0) *
        (fun i => if active i then D.beta b i else 0) = D.alpha a * D.beta b := by
      ext i
      by_cases h : active i
      · simp [h]
      · have ha : D.alpha a i = 0 := by
          by_contra ha
          exact h ⟨a, ha⟩
        simp [h, ha]
    change D.output ((fun i => if active i then D.alpha a i else a.1 0) *
        (fun i => if active i then D.beta b i else 0)) = _
    rw [heq]
    exact D.correct a b

theorem removeZeroForms_nonzero (i : Fin r) :
    ∃ a, D.removeZeroForms.alpha a i ≠ 0 := by
  classical
  by_cases h : ∃ a, D.alpha a i ≠ 0
  · obtain ⟨a, ha⟩ := h
    refine ⟨a, ?_⟩
    change (if ∃ b, D.alpha b i ≠ 0 then D.alpha a i else a.1 0) ≠ 0
    rw [if_pos (show ∃ b, D.alpha b i ≠ 0 from ⟨a, ha⟩)]
    exact ha
  · refine ⟨(colUnit 0, 0), ?_⟩
    change (if ∃ b, D.alpha b i ≠ 0 then D.alpha (colUnit 0, 0) i else colUnit 0 0) ≠ 0
    rw [if_neg h]
    simp [colUnit, Pi.single_apply]

/-- Triangular changes of matrix coordinates, preserving exact multiplication. -/
def changeCoordinates (t : K) (w : Col K) (hw : w 0 = 0) : Decomposition K mcols r where
  alpha := D.alpha.comp (shearLeft t w)
  beta := D.beta.comp (shearRight t)
  output := (unshearOutput w).comp D.output
  correct a b := by
    change unshearOutput w (D.output (D.alpha (shearLeft t w a) *
      D.beta (shearRight t b))) = _
    rw [D.correct]
    exact change_matrixMul t w hw a b

/-- Inverse rescaling of the two input forms at each product coordinate. -/
noncomputable def rescale (c : Products K r) (hc : ∀ i, c i ≠ 0) : Decomposition K mcols r where
  alpha := (diag (fun i => (c i)⁻¹)).comp D.alpha
  beta := (diag c).comp D.beta
  output := D.output
  correct a b := by
    change D.output (((fun i => (c i)⁻¹) * D.alpha a) * (c * D.beta b)) = _
    have h : ((fun i => (c i)⁻¹) * D.alpha a) * (c * D.beta b) =
        D.alpha a * D.beta b := by
      ext i
      change ((c i)⁻¹ * D.alpha a i) * (c i * D.beta b i) = _
      calc
        _ = ((c i)⁻¹ * c i) * (D.alpha a i * D.beta b i) := by ring
        _ = _ := by rw [inv_mul_cancel₀ (hc i), one_mul]; rfl
    rw [h]
    exact D.correct a b

@[simp] theorem changeCoordinates_alpha (t : K) (w : Col K) (hw : w 0 = 0)
    (a : LeftInput K) :
    (D.changeCoordinates t w hw).alpha a = D.alpha (shearLeft t w a) := rfl

@[simp] theorem rescale_alpha (c : Products K r) (hc : ∀ i, c i ≠ 0)
    (a : LeftInput K) (i : Fin r) :
    (D.rescale c hc).alpha a i = (c i)⁻¹ * D.alpha a i := rfl

theorem rescale_normalized (c : Products K r) (hc : ∀ i, c i ≠ 0)
    (he : D.alpha (colUnit 0, 0) = c) :
    (D.rescale c hc).alpha (colUnit 0, 0) = 1 := by
  ext i
  rw [rescale_alpha, he]
  exact inv_mul_cancel₀ (hc i)

end Decomposition
end MatrixMultiplicationLowerBound


/-! ## InvariantKernel -/
/-!
# The invariant-kernel step in the matrix multiplication lower-bound argument

This file isolates the algebraic equality-case argument.  The projection `q`
may be the quotient map `E → E / range Y`.  Neither finite dimensionality nor
injectivity of `Y` is needed for this step.
-/

namespace MatrixMultiplicationLowerBound

variable {mcols : ℕ}

section

variable {K V E Q : Type*} [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup E] [Module K E]
variable [AddCommGroup Q] [Module K Q]

/-- The lifting argument with only maps on the subspace where the quotient is
defined.  Here `hlift₁`, `hlift₂`, and `hcompatible` are immediate properties of
the quotient `(ker W) / range Y` in the matrix multiplication application. -/
theorem common_kernel_lifts_abstract
    (Y : V →ₗ[K] E) (S T : E →ₗ[K] E) (p₁ p₂ : V →ₗ[K] Q)
    (hlift₁ : ∀ x, p₁ x = 0 → ∃ u, Y u = S (Y x))
    (hlift₂ : ∀ x, p₂ x = 0 → ∃ v, Y v = T (Y x))
    (hcompatible : ∀ u v, S (Y u) = T (Y v) → p₁ u = p₂ v)
    (hcomm : ∀ e, S (T e) = T (S e))
    (hker : ∀ v, p₁ v = 0 ↔ p₂ v = 0)
    (hsep : ∀ u v, p₁ u = p₂ v → p₁ u = 0)
    {x : V} (hx : p₁ x = 0) :
    ∃ u v, p₁ u = 0 ∧ p₁ v = 0 ∧
      S (Y x) = Y u ∧ T (Y x) = Y v := by
  obtain ⟨u, hu⟩ := hlift₁ x hx
  obtain ⟨v, hv⟩ := hlift₂ x ((hker x).mp hx)
  have huv : p₁ v = p₂ u := by
    apply hcompatible
    rw [hv, hu, hcomm]
  have hv₀ : p₁ v = 0 := hsep v u huv
  have hu₂ : p₂ u = 0 := huv.symm.trans hv₀
  exact ⟨u, v, (hker u).mpr hu₂, hv₀, hu.symm, hv.symm⟩

/-- The invariant-submodule conclusion using a quotient defined only on a
subspace of the coefficient space. -/
theorem common_kernel_image_invariant_abstract
    (Y : V →ₗ[K] E) (S T : E →ₗ[K] E) (p₁ p₂ : V →ₗ[K] Q)
    (hlift₁ : ∀ x, p₁ x = 0 → ∃ u, Y u = S (Y x))
    (hlift₂ : ∀ x, p₂ x = 0 → ∃ v, Y v = T (Y x))
    (hcompatible : ∀ u v, S (Y u) = T (Y v) → p₁ u = p₂ v)
    (hcomm : ∀ e, S (T e) = T (S e))
    (hker : LinearMap.ker p₁ = LinearMap.ker p₂)
    (hdisjoint : Disjoint (LinearMap.range p₁) (LinearMap.range p₂)) :
    (∀ e ∈ Submodule.map Y (LinearMap.ker p₁),
      S e ∈ Submodule.map Y (LinearMap.ker p₁)) ∧
    (∀ e ∈ Submodule.map Y (LinearMap.ker p₁),
      T e ∈ Submodule.map Y (LinearMap.ker p₁)) := by
  have hker' : ∀ v, p₁ v = 0 ↔ p₂ v = 0 := by
    intro v
    change v ∈ LinearMap.ker p₁ ↔ v ∈ LinearMap.ker p₂
    rw [hker]
  have hsep : ∀ u v, p₁ u = p₂ v → p₁ u = 0 := by
    intro u v huv
    have hm : p₁ u ∈ LinearMap.range p₁ ⊓ LinearMap.range p₂ :=
      ⟨⟨u, rfl⟩, ⟨v, huv.symm⟩⟩
    have hi : LinearMap.range p₁ ⊓ LinearMap.range p₂ = ⊥ :=
      disjoint_iff.mp hdisjoint
    rw [hi] at hm
    exact hm
  constructor
  · intro e he
    obtain ⟨x, hx, rfl⟩ := he
    obtain ⟨u, v, hu, hv, hSu, hTv⟩ :=
      common_kernel_lifts_abstract Y S T p₁ p₂
        hlift₁ hlift₂ hcompatible hcomm hker' hsep hx
    exact ⟨u, hu, hSu.symm⟩
  · intro e he
    obtain ⟨x, hx, rfl⟩ := he
    obtain ⟨u, v, hu, hv, hSu, hTv⟩ :=
      common_kernel_lifts_abstract Y S T p₁ p₂
        hlift₁ hlift₂ hcompatible hcomm hker' hsep hx
    exact ⟨v, hv, hTv.symm⟩

/-- The elementary form of the invariant-kernel argument.  A pair of commuting
operators that send the common kernel into `range Y` in fact send it into the
image of the common kernel, provided the two induced maps have separated
ranges.  The separation assumption follows from disjoint linear-map ranges. -/
theorem common_kernel_lifts
    (Y : V →ₗ[K] E) (S T : E →ₗ[K] E) (q : E →ₗ[K] Q)
    (p₁ p₂ : V →ₗ[K] Q)
    (hq : ∀ e, q e = 0 ↔ ∃ v, Y v = e)
    (hp₁ : ∀ v, p₁ v = q (S (Y v)))
    (hp₂ : ∀ v, p₂ v = q (T (Y v)))
    (hcomm : ∀ e, S (T e) = T (S e))
    (hker : ∀ v, p₁ v = 0 ↔ p₂ v = 0)
    (hsep : ∀ u v, p₁ u = p₂ v → p₁ u = 0)
    {x : V} (hx : p₁ x = 0) :
    ∃ u v, p₁ u = 0 ∧ p₁ v = 0 ∧
      S (Y x) = Y u ∧ T (Y x) = Y v := by
  have hx₂ : p₂ x = 0 := (hker x).mp hx
  obtain ⟨u, hu⟩ := (hq (S (Y x))).mp ((hp₁ x).symm.trans hx)
  obtain ⟨v, hv⟩ := (hq (T (Y x))).mp ((hp₂ x).symm.trans hx₂)
  have huv : p₁ v = p₂ u := by
    rw [hp₁, hp₂, hv, hu, hcomm]
  have hv₀ : p₁ v = 0 := hsep v u huv
  have hu₂ : p₂ u = 0 := huv.symm.trans hv₀
  exact ⟨u, v, (hker u).mpr hu₂, hv₀, hu.symm, hv.symm⟩

/-- A coordinate-free statement of the equality-case invariant-subspace step.
The submodule `Y(ker p₁)` is stable under each of `S` and `T`. -/
theorem common_kernel_image_invariant
    (Y : V →ₗ[K] E) (S T : E →ₗ[K] E) (q : E →ₗ[K] Q)
    (p₁ p₂ : V →ₗ[K] Q)
    (hq : LinearMap.ker q = LinearMap.range Y)
    (hp₁ : p₁ = q.comp (S.comp Y))
    (hp₂ : p₂ = q.comp (T.comp Y))
    (hcomm : ∀ e, S (T e) = T (S e))
    (hker : LinearMap.ker p₁ = LinearMap.ker p₂)
    (hdisjoint : Disjoint (LinearMap.range p₁) (LinearMap.range p₂)) :
    (∀ e ∈ Submodule.map Y (LinearMap.ker p₁),
      S e ∈ Submodule.map Y (LinearMap.ker p₁)) ∧
    (∀ e ∈ Submodule.map Y (LinearMap.ker p₁),
      T e ∈ Submodule.map Y (LinearMap.ker p₁)) := by
  have hq' : ∀ e, q e = 0 ↔ ∃ v, Y v = e := by
    intro e
    change e ∈ LinearMap.ker q ↔ e ∈ LinearMap.range Y
    rw [hq]
  have hker' : ∀ v, p₁ v = 0 ↔ p₂ v = 0 := by
    intro v
    change v ∈ LinearMap.ker p₁ ↔ v ∈ LinearMap.ker p₂
    rw [hker]
  have hsep : ∀ u v, p₁ u = p₂ v → p₁ u = 0 := by
    intro u v huv
    have hm : p₁ u ∈ LinearMap.range p₁ ⊓ LinearMap.range p₂ := by
      exact ⟨⟨u, rfl⟩, ⟨v, huv.symm⟩⟩
    have hi : LinearMap.range p₁ ⊓ LinearMap.range p₂ = ⊥ :=
      disjoint_iff.mp hdisjoint
    rw [hi] at hm
    exact hm
  have hlift : ∀ x, p₁ x = 0 →
      ∃ u v, p₁ u = 0 ∧ p₁ v = 0 ∧
        S (Y x) = Y u ∧ T (Y x) = Y v := by
    intro x hx
    exact common_kernel_lifts Y S T q p₁ p₂ hq'
      (by intro v; rw [hp₁]; rfl)
      (by intro v; rw [hp₂]; rfl)
      hcomm hker' hsep hx
  constructor
  · intro e he
    obtain ⟨x, hx, rfl⟩ := he
    obtain ⟨u, v, hu, hv, hSu, hTv⟩ := hlift x hx
    exact ⟨u, hu, hSu.symm⟩
  · intro e he
    obtain ⟨x, hx, rfl⟩ := he
    obtain ⟨u, v, hu, hv, hSu, hTv⟩ := hlift x hx
    exact ⟨v, hv, hTv.symm⟩

end

end MatrixMultiplicationLowerBound


/-! ## PaperInjection -/
/-!
# The injection underlying the rectangular matrix multiplication bound

The proof is written as an algebraic lifting lemma, so the quotient can be
taken only on `ker W`.  In particular, no extension of a quotient projection
from `ker W` to the coefficient space is necessary.
-/

namespace MatrixMultiplicationLowerBound

variable {mcols : ℕ}

section

variable {K V E O : Type*} [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup E] [Module K E]
variable [AddCommGroup O] [Module K O]

/-- The kernel computation used in Yang's dimension argument.  The three
equations are exactly the vanishing of the three components of the quotient
map after lifting them to the coefficient space. -/
theorem paper_injection_lifting
    (X Y μ : V →ₗ[K] E) (S T Z : E →ₗ[K] E)
    (W : E →ₗ[K] O) (e₀ e₁ e₂ : V →ₗ[K] O)
    (hμ : ∀ v, μ v = Z (Y v) - X v)
    (hZS : ∀ x, Z (S x) = S (Z x))
    (hZT : ∀ x, Z (T x) = T (Z x))
    (hST : ∀ x, S (T x) = T (S x))
    (hWZY : ∀ v, W (Z (Y v)) = e₀ v)
    (hWSY : ∀ v, W (S (Y v)) = 0)
    (hWTY : ∀ v, W (T (Y v)) = 0)
    (hWSX : ∀ v, W (S (X v)) = e₁ v)
    (hWTX : ∀ v, W (T (X v)) = e₂ v)
    (hrows : ∀ a v w, e₀ a = e₁ v + e₂ w → v = 0 ∧ w = 0)
    (v w c a b d : V)
    (ha : S (Y v) + T (Y w) = Y a)
    (hb : -μ v + T (Y c) = Y b)
    (hd : -μ w - S (Y c) = Y d) : v = 0 ∧ w = 0 := by
  have hid :
      Z (S (Y v) + T (Y w)) +
        S (-μ v + T (Y c)) + T (-μ w - S (Y c)) =
      S (X v) + T (X w) := by
    simp only [map_add, map_sub, map_neg, hμ, hZS, hZT, hST]
    abel
  apply hrows a v w
  calc
    e₀ a = W (Z (Y a) + S (Y b) + T (Y d)) := by
      simp only [map_add, hWZY, hWSY, hWTY, add_zero]
    _ = W (S (X v) + T (X w)) := by rw [← ha, ← hb, ← hd, hid]
    _ = e₁ v + e₂ w := by rw [map_add, hWSX, hWTX]

/-- Version with an arbitrary quotient space: it suffices to supply the three
lifting properties of quotient equality. These properties hold for the
quotient `(ker W) / range Y`. -/
theorem paper_injection_kernel
    {Q : Type*} [AddCommGroup Q] [Module K Q]
    (X Y μ : V →ₗ[K] E) (S T Z : E →ₗ[K] E)
    (W : E →ₗ[K] O) (e₀ e₁ e₂ : V →ₗ[K] O)
    (p₁ p₂ m : V →ₗ[K] Q)
    (hμ : ∀ v, μ v = Z (Y v) - X v)
    (hZS : ∀ x, Z (S x) = S (Z x))
    (hZT : ∀ x, Z (T x) = T (Z x))
    (hST : ∀ x, S (T x) = T (S x))
    (hWZY : ∀ v, W (Z (Y v)) = e₀ v)
    (hWSY : ∀ v, W (S (Y v)) = 0)
    (hWTY : ∀ v, W (T (Y v)) = 0)
    (hWSX : ∀ v, W (S (X v)) = e₁ v)
    (hWTX : ∀ v, W (T (X v)) = e₂ v)
    (hrows : ∀ a v w, e₀ a = e₁ v + e₂ w → v = 0 ∧ w = 0)
    (hlift₀ : ∀ v w, p₁ v + p₂ w = 0 →
      ∃ a, S (Y v) + T (Y w) = Y a)
    (hlift₁ : ∀ v c, -m v + p₂ c = 0 →
      ∃ b, -μ v + T (Y c) = Y b)
    (hlift₂ : ∀ w c, -m w - p₁ c = 0 →
      ∃ d, -μ w - S (Y c) = Y d)
    (v w c : V)
    (h₀ : p₁ v + p₂ w = 0)
    (h₁ : -m v + p₂ c = 0)
    (h₂ : -m w - p₁ c = 0) : v = 0 ∧ w = 0 := by
  obtain ⟨a, ha⟩ := hlift₀ v w h₀
  obtain ⟨b, hb⟩ := hlift₁ v c h₁
  obtain ⟨d, hd⟩ := hlift₂ w c h₂
  exact paper_injection_lifting X Y μ S T Z W e₀ e₁ e₂
    hμ hZS hZT hST hWZY hWSY hWTY hWSX hWTX hrows
    v w c a b d ha hb hd

end

end MatrixMultiplicationLowerBound


/-! ## QuotientBridge -/
/-!
# Quotient maps used by the lower-bound argument

Here `H` denotes the kernel of the output map, `Y : V → H` is the map coming
from the second input row, and the quotient is `H / range Y`.
-/

namespace MatrixMultiplicationLowerBound

variable {mcols : ℕ}

section

variable {K V H : Type*} [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup H] [Module K H]

/-- Project a map into `H` to the quotient by the image of `Y`. -/
noncomputable def rangeQuotientMap (Y A : V →ₗ[K] H) :
    V →ₗ[K] H ⧸ LinearMap.range Y :=
  (LinearMap.range Y).mkQ.comp A

@[simp]
theorem rangeQuotientMap_apply (Y A : V →ₗ[K] H) (v : V) :
    rangeQuotientMap Y A v = (LinearMap.range Y).mkQ (A v) := rfl

theorem range_quotient_zero_iff (Y : V →ₗ[K] H) (x : H) :
    (LinearMap.range Y).mkQ x = 0 ↔ ∃ v, Y v = x := by
  change (Submodule.Quotient.mk x : H ⧸ LinearMap.range Y) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

@[simp]
theorem rangeQuotientMap_eq_zero_iff (Y A : V →ₗ[K] H) (v : V) :
    rangeQuotientMap Y A v = 0 ↔ ∃ u, Y u = A v :=
  range_quotient_zero_iff Y (A v)

theorem rangeQuotientMap_compatible
    (Y A B : V →ₗ[K] H) {u v : V} (h : A u = B v) :
    rangeQuotientMap Y A u = rangeQuotientMap Y B v := by
  simp only [rangeQuotientMap_apply, h]

/-- Lift the first component of the injection to the image of `Y`. -/
theorem rangeQuotientMap_lift_add
    (Y A B : V →ₗ[K] H) (v w : V)
    (h : rangeQuotientMap Y A v + rangeQuotientMap Y B w = 0) :
    ∃ a, A v + B w = Y a := by
  have hz : (LinearMap.range Y).mkQ (A v + B w) = 0 := by
    simpa only [map_add, rangeQuotientMap_apply] using h
  obtain ⟨a, ha⟩ := (range_quotient_zero_iff Y _).mp hz
  exact ⟨a, ha.symm⟩

/-- Lift the second component of the injection to the image of `Y`. -/
theorem rangeQuotientMap_lift_neg_add
    (Y A B : V →ₗ[K] H) (v w : V)
    (h : -rangeQuotientMap Y A v + rangeQuotientMap Y B w = 0) :
    ∃ a, -A v + B w = Y a := by
  have hz : (LinearMap.range Y).mkQ (-A v + B w) = 0 := by
    simpa only [map_add, map_neg, rangeQuotientMap_apply] using h
  obtain ⟨a, ha⟩ := (range_quotient_zero_iff Y _).mp hz
  exact ⟨a, ha.symm⟩

/-- Lift the third component of the injection to the image of `Y`. -/
theorem rangeQuotientMap_lift_neg_sub
    (Y A B : V →ₗ[K] H) (v w : V)
    (h : -rangeQuotientMap Y A v - rangeQuotientMap Y B w = 0) :
    ∃ a, -A v - B w = Y a := by
  have hz : (LinearMap.range Y).mkQ (-A v - B w) = 0 := by
    simpa only [map_sub, map_neg, rangeQuotientMap_apply] using h
  obtain ⟨a, ha⟩ := (range_quotient_zero_iff Y _).mp hz
  exact ⟨a, ha.symm⟩

end

end MatrixMultiplicationLowerBound


/-! ## DimensionRigidity -/
/-! Dimension rigidity at equality, uniformly in the input-row dimension. -/

namespace MatrixMultiplicationLowerBound

variable {mcols : ℕ}

open Module LinearMap Submodule

/-- Equality in the dimension estimate, uniformly in the input-row dimension. -/
theorem equality_case_arithmetic
    (v q n s a b k₁ k₂ : ℕ)
    (hq : 5 * q ≤ 4 * v) (hmain : 3 * v ≤ n + s + 2 * q)
    (hn₁ : n ≤ k₁) (hn₂ : n ≤ k₂)
    (hr₁ : a + k₁ = v) (hr₂ : b + k₂ = v)
    (hs : s ≤ a + b) (hsq : s ≤ q) :
    5 * n = 3 * v ∧ n = k₁ ∧ n = k₂ ∧ s = a + b := by
  omega

variable {K V Q : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]

/-- The dimension bound from the three equations in the commuting-diagonal
argument.  The first two variables vanish in their simultaneous kernel. -/
theorem three_equation_dimension_bound
    (p₁ p₂ m : V →ₗ[K] Q)
    (hkernel : ∀ v w c : V,
      p₁ v + p₂ w = 0 → -m v + p₂ c = 0 → -m w - p₁ c = 0 →
      v = 0 ∧ w = 0) :
    3 * finrank K V ≤ finrank K ↥((LinearMap.ker p₁) ⊓ (LinearMap.ker p₂)) +
      finrank K ↥((LinearMap.range p₁) ⊔ (LinearMap.range p₂)) + 2 * finrank K Q := by
  let U : Submodule K Q := (LinearMap.range p₁) ⊔ (LinearMap.range p₂)
  let φ : (V × V × V) →ₗ[K] (U × Q × Q) :=
    { toFun := fun z =>
        (⟨p₁ z.1 + p₂ z.2.1,
          Submodule.add_mem U
            ((show (LinearMap.range p₁) ≤ U from le_sup_left) ⟨z.1, rfl⟩)
            ((show (LinearMap.range p₂) ≤ U from le_sup_right) ⟨z.2.1, rfl⟩)⟩,
          -m z.1 + p₂ z.2.2, -m z.2.1 - p₁ z.2.2)
      map_add' := by
        intro x y
        ext <;> simp <;> abel
      map_smul' := by
        intro a x
        ext <;> simp [smul_add, smul_sub] }
  have hz (z : (LinearMap.ker φ)) : z.val.1 = 0 ∧ z.val.2.1 = 0 := by
    have heq : φ z.val = 0 := z.property
    apply hkernel z.val.1 z.val.2.1 z.val.2.2
    · exact congrArg (fun t : U × Q × Q => t.1.val) heq
    · exact congrArg (fun t : U × Q × Q => t.2.1) heq
    · exact congrArg (fun t : U × Q × Q => t.2.2) heq
  have hc (z : (LinearMap.ker φ)) : z.val.2.2 ∈ (LinearMap.ker p₁) ⊓ (LinearMap.ker p₂) := by
    have heq : φ z.val = 0 := z.property
    have h₁ := congrArg (fun t : U × Q × Q => t.2.1) heq
    have h₂ := congrArg (fun t : U × Q × Q => t.2.2) heq
    change -m z.val.1 + p₂ z.val.2.2 = 0 at h₁
    change -m z.val.2.1 - p₁ z.val.2.2 = 0 at h₂
    rcases hz z with ⟨hv, hw⟩
    constructor
    · change p₁ z.val.2.2 = 0
      simpa [hw] using h₂
    · change p₂ z.val.2.2 = 0
      simpa [hv] using h₁
  let κ : (LinearMap.ker φ) →ₗ[K] ↥((LinearMap.ker p₁) ⊓ (LinearMap.ker p₂)) :=
    { toFun := fun z => ⟨z.val.2.2, hc z⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hκ : Function.Injective κ := by
    intro x y hxy
    have hcxy : x.val.2.2 = y.val.2.2 := congrArg Subtype.val hxy
    apply Subtype.ext
    exact Prod.ext ((hz x).1.trans (hz y).1.symm)
      (Prod.ext ((hz x).2.trans (hz y).2.symm) hcxy)
  have hk := LinearMap.finrank_le_finrank_of_injective hκ
  have hr := Submodule.finrank_le (LinearMap.range φ)
  have he := φ.finrank_range_add_finrank_ker
  simp only [Module.finrank_prod] at hr he
  change finrank K (LinearMap.ker φ) ≤ finrank K ↥((LinearMap.ker p₁) ⊓ (LinearMap.ker p₂)) at hk
  change finrank K (LinearMap.range φ) ≤ finrank K ↥((LinearMap.range p₁) ⊔ (LinearMap.range p₂)) +
    (finrank K Q + finrank K Q) at hr
  omega

/-- Equality forces a common kernel and disjoint ranges in every dimension. -/
theorem dimension_rigidity
    (p₁ p₂ : V →ₗ[K] Q)
    (hQ : 5 * finrank K Q ≤ 4 * finrank K V)
    (hmain : 3 * finrank K V ≤
      finrank K ↥((LinearMap.ker p₁) ⊓ (LinearMap.ker p₂)) +
      finrank K ↥((LinearMap.range p₁) ⊔ (LinearMap.range p₂)) + 2 * finrank K Q) :
    5 * finrank K ↥((LinearMap.ker p₁) ⊓ (LinearMap.ker p₂)) = 3 * finrank K V ∧
    (LinearMap.ker p₁) = (LinearMap.ker p₂) ∧
    Disjoint (LinearMap.range p₁) (LinearMap.range p₂) := by
  have hn₁ := Submodule.finrank_mono
    (show (LinearMap.ker p₁) ⊓ (LinearMap.ker p₂) ≤ (LinearMap.ker p₁) from inf_le_left)
  have hn₂ := Submodule.finrank_mono
    (show (LinearMap.ker p₁) ⊓ (LinearMap.ker p₂) ≤ (LinearMap.ker p₂) from inf_le_right)
  have hr₁ := p₁.finrank_range_add_finrank_ker
  have hr₂ := p₂.finrank_range_add_finrank_ker
  have hs := Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range p₁) (LinearMap.range p₂)
  have hsq := Submodule.finrank_le ((LinearMap.range p₁) ⊔ (LinearMap.range p₂))
  obtain ⟨hn, hk₁, hk₂, hs'⟩ :=
    equality_case_arithmetic _ _ _ _ _ _ _ _ hQ hmain hn₁ hn₂ hr₁ hr₂ hs hsq
  have he₁ : (LinearMap.ker p₁) ⊓ (LinearMap.ker p₂) = (LinearMap.ker p₁) :=
    Submodule.eq_of_le_of_finrank_eq inf_le_left hk₁
  have he₂ : (LinearMap.ker p₁) ⊓ (LinearMap.ker p₂) = (LinearMap.ker p₂) :=
    Submodule.eq_of_le_of_finrank_eq inf_le_right hk₂
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range p₁) (LinearMap.range p₂)
  have hz : finrank K ↥((LinearMap.range p₁) ⊓ (LinearMap.range p₂)) = 0 := by omega
  have hdis : Disjoint (LinearMap.range p₁) (LinearMap.range p₂) := by
    rw [disjoint_iff]
    exact Submodule.finrank_eq_zero.mp hz
  exact ⟨hn, he₁.symm.trans he₂, hdis⟩

/-- The equality-case result from the three commuting-diagonal equations. -/
theorem dimension_rigidity_of_three_equations
    (p₁ p₂ μ : V →ₗ[K] Q)
    (hQ : 5 * finrank K Q ≤ 4 * finrank K V)
    (hkernel : ∀ v w c : V,
      p₁ v + p₂ w = 0 → -μ v + p₂ c = 0 → -μ w - p₁ c = 0 →
      v = 0 ∧ w = 0) :
    5 * finrank K ↥((LinearMap.ker p₁) ⊓ (LinearMap.ker p₂)) = 3 * finrank K V ∧
    (LinearMap.ker p₁) = (LinearMap.ker p₂) ∧
    Disjoint (LinearMap.range p₁) (LinearMap.range p₂) := by
  exact dimension_rigidity p₁ p₂ hQ (three_equation_dimension_bound p₁ p₂ μ hkernel)

end MatrixMultiplicationLowerBound


/-! ## DiagonalSupport -/
/-!
# Joint spectral support for invariant subspaces of diagonal operators

This file uses no infinite-field or algebraic-closure hypothesis.  Instead of
spectral projectors it eliminates unwanted coordinates one at a time.
-/

namespace MatrixMultiplicationLowerBound

variable {mcols : ℕ}

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

private theorem isolate_finite
    (F : Submodule K (ι → K)) (s t : ι → K)
    (hs : ∀ v ∈ F, (fun i => s i * v i) ∈ F)
    (ht : ∀ v ∈ F, (fun i => t i * v i) ∈ F)
    (i₀ : ι) (v : ι → K) (hv : v ∈ F) (hvi : v i₀ ≠ 0)
    (J : Finset ι)
    (hJ : ∀ j ∈ J, s i₀ ≠ s j ∨ t i₀ ≠ t j) :
    ∃ w : ι → K, w ∈ F ∧ w i₀ ≠ 0 ∧ ∀ j ∈ J, w j = 0 := by
  classical
  revert hJ
  induction J using Finset.induction_on with
  | empty =>
      intro hJ
      exact ⟨v, hv, hvi, by simp⟩
  | @insert j J hj ih =>
      intro hJ
      obtain ⟨w, hw, hwi, hwJ⟩ := ih (fun k hk => hJ k (Finset.mem_insert_of_mem hk))
      rcases hJ j (Finset.mem_insert_self j J) with hsj | htj
      · refine ⟨fun k => s k * w k - s j * w k, ?_, ?_, ?_⟩
        · exact F.sub_mem (hs w hw) (F.smul_mem (s j) hw)
        · dsimp
          rw [← sub_mul]
          exact mul_ne_zero (sub_ne_zero.mpr hsj) hwi
        · intro k hk
          rcases Finset.mem_insert.mp hk with rfl | hk
          · simp
          · simp [hwJ k hk]
      · refine ⟨fun k => t k * w k - t j * w k, ?_, ?_, ?_⟩
        · exact F.sub_mem (ht w hw) (F.smul_mem (t j) hw)
        · dsimp
          rw [← sub_mul]
          exact mul_ne_zero (sub_ne_zero.mpr htj) hwi
        · intro k hk
          rcases Finset.mem_insert.mp hk with rfl | hk
          · simp
          · simp [hwJ k hk]

/-- A nonzero invariant subspace of two diagonal maps contains a nonzero
vector supported on one common eigenvalue class.  The chosen coordinate can
be prescribed whenever the initial vector is nonzero there. -/
theorem diagonal_joint_support_at
    (F : Submodule K (ι → K)) (s t : ι → K)
    (hs : ∀ v ∈ F, (fun i => s i * v i) ∈ F)
    (ht : ∀ v ∈ F, (fun i => t i * v i) ∈ F)
    (i₀ : ι) (v : ι → K) (hv : v ∈ F) (hvi : v i₀ ≠ 0) :
    ∃ w : ι → K, w ∈ F ∧ w i₀ ≠ 0 ∧
      ∀ j, w j ≠ 0 → s j = s i₀ ∧ t j = t i₀ := by
  classical
  let J : Finset ι := Finset.univ.filter (fun j => s i₀ ≠ s j ∨ t i₀ ≠ t j)
  obtain ⟨w, hw, hwi, hwJ⟩ := isolate_finite F s t hs ht i₀ v hv hvi J
    (fun j hj => (Finset.mem_filter.mp hj).2)
  refine ⟨w, hw, hwi, ?_⟩
  intro j hwj
  have hnot : ¬ (s i₀ ≠ s j ∨ t i₀ ≠ t j) := by
    intro hj
    exact hwj (hwJ j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩))
  have hs : s i₀ = s j := by
    by_contra hs
    exact hnot (Or.inl hs)
  have ht : t i₀ = t j := by
    by_contra ht
    exact hnot (Or.inr ht)
  exact ⟨hs.symm, ht.symm⟩

/-- The joint spectral support lemma, with the nonzero coordinate selected
from an arbitrary nonzero vector of the invariant subspace. -/
theorem diagonal_joint_support
    (F : Submodule K (ι → K)) (s t : ι → K)
    (hs : ∀ v ∈ F, (fun i => s i * v i) ∈ F)
    (ht : ∀ v ∈ F, (fun i => t i * v i) ∈ F)
    (hF : F ≠ ⊥) :
    ∃ i₀ : ι, ∃ w : ι → K, w ∈ F ∧ w i₀ ≠ 0 ∧
      ∀ j, w j ≠ 0 → s j = s i₀ ∧ t j = t i₀ := by
  obtain ⟨v, hv, hv0⟩ := F.ne_bot_iff.mp hF
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hv0
  exact ⟨i₀, diagonal_joint_support_at F s t hs ht i₀ v hv hi₀⟩

end MatrixMultiplicationLowerBound


/-! ## SummandRank -/
/-! The image dimension of a sum of rank-one linear maps is bounded by
the dimension of the span of its coefficient forms. -/

namespace MatrixMultiplicationLowerBound

variable {mcols : ℕ}

open Module

variable {K : Type*} [Field K]
variable {A C : Type*} [AddCommGroup A] [Module K A]
  [AddCommGroup C] [Module K C]
  [FiniteDimensional K A] [FiniteDimensional K C]
variable {ι : Type*}

/-- A collection of coefficient forms spanning a space of dimension at most
`d` defines a linear map with image dimension at most `d`, regardless of the
associated output vectors. -/
theorem finrank_range_sum_smulRight_le
    (α : ι → Module.Dual K A) (c : ι → C) (G : Finset ι) :
    finrank K (LinearMap.range (∑ i ∈ G, (α i).smulRight (c i))) ≤
      finrank K (Submodule.span K (α '' (G : Set ι))) := by
  classical
  let f : A →ₗ[K] C := ∑ i ∈ G, (α i).smulRight (c i)
  let U : Submodule K (Module.Dual K A) := Submodule.span K (α '' (G : Set ι))
  have hrange : LinearMap.range f.dualMap ≤ U := by
    rintro _ ⟨φ, rfl⟩
    have heq : f.dualMap φ = ∑ i ∈ G, φ (c i) • α i := by
      ext a
      simp [f, LinearMap.dualMap_apply, LinearMap.smulRight_apply, mul_comm]
    rw [heq]
    exact Submodule.sum_mem U (fun i hi =>
      U.smul_mem _ (Submodule.subset_span ⟨i, hi, rfl⟩))
  calc
    finrank K (LinearMap.range f) = finrank K (LinearMap.range f.dualMap) :=
      (LinearMap.finrank_range_dualMap_eq_finrank_range f).symm
    _ ≤ finrank K U := Submodule.finrank_mono hrange

/-- Weighted version: coefficient forms of zero-weight summands need not
belong to the specified subspace. -/
theorem finrank_range_weighted_sum_le [Fintype ι]
    (α : ι → Module.Dual K A) (c : ι → C) (y : ι → K)
    (U : Submodule K (Module.Dual K A))
    (hU : ∀ i, y i ≠ 0 → α i ∈ U) :
    finrank K (LinearMap.range (∑ i, (α i).smulRight (y i • c i))) ≤
      finrank K U := by
  classical
  let f : A →ₗ[K] C := ∑ i, (α i).smulRight (y i • c i)
  have hrange : LinearMap.range f.dualMap ≤ U := by
    rintro _ ⟨φ, rfl⟩
    have heq : f.dualMap φ = ∑ i, φ (y i • c i) • α i := by
      ext a
      simp [f, LinearMap.dualMap_apply, LinearMap.smulRight_apply, mul_comm]
    rw [heq]
    apply Submodule.sum_mem U
    intro i hi
    by_cases hy : y i = 0
    · simp [hy]
    · exact U.smul_mem _ (hU i hy)
  calc
    finrank K (LinearMap.range f) = finrank K (LinearMap.range f.dualMap) :=
      (LinearMap.finrank_range_dualMap_eq_finrank_range f).symm
    _ ≤ finrank K U := Submodule.finrank_mono hrange

end MatrixMultiplicationLowerBound


/-! ## Contraction -/
namespace MatrixMultiplicationLowerBound

variable {mcols : ℕ}

open Module

variable {K : Type*} [Field K] {r : ℕ}

namespace Decomposition

variable (D : Decomposition K mcols r)

def coefficient (i : Fin r) : Module.Dual K (LeftInput K) :=
  (LinearMap.proj i).comp D.alpha

noncomputable def contraction (n : Row K mcols) : LeftInput K →ₗ[K] Output K mcols :=
  D.output.comp ((diag (D.Y n)).comp D.alpha)

@[simp] theorem contraction_apply (n : Row K mcols) (a : LeftInput K) :
    D.contraction n a = matrixMul a (0, n) := by
  change D.output (D.Y n * D.alpha a) = _
  rw [mul_comm]
  exact D.correct a (0, n)

theorem contraction_eq_sum (n : Row K mcols) :
    D.contraction n =
      ∑ i, (D.coefficient i).smulRight
        (D.Y n i • D.output (Pi.single i 1)) := by
  classical
  apply LinearMap.ext
  intro a
  change D.output (D.Y n * D.alpha a) = _
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply]
  have h : D.Y n * D.alpha a =
      ∑ i : Fin r, D.coefficient i a •
        (D.Y n i • (Pi.single i (1 : K) : Products K r)) := by
    ext k
    simp [Pi.single_apply, coefficient, mul_comm, eq_comm]
  rw [h, map_sum]
  simp only [map_smul]

/-- A nonzero second row gives a contraction of image dimension at least 3. -/
theorem three_le_finrank_contraction (n : Row K mcols) (hn : n ≠ 0) :
    3 ≤ finrank K (LinearMap.range (D.contraction n)) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hn
  let g : Col K →ₗ[K] Output K mcols :=
    (D.contraction n).comp (LinearMap.inr K (Col K) (Col K))
  have hg : Function.Injective g := by
    intro x y hxy
    ext i
    have h := congrFun (congrFun hxy i) j
    have heq : x i * n j = y i * n j := by
      simpa [g, matrixMul] using h
    exact mul_right_cancel₀ hj heq
  have hdim : finrank K (LinearMap.range g) = 3 := by
    rw [LinearMap.finrank_range_of_inj hg]
    simp [Col]
  calc
    3 = finrank K (LinearMap.range g) := hdim.symm
    _ ≤ finrank K (LinearMap.range (D.contraction n)) := by
      apply Submodule.finrank_mono
      rintro _ ⟨x, rfl⟩
      exact ⟨(0, x), rfl⟩

/-- If the nonzero coordinates of a row contraction use coefficient forms
in a two-dimensional subspace, exact matrix multiplication is impossible. -/
theorem contraction_support_contradiction
    (n : Row K mcols) (hn : n ≠ 0)
    (U : Submodule K (Module.Dual K (LeftInput K)))
    (hU : finrank K U ≤ 2)
    (hsupport : ∀ i, D.Y n i ≠ 0 → D.coefficient i ∈ U) : False := by
  have hlow := D.three_le_finrank_contraction n hn
  have hupp := finrank_range_weighted_sum_le
    D.coefficient (fun i => D.output (Pi.single i 1)) (D.Y n) U hsupport
  rw [← D.contraction_eq_sum n] at hupp
  exact (by decide : ¬ (3 : ℕ) ≤ 2) (hlow.trans (hupp.trans hU))

/-- Combines diagonal coordinate isolation with the rank-three contraction.
Every nonzero common invariant subspace inside the second-row image rules
out a decomposition whose common eigenvalue classes span at most two
coefficient forms. -/
theorem no_invariant_subspace_with_small_classes
    (F : Submodule K (Products K r))
    (hF : F ≠ ⊥) (hFY : F ≤ LinearMap.range D.Y)
    (hs : ∀ v ∈ F, diag D.s v ∈ F)
    (ht : ∀ v ∈ F, diag D.t v ∈ F)
    (hclasses : ∀ i₀ : Fin r,
      ∃ U : Submodule K (Module.Dual K (LeftInput K)),
        finrank K U ≤ 2 ∧ ∀ i,
          D.s i = D.s i₀ → D.t i = D.t i₀ → D.coefficient i ∈ U) : False := by
  obtain ⟨i₀, w, hw, hwi, hsupport⟩ :=
    diagonal_joint_support F D.s D.t hs ht hF
  obtain ⟨n, hn⟩ := hFY hw
  have hn0 : n ≠ 0 := by
    intro hz
    apply hwi
    rw [← hn, hz, map_zero]
    rfl
  obtain ⟨U, hU, hclass⟩ := hclasses i₀
  apply D.contraction_support_contradiction n hn0 U hU
  intro i hi
  have hpair := hsupport i (by rwa [← hn])
  exact hclass i hpair.1 hpair.2

end Decomposition
end MatrixMultiplicationLowerBound


/-! ## NormalizedDimensions -/
namespace MatrixMultiplicationLowerBound

variable {mcols : ℕ}

open Module LinearMap Submodule

namespace Decomposition

variable {K : Type*} [Field K] {r : ℕ} (D : Decomposition K mcols r)

/-- The kernel of the output map in a bilinear algorithm. -/
def H : Submodule K (Products K r) := LinearMap.ker D.output

/-- The second-row input map, regarded as taking values in `H`. -/
def YH (hD : D.alpha (colUnit 0, 0) = 1) : Row K mcols →ₗ[K] D.H :=
  D.Y.codRestrict D.H (fun v => D.output_Y hD v)

/-- The m-dimensional subspace generated by the second input row. -/
def J (hD : D.alpha (colUnit 0, 0) = 1) : Submodule K D.H :=
  LinearMap.range (D.YH hD)

/-- The residual space in the paper's dimension argument. -/
abbrev Q (hD : D.alpha (colUnit 0, 0) = 1) := D.H ⧸ D.J hD

@[simp] theorem YH_val (hD : D.alpha (colUnit 0, 0) = 1) (v : Row K mcols) :
    (D.YH hD v).val = D.Y v := rfl

theorem YH_injective (hD : D.alpha (colUnit 0, 0) = 1) :
    Function.Injective (D.YH hD) := by
  intro v w hvw
  apply D.Y_injective
  exact congrArg Subtype.val hvw

@[simp] theorem finrank_row : finrank K (Row K mcols) = mcols := by
  simp [Row]

@[simp] theorem finrank_output : finrank K (Output K mcols) = 3 * mcols := by
  simp [Output, Row, Module.finrank_pi_fintype]

@[simp] theorem finrank_products : finrank K (Products K r) = r := by
  simp [Products]

theorem finrank_H_add : finrank K D.H + 3 * mcols = r := by
  have h := LinearMap.finrank_range_add_finrank_ker D.output
  rw [LinearMap.range_eq_top.mpr D.output_surjective, finrank_top] at h
  change finrank K (Output K mcols) + finrank K D.H = finrank K (Products K r) at h
  rw [finrank_output, finrank_products] at h
  omega

theorem finrank_J (hD : D.alpha (colUnit 0, 0) = 1) :
    finrank K (D.J hD) = mcols := by
  have h := LinearMap.finrank_range_of_inj (D.YH_injective hD)
  exact h.trans finrank_row

theorem finrank_Q_add (hD : D.alpha (colUnit 0, 0) = 1) :
    finrank K (D.Q hD) + 4 * mcols = r := by
  have hquot := (D.J hD).finrank_quotient_add_finrank
  change finrank K (D.Q hD) + finrank K (D.J hD) = finrank K D.H at hquot
  rw [D.finrank_J hD] at hquot
  have hH := D.finrank_H_add
  omega

end Decomposition
end MatrixMultiplicationLowerBound


/-! ## NormalizedReduction -/
namespace MatrixMultiplicationLowerBound

variable {mcols : ℕ}

open Module

variable {K : Type*} [Field K] {r : ℕ}

namespace Decomposition

variable (D : Decomposition K mcols r)

/-- The finite joint-eigenvalue classes use at most two input forms. -/
def SmallClasses : Prop := ∀ i₀ : Fin r,
  ∃ U : Submodule K (Module.Dual K (LeftInput K)),
    finrank K U ≤ 2 ∧ ∀ i,
      D.s i = D.s i₀ → D.t i = D.t i₀ → D.coefficient i ∈ U

/-- The complete equality-case argument for a normalized decomposition.
The normalization and the small-class property are explicit hypotheses;
they must be obtained from a general decomposition by a separate theorem. -/
theorem rank_strict_of_normalized_small_classes (hm : 0 < mcols)
    (hD : D.alpha (colUnit 0, 0) = 1) (hclasses : D.SmallClasses) : 24 * mcols < 5 * r := by
  by_contra hr
  have hrbound : 5 * r ≤ 24 * mcols := by omega
  let YH := D.YH hD
  let SH : Row K mcols →ₗ[K] D.H :=
    ((diag D.s).comp D.Y).codRestrict D.H (fun v => D.output_sY v)
  let TH : Row K mcols →ₗ[K] D.H :=
    ((diag D.t).comp D.Y).codRestrict D.H (fun v => D.output_tY v)
  let μ : Row K mcols →ₗ[K] Products K r := (diag D.z).comp D.Y - D.X
  have hμH (v : Row K mcols) : μ v ∈ D.H := by
    change D.output (diag D.z (D.Y v) - D.X v) = 0
    rw [map_sub, D.output_zY, D.output_X hD, sub_self]
  let MH : Row K mcols →ₗ[K] D.H := μ.codRestrict D.H hμH
  let p₁ := rangeQuotientMap YH SH
  let p₂ := rangeQuotientMap YH TH
  let m := rangeQuotientMap YH MH
  have hkernel : ∀ v w c : Row K mcols,
      p₁ v + p₂ w = 0 → -m v + p₂ c = 0 → -m w - p₁ c = 0 →
      v = 0 ∧ w = 0 := by
    apply paper_injection_kernel D.X D.Y μ (diag D.s) (diag D.t) (diag D.z)
      D.output (rowInsert 0) (rowInsert 1) (rowInsert 2) p₁ p₂ m
    · intro v; rfl
    · exact diag_commute D.z D.s
    · exact diag_commute D.z D.t
    · exact diag_commute D.s D.t
    · exact D.output_zY
    · exact D.output_sY
    · exact D.output_tY
    · exact D.output_sX
    · exact D.output_tX
    · exact row_independent
    · intro v w h
      obtain ⟨a, ha⟩ := rangeQuotientMap_lift_add YH SH TH v w h
      exact ⟨a, congrArg Subtype.val ha⟩
    · intro v c h
      obtain ⟨b, hb⟩ := rangeQuotientMap_lift_neg_add YH MH TH v c h
      exact ⟨b, congrArg Subtype.val hb⟩
    · intro w c h
      obtain ⟨d, hd⟩ := rangeQuotientMap_lift_neg_sub YH MH SH w c h
      exact ⟨d, congrArg Subtype.val hd⟩
  have hQ : 5 * finrank K (D.H ⧸ LinearMap.range YH) ≤
      4 * finrank K (Row K mcols) := by
    have hdim := D.finrank_Q_add hD
    change finrank K (D.H ⧸ LinearMap.range YH) + 4 * mcols = r at hdim
    rw [finrank_row]
    omega
  obtain ⟨hN, hker, hdisjoint⟩ :=
    dimension_rigidity_of_three_equations p₁ p₂ m hQ hkernel
  have hlift₁ : ∀ x, p₁ x = 0 → ∃ u, D.Y u = diag D.s (D.Y x) := by
    intro x hx
    obtain ⟨u, hu⟩ := (rangeQuotientMap_eq_zero_iff YH SH x).mp hx
    exact ⟨u, congrArg Subtype.val hu⟩
  have hlift₂ : ∀ x, p₂ x = 0 → ∃ u, D.Y u = diag D.t (D.Y x) := by
    intro x hx
    obtain ⟨u, hu⟩ := (rangeQuotientMap_eq_zero_iff YH TH x).mp hx
    exact ⟨u, congrArg Subtype.val hu⟩
  have hcompat : ∀ u v, diag D.s (D.Y u) = diag D.t (D.Y v) → p₁ u = p₂ v := by
    intro u v huv
    apply rangeQuotientMap_compatible YH SH TH
    exact Subtype.ext huv
  obtain ⟨hs, ht⟩ := common_kernel_image_invariant_abstract
    D.Y (diag D.s) (diag D.t) p₁ p₂ hlift₁ hlift₂ hcompat
    (diag_commute D.s D.t) hker hdisjoint
  let F : Submodule K (Products K r) := Submodule.map D.Y (LinearMap.ker p₁)
  have hNdim : 5 * finrank K (LinearMap.ker p₁) = 3 * mcols := by
    have heq : LinearMap.ker p₁ ⊓ LinearMap.ker p₂ = LinearMap.ker p₁ := by
      rw [← hker, inf_idem]
    rw [heq, finrank_row] at hN
    exact hN
  have hNne : LinearMap.ker p₁ ≠ ⊥ := by
    intro hn
    have hz : finrank K (LinearMap.ker p₁) = 0 := Submodule.finrank_eq_zero.mpr hn
    omega
  obtain ⟨n, hn, hn0⟩ := (LinearMap.ker p₁).ne_bot_iff.mp hNne
  have hYn0 : D.Y n ≠ 0 := by
    intro hh
    apply hn0
    apply D.Y_injective
    simpa using hh
  have hF : F ≠ ⊥ := by
    intro hf
    have hYn_mem : D.Y n ∈ F := ⟨n, hn, rfl⟩
    rw [hf] at hYn_mem
    exact hYn0 hYn_mem
  have hFY : F ≤ LinearMap.range D.Y := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, rfl⟩
  exact D.no_invariant_subspace_with_small_classes F hF hFY hs ht hclasses

end Decomposition
end MatrixMultiplicationLowerBound


/-! ## GenericGrouping -/
/-!
Elementary algebra behind the two-dimensional generic grouping lemma.
All statements are characteristic-independent.
-/

namespace MM325

noncomputable section

variable {K : Type*} [Field K] {ι σ : Type*}

/-- A single point detects the zero polynomial simultaneously in a finite
family. This is precisely the finite generic-avoidance step; no algebraic
closure or characteristic assumption is used. -/
theorem exists_generic_polynomial_point [Infinite K] [Fintype σ]
    (p : σ → Polynomial K) :
    ∃ t : K, ∀ i, (p i).eval t = 0 → p i = 0 := by
  classical
  let bad : Finset K := Finset.univ.biUnion fun i => (p i).roots.toFinset
  obtain ⟨t, ht⟩ := bad.exists_not_mem
  refine ⟨t, ?_⟩
  intro i hi
  by_contra hp
  apply ht
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ i, ?_⟩
  exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hi)

/-- A polynomial encoding a coordinate of the affine pencil `u + t v`. -/
def pencilPolynomial (u v : K) : Polynomial K :=
  Polynomial.C u + Polynomial.C v * Polynomial.X

@[simp] theorem pencilPolynomial_eval (u v t : K) :
    (pencilPolynomial u v).eval t = u + t * v := by
  simp only [pencilPolynomial, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X]
  ring

theorem pencilPolynomial_eq_zero_iff (u v : K) :
    pencilPolynomial u v = 0 ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro h
    have h₀ := congrArg (fun p : Polynomial K => p.coeff 0) h
    have h₁ := congrArg (fun p : Polynomial K => p.coeff 1) h
    constructor
    · simpa [pencilPolynomial] using h₀
    · simpa [pencilPolynomial] using h₁
  · rintro ⟨rfl, rfl⟩
    simp [pencilPolynomial]

/-- A generic triangular change of the three row coordinates makes the first
coordinate of every prescribed nonzero vector nonzero. -/
theorem exists_generic_row_point [Infinite K] [Fintype σ]
    (w : σ → Fin 3 → K) :
    ∃ s : K, ∀ i, w i ≠ 0 →
      w i 0 + s * w i 1 + s ^ 2 * w i 2 ≠ 0 := by
  let polys : σ → Polynomial K := fun i =>
    Polynomial.C (w i 0) + Polynomial.C (w i 1) * Polynomial.X +
    Polynomial.C (w i 2) * Polynomial.X ^ 2
  obtain ⟨s, hs⟩ := exists_generic_polynomial_point polys
  refine ⟨s, ?_⟩
  intro i hi hz
  have hp : polys i = 0 := by
    apply hs i
    simp only [polys, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_pow]
    linear_combination hz
  have h₀ := congrArg (fun p : Polynomial K => p.coeff 0) hp
  have h₁ := congrArg (fun p : Polynomial K => p.coeff 1) hp
  have h₂ := congrArg (fun p : Polynomial K => p.coeff 2) hp
  simp [polys] at h₀ h₁ h₂
  apply hi
  funext q
  fin_cases q
  · exact h₀
  · exact h₁
  · exact h₂

/-- Vanishing of all two-by-two minors of a pair of vectors. -/
def WedgeZero (a b : ι → K) : Prop :=
  ∀ p q, a p * b q = a q * b p

theorem wedgeZero_iff_exists_smul (a b : ι → K) (ha : a ≠ 0) :
    WedgeZero a b ↔ ∃ c : K, b = c • a := by
  obtain ⟨p, hp⟩ : ∃ p, a p ≠ 0 := by
    by_contra! h
    apply ha
    funext p
    exact h p
  constructor
  · intro h
    refine ⟨b p / a p, ?_⟩
    funext q
    change b q = b p / a p * a q
    field_simp [hp]
    linear_combination h p q
  · rintro ⟨c, rfl⟩ p q
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem WedgeZero.smul_left (a b : ι → K) (c : K) (h : WedgeZero a b) :
    WedgeZero (c • a) b := by
  intro p q
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination c * h p q

theorem WedgeZero.smul_right (a b : ι → K) (c : K) (h : WedgeZero a b) :
    WedgeZero a (c • b) := by
  intro p q
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination c * h p q

theorem WedgeZero.map {κ : Type*} (F : (ι → K) →ₗ[K] (κ → K))
    {a b : ι → K} (h : WedgeZero a b) : WedgeZero (F a) (F b) := by
  by_cases ha : a = 0
  · subst a
    intro p q
    simp
  · obtain ⟨c, hc⟩ := (wedgeZero_iff_exists_smul a b ha).mp h
    rw [hc, map_smul]
    intro p q
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem WedgeZero.of_map {κ : Type*} (F : (ι → K) →ₗ[K] (κ → K))
    (hF : Function.Injective F) {a b : ι → K}
    (h : WedgeZero (F a) (F b)) : WedgeZero a b := by
  by_cases ha : a = 0
  · subst a
    intro p q
    simp
  · have hFa : F a ≠ 0 := by
      intro hz
      apply ha
      apply hF
      simpa using hz
    obtain ⟨c, hc⟩ := (wedgeZero_iff_exists_smul (F a) (F b) hFa).mp h
    apply (wedgeZero_iff_exists_smul a b ha).mpr
    refine ⟨c, hF ?_⟩
    simpa using hc

theorem wedgeZero_of_smul_eq_smul
    {a b : ι → K} {c d : K} (hc : c ≠ 0) (hd : d ≠ 0)
    (h : c • a = d • b) : WedgeZero a b := by
  have hw : WedgeZero (c • a) (d • b) := by
    rw [h]
    intro p q
    ring
  intro p q
  have hpq := hw p q
  simp only [Pi.smul_apply, smul_eq_mul] at hpq
  apply mul_left_cancel₀ (mul_ne_zero hc hd)
  linear_combination hpq

def pencilVector (u v : σ → ι → K) (i : σ) (t : K) : ι → K :=
  fun p => u i p + t * v i p

/-- One two-by-two minor of two affine vector pencils, expanded in `X`. -/
def pencilMinor (u v : σ → ι → K) (i j : σ) (p q : ι) : Polynomial K :=
  Polynomial.C (u i p * u j q - u i q * u j p) +
  Polynomial.C (u i p * v j q + v i p * u j q -
    u i q * v j p - v i q * u j p) * Polynomial.X +
  Polynomial.C (v i p * v j q - v i q * v j p) * Polynomial.X ^ 2

@[simp] theorem pencilMinor_eval (u v : σ → ι → K)
    (i j : σ) (p q : ι) (t : K) :
    (pencilMinor u v i j p q).eval t =
      pencilVector u v i t p * pencilVector u v j t q -
      pencilVector u v i t q * pencilVector u v j t p := by
  simp only [pencilMinor, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, pencilVector]
  ring

@[simp] theorem pencilMinor_coeff_two (u v : σ → ι → K)
    (i j : σ) (p q : ι) :
    (pencilMinor u v i j p q).coeff 2 =
      v i p * v j q - v i q * v j p := by
  simp only [pencilMinor, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_X_pow]
  norm_num

/-- Choose a generic first input column `(1,t)`. Every nonzero matrix has a
nonzero image there, and two proportional images there imply proportional
images for the entire pencil as well as for the second column. -/
theorem exists_generic_pencil_point [Infinite K] [Fintype σ] [Fintype ι]
    (u v : σ → ι → K) :
    ∃ t : K,
      (∀ i, u i ≠ 0 ∨ v i ≠ 0 → pencilVector u v i t ≠ 0) ∧
      ∀ i j, WedgeZero (pencilVector u v i t) (pencilVector u v j t) →
        WedgeZero (v i) (v j) ∧
        ∀ s, WedgeZero (pencilVector u v i s) (pencilVector u v j s) := by
  let polys : (σ × ι) ⊕ (σ × σ × ι × ι) → Polynomial K := fun z =>
    match z with
    | Sum.inl z => pencilPolynomial (u z.1 z.2) (v z.1 z.2)
    | Sum.inr z => pencilMinor u v z.1 z.2.1 z.2.2.1 z.2.2.2
  obtain ⟨t, ht⟩ := exists_generic_polynomial_point polys
  refine ⟨t, ?_, ?_⟩
  · intro i hi hz
    have huv : ∀ p, u i p = 0 ∧ v i p = 0 := by
      intro p
      apply (pencilPolynomial_eq_zero_iff _ _).mp
      apply ht (Sum.inl (i, p))
      simpa [polys, pencilVector] using congrFun hz p
    have hu : u i = 0 := by funext p; exact (huv p).1
    have hv : v i = 0 := by funext p; exact (huv p).2
    exact hi.elim (fun h => h hu) (fun h => h hv)
  · intro i j hij
    have hm : ∀ p q, pencilMinor u v i j p q = 0 := by
      intro p q
      apply ht (Sum.inr (i, j, p, q))
      change (pencilMinor u v i j p q).eval t = 0
      rw [pencilMinor_eval]
      exact sub_eq_zero.mpr (hij p q)
    constructor
    · intro p q
      apply sub_eq_zero.mp
      have hcoeff := congrArg (fun f : Polynomial K => f.coeff 2) (hm p q)
      simpa using hcoeff
    · intro s p q
      apply sub_eq_zero.mp
      have heval := congrArg (fun f : Polynomial K => f.eval s) (hm p q)
      simpa using heval

/-- A family of normalized two-column matrices with pointwise dependent images
lies in an affine line: the varying second column differs from one fixed
column by a multiple of the common first column. Only dependence at `(0,1)`
and `(1,1)` is needed. -/
theorem normalized_columns_affine
    (a : ι → K) (b : σ → ι → K) (i₀ : σ)
    (ha : a ≠ 0)
    (hsecond : ∀ i, WedgeZero (b i) (b i₀))
    (hsum : ∀ i, WedgeZero (a + b i) (a + b i₀)) :
    ∃ c : σ → K, ∀ i, b i = b i₀ + c i • a := by
  obtain ⟨p, hp⟩ : ∃ p, a p ≠ 0 := by
    by_contra! h
    apply ha
    funext p
    exact h p
  refine ⟨fun i => (b i p - b i₀ p) / a p, ?_⟩
  intro i
  funext q
  have h₀ := hsecond i p q
  have h₁ := hsum i p q
  change (a p + b i p) * (a q + b i₀ q) =
    (a q + b i q) * (a p + b i₀ p) at h₁
  have hc : a p * (b i q - b i₀ q) = a q * (b i p - b i₀ p) := by
    linear_combination h₀ - h₁
  change b i q = b i₀ q + ((b i p - b i₀ p) / a p) * a q
  field_simp [hp]
  linear_combination hc

/-- The corresponding complete two-column matrices belong to a linear span
of two fixed matrices. -/
theorem normalized_matrices_span_two
    (a : ι → K) (b : σ → ι → K) (i₀ : σ)
    (ha : a ≠ 0)
    (hsecond : ∀ i, WedgeZero (b i) (b i₀))
    (hsum : ∀ i, WedgeZero (a + b i) (a + b i₀)) :
    ∃ U V : ι → Fin 2 → K, ∀ i,
      (fun p j => if j = 0 then a p else b i p) ∈
      Submodule.span K ({U, V} : Set (ι → Fin 2 → K)) := by
  obtain ⟨c, hc⟩ := normalized_columns_affine a b i₀ ha hsecond hsum
  let U : ι → Fin 2 → K := fun p j => if j = 0 then a p else b i₀ p
  let V : ι → Fin 2 → K := fun p j => if j = 0 then 0 else a p
  refine ⟨U, V, ?_⟩
  intro i
  have hU : U ∈ Submodule.span K ({U, V} : Set (ι → Fin 2 → K)) :=
    Submodule.subset_span (by simp)
  have hV : V ∈ Submodule.span K ({U, V} : Set (ι → Fin 2 → K)) :=
    Submodule.subset_span (by simp)
  have hEq : (fun p j => if j = 0 then a p else b i p) = U + c i • V := by
    funext p j
    by_cases hj : j = 0
    · simp [U, V, hj]
    · have hp := congrFun (hc i) p
      simpa [U, V, hj] using hp
  rw [hEq]
  exact Submodule.add_mem _ hU (Submodule.smul_mem _ _ hV)

/-- Dimension form of the generic-grouping conclusion. -/
theorem normalized_matrices_finrank_le_two
    (a : ι → K) (b : σ → ι → K) (i₀ : σ)
    (ha : a ≠ 0)
    (hsecond : ∀ i, WedgeZero (b i) (b i₀))
    (hsum : ∀ i, WedgeZero (a + b i) (a + b i₀)) :
    Module.finrank K (Submodule.span K
      (Set.range fun i p (j : Fin 2) => if j = 0 then a p else b i p)) ≤ 2 := by
  classical
  obtain ⟨U, V, hUV⟩ := normalized_matrices_span_two a b i₀ ha hsecond hsum
  letI : Module.Finite K (Submodule.span K ({U, V} : Set (ι → Fin 2 → K))) :=
    Module.Finite.span_of_finite K ((Set.finite_singleton V).insert U)
  have hle : Submodule.span K
      (Set.range fun i p (j : Fin 2) => if j = 0 then a p else b i p) ≤
      Submodule.span K ({U, V} : Set (ι → Fin 2 → K)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hUV i
  calc
    _ ≤ Module.finrank K (Submodule.span K ({U, V} : Set (ι → Fin 2 → K))) :=
      Submodule.finrank_mono hle
    _ ≤ ({U, V} : Finset (ι → Fin 2 → K)).card := by
      simpa using finrank_span_finset_le_card (R := K) ({U, V} : Finset (ι → Fin 2 → K))
    _ ≤ 2 := by
      simpa using Finset.card_insert_le U ({V} : Finset (ι → Fin 2 → K))

/-- Coordinate extensionality for bilinear-algorithm input forms. -/
theorem linear_form_ext [Fintype ι] [DecidableEq ι]
    (f g : ((ι → K) × (ι → K)) →ₗ[K] K)
    (hfirst : ∀ p, f (Pi.single p 1, 0) = g (Pi.single p 1, 0))
    (hsecond : ∀ p, f (0, Pi.single p 1) = g (0, Pi.single p 1)) : f = g := by
  apply LinearMap.prod_ext
  · apply LinearMap.pi_ext
    intro p x
    have hx : ((Pi.single p x : ι → K), (0 : ι → K)) =
        x • ((Pi.single p 1 : ι → K), (0 : ι → K)) := by
      ext q <;> simp [Pi.single_apply]
    simpa only [LinearMap.comp_apply, LinearMap.inl_apply, hx, map_smul, hfirst p]
  · apply LinearMap.pi_ext
    intro p x
    have hx : ((0 : ι → K), (Pi.single p x : ι → K)) =
        x • ((0 : ι → K), (Pi.single p 1 : ι → K)) := by
      ext q <;> simp [Pi.single_apply]
    simpa only [LinearMap.comp_apply, LinearMap.inr_apply, hx, map_smul, hsecond p]

/-- Generic-grouping conclusion directly for the coefficient linear forms
used by a matrix-multiplication decomposition. -/
theorem normalized_forms_span_two [Fintype ι] [DecidableEq ι]
    (f : σ → ((ι → K) × (ι → K)) →ₗ[K] K) (i₀ : σ)
    (a : ι → K) (ha : a ≠ 0)
    (hfirst : ∀ i p, f i (Pi.single p 1, 0) = a p)
    (hsecond : ∀ i, WedgeZero (fun p => f i (0, Pi.single p 1))
      (fun p => f i₀ (0, Pi.single p 1)))
    (hsum : ∀ i, WedgeZero (a + fun p => f i (0, Pi.single p 1))
      (a + fun p => f i₀ (0, Pi.single p 1))) :
    ∃ U : Submodule K (((ι → K) × (ι → K)) →ₗ[K] K),
      Module.finrank K U ≤ 2 ∧ ∀ i, f i ∈ U := by
  obtain ⟨c, hc⟩ := normalized_columns_affine a
    (fun i p => f i (0, Pi.single p 1)) i₀ ha hsecond hsum
  let shift : ((ι → K) × (ι → K)) →ₗ[K] ((ι → K) × (ι → K)) :=
    (LinearMap.inl K (ι → K) (ι → K)).comp (LinearMap.snd K (ι → K) (ι → K))
  let d := (f i₀).comp shift
  let U := Submodule.span K ({f i₀, d} : Set (((ι → K) × (ι → K)) →ₗ[K] K))
  have hfi : ∀ i, f i = f i₀ + c i • d := by
    intro i
    apply linear_form_ext
    · intro p
      simp [d, shift, hfirst]
    · intro p
      have h := congrFun (hc i) p
      simpa [d, shift, hfirst] using h
  refine ⟨U, ?_, ?_⟩
  · classical
    calc
      Module.finrank K U ≤ ({f i₀, d} : Finset _).card := by
        simpa [U] using finrank_span_finset_le_card (R := K) ({f i₀, d} : Finset _)
      _ ≤ 2 := by simpa using Finset.card_insert_le (f i₀) ({d} : Finset _)
  · intro i
    rw [hfi i]
    exact Submodule.add_mem _ (Submodule.subset_span (by simp))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

end

end MM325


/-! ## GenericTransport -/
namespace MM325

variable {K : Type*} [Field K] {ι κ σ : Type*}

/-- Generic collinearity is preserved by an injective change of row
coordinates and by independently scaling each member of the family.
If their normalized first columns agree, the two dependence conditions
needed by `normalized_forms_span_two` follow. -/
theorem generic_normalized_dependence
    (u v : σ → ι → K) (t : K)
    (hgeneric : ∀ i j,
      WedgeZero (pencilVector u v i t) (pencilVector u v j t) →
        WedgeZero (v i) (v j) ∧
        ∀ s, WedgeZero (pencilVector u v i s) (pencilVector u v j s))
    (F : (ι → K) →ₗ[K] (κ → K)) (hF : Function.Injective F)
    (c : σ → K) (hc : ∀ i, c i ≠ 0)
    (a : κ → K)
    (hcommon : ∀ i, c i • F (pencilVector u v i t) = a)
    (i₀ : σ) :
    (∀ i, WedgeZero (c i • F (v i)) (c i₀ • F (v i₀))) ∧
    (∀ i, WedgeZero (a + c i • F (v i)) (a + c i₀ • F (v i₀))) := by
  have hdep (i : σ) := hgeneric i i₀
    (WedgeZero.of_map F hF
      (wedgeZero_of_smul_eq_smul (hc i) (hc i₀)
        ((hcommon i).trans (hcommon i₀).symm)))
  have hsum (i : σ) :
      a + c i • F (v i) = c i • F (pencilVector u v i (t + 1)) := by
    have hp : pencilVector u v i (t + 1) = pencilVector u v i t + v i := by
      funext p
      simp only [pencilVector, Pi.add_apply]
      ring
    rw [hp, map_add, smul_add, hcommon i]
  constructor
  · intro i
    exact WedgeZero.smul_right _ _ (c i₀)
      (WedgeZero.smul_left _ _ (c i) (WedgeZero.map F (hdep i).1))
  · intro i
    rw [hsum i, hsum i₀]
    exact WedgeZero.smul_right _ _ (c i₀)
      (WedgeZero.smul_left _ _ (c i) (WedgeZero.map F ((hdep i).2 (t + 1))))

end MM325


/-! ## GenericNormalForm -/
namespace MM325

variable {K : Type*} [Field K] {σ : Type*}

/-- The transpose of the determinant-one row-basis shear used to normalize
the matrix-multiplication algorithm. -/
def coefficientRowChange (s : K) : (Fin 3 → K) →ₗ[K] (Fin 3 → K) where
  toFun x p := if p = 0 then x 0 + s * x 1 + s ^ 2 * x 2 else x p
  map_add' x y := by
    funext p
    by_cases hp : p = 0
    · simp [hp]
      ring
    · simp [hp]
  map_smul' c x := by
    funext p
    by_cases hp : p = 0
    · simp [hp]
      ring
    · simp [hp]

@[simp] theorem coefficientRowChange_zero (s : K) (x : Fin 3 → K) :
    coefficientRowChange s x 0 = x 0 + s * x 1 + s ^ 2 * x 2 := by
  simp [coefficientRowChange]

@[simp] theorem coefficientRowChange_one (s : K) (x : Fin 3 → K) :
    coefficientRowChange s x 1 = x 1 := by
  simp [coefficientRowChange]

@[simp] theorem coefficientRowChange_two (s : K) (x : Fin 3 → K) :
    coefficientRowChange s x 2 = x 2 := by
  simp [coefficientRowChange]

theorem coefficientRowChange_injective (s : K) :
    Function.Injective (coefficientRowChange (K := K) s) := by
  intro x y h
  have h₀ := congrFun h (0 : Fin 3)
  have h₁ := congrFun h (1 : Fin 3)
  have h₂ := congrFun h (2 : Fin 3)
  simp only [coefficientRowChange_zero, coefficientRowChange_one,
    coefficientRowChange_two] at h₀ h₁ h₂
  funext p
  fin_cases p
  · change x (0 : Fin 3) = y 0
    linear_combination h₀ - s * h₁ - s ^ 2 * h₂
  · exact h₁
  · exact h₂

/-- Generic coordinate choices, normalization, and the two-dimensional joint
eigenvalue classes, in a form directly applicable to algorithm coefficients.
The hypotheses on `f` specify its six coefficients after the two triangular
coordinate changes and the inverse rescaling by `d`. -/
theorem generic_normal_form [Infinite K] [Fintype σ]
    (u v : σ → Fin 3 → K) (huv : ∀ i, u i ≠ 0 ∨ v i ≠ 0) :
    ∃ (t s : K) (d : σ → K),
      (∀ i, d i ≠ 0) ∧
      (∀ i, d i = coefficientRowChange s (pencilVector u v i t) 0) ∧
      ∀ f : σ → (((Fin 3 → K) × (Fin 3 → K)) →ₗ[K] K),
        (∀ i p, f i (Pi.single p 1, 0) =
          (d i)⁻¹ * coefficientRowChange s (pencilVector u v i t) p) →
        (∀ i p, f i (0, Pi.single p 1) =
          (d i)⁻¹ * coefficientRowChange s (v i) p) →
        (∀ i, f i (Pi.single 0 1, 0) = 1) ∧
        ∀ i₀, ∃ U : Submodule K (((Fin 3 → K) × (Fin 3 → K)) →ₗ[K] K),
          Module.finrank K U ≤ 2 ∧
          ∀ i, f i (Pi.single 1 1, 0) = f i₀ (Pi.single 1 1, 0) →
            f i (Pi.single 2 1, 0) = f i₀ (Pi.single 2 1, 0) → f i ∈ U := by
  classical
  obtain ⟨t, hnonzero, hgeneric⟩ := exists_generic_pencil_point u v
  obtain ⟨s, hs⟩ := exists_generic_row_point (fun i => pencilVector u v i t)
  let d : σ → K := fun i => coefficientRowChange s (pencilVector u v i t) 0
  have hd : ∀ i, d i ≠ 0 := by
    intro i
    exact hs i (hnonzero i (huv i))
  refine ⟨t, s, d, hd, fun _ => rfl, ?_⟩
  intro f hf hg
  have hnorm : ∀ i, f i (Pi.single 0 1, 0) = 1 := by
    intro i
    rw [hf]
    exact inv_mul_cancel₀ (hd i)
  refine ⟨hnorm, ?_⟩
  intro i₀
  let G := {i : σ //
    f i (Pi.single 1 1, 0) = f i₀ (Pi.single 1 1, 0) ∧
    f i (Pi.single 2 1, 0) = f i₀ (Pi.single 2 1, 0)}
  let base : G := ⟨i₀, rfl, rfl⟩
  let a : Fin 3 → K := fun p => f i₀ (Pi.single p 1, 0)
  have ha : a ≠ 0 := by
    intro hz
    have h := congrFun hz (0 : Fin 3)
    simpa [a, hnorm] using h
  have hcommon : ∀ i : G,
      (d i.val)⁻¹ • coefficientRowChange s (pencilVector u v i.val t) = a := by
    intro i
    funext p
    change (d i.val)⁻¹ * coefficientRowChange s (pencilVector u v i.val t) p =
      f i₀ (Pi.single p 1, 0)
    rw [← hf]
    fin_cases p
    · change f i.val (Pi.single (0 : Fin 3) 1, 0) = f i₀ (Pi.single 0 1, 0)
      rw [hnorm, hnorm]
    · exact i.prop.1
    · exact i.prop.2
  have hgenericG : ∀ i j : G,
      WedgeZero (pencilVector (fun k : G => u k.val) (fun k : G => v k.val) i t)
        (pencilVector (fun k : G => u k.val) (fun k : G => v k.val) j t) →
      WedgeZero (v i.val) (v j.val) ∧
      ∀ x, WedgeZero
        (pencilVector (fun k : G => u k.val) (fun k : G => v k.val) i x)
        (pencilVector (fun k : G => u k.val) (fun k : G => v k.val) j x) := by
    intro i j
    exact hgeneric i.val j.val
  obtain ⟨hsecond, hsum⟩ := generic_normalized_dependence
    (fun i : G => u i.val) (fun i : G => v i.val) t hgenericG
    (coefficientRowChange s) (coefficientRowChange_injective s)
    (fun i : G => (d i.val)⁻¹) (fun i => inv_ne_zero (hd i.val))
    a hcommon base
  have hfirst' : ∀ (i : G) p, f i.val (Pi.single p 1, 0) = a p := by
    intro i p
    rw [hf]
    exact congrFun (hcommon i) p
  have hsecond' : ∀ i : G, WedgeZero
      (fun p => f i.val (0, Pi.single p 1))
      (fun p => f base.val (0, Pi.single p 1)) := by
    intro i
    simpa only [hg, Pi.smul_apply, smul_eq_mul] using hsecond i
  have hsum' : ∀ i : G, WedgeZero
      (a + fun p => f i.val (0, Pi.single p 1))
      (a + fun p => f base.val (0, Pi.single p 1)) := by
    intro i
    simpa only [hg, Pi.smul_apply, smul_eq_mul] using hsum i
  obtain ⟨U, hdim, hU⟩ := normalized_forms_span_two (fun i : G => f i.val)
    base a ha hfirst' hsecond' hsum'
  refine ⟨U, hdim, ?_⟩
  intro i hi₁ hi₂
  exact hU ⟨i, hi₁, hi₂⟩

end MM325


/-! ## GenericIntegration -/
namespace MatrixMultiplicationLowerBound

variable {mcols : ℕ}

variable {K : Type*} [Field K]

def normalizationShear (s : K) : Col K :=
  fun i => if i = 0 then 0 else if i = 1 then s else s ^ 2

@[simp] theorem normalizationShear_zero (s : K) : normalizationShear s 0 = 0 := by
  simp [normalizationShear]

theorem linear_form_coordinates (f : LeftInput K →ₗ[K] K) (a : LeftInput K) :
    f a =
      a.1 0 * f (colUnit 0, 0) + a.1 1 * f (colUnit 1, 0) +
      a.1 2 * f (colUnit 2, 0) + a.2 0 * f (0, colUnit 0) +
      a.2 1 * f (0, colUnit 1) + a.2 2 * f (0, colUnit 2) := by
  have ha : a =
      a.1 0 • (colUnit 0, (0 : Col K)) + a.1 1 • (colUnit 1, 0) +
      a.1 2 • (colUnit 2, 0) + a.2 0 • (0, colUnit 0) +
      a.2 1 • (0, colUnit 1) + a.2 2 • (0, colUnit 2) := by
    ext i <;> fin_cases i <;> simp [colUnit, Pi.single_apply]
  conv_lhs => rw [ha]
  simp only [map_add, map_smul, smul_eq_mul]

theorem shear_form_first
    (f : LeftInput K →ₗ[K] K) (t s : K) (p : Fin 3) :
    f (shearLeft t (normalizationShear s) (colUnit p, 0)) =
      MM325.coefficientRowChange s
        (fun q => f (colUnit q, 0) + t * f (0, colUnit q)) p := by
  rw [linear_form_coordinates]
  fin_cases p <;>
    simp [shearLeft, shearCol, normalizationShear, colUnit, Pi.single_apply,
      MM325.coefficientRowChange]
  ring

theorem shear_form_second
    (f : LeftInput K →ₗ[K] K) (t s : K) (p : Fin 3) :
    f (shearLeft t (normalizationShear s) (0, colUnit p)) =
      MM325.coefficientRowChange s (fun q => f (0, colUnit q)) p := by
  rw [linear_form_coordinates]
  fin_cases p <;>
    simp [shearLeft, shearCol, normalizationShear, colUnit, Pi.single_apply,
      MM325.coefficientRowChange]

namespace Decomposition

variable {r : ℕ}

/-- Every exact bilinear algorithm over an infinite field admits the generic
normalization used by the equality-case argument, without changing its length. -/
theorem exists_normalized_small_classes [Infinite K] (D : Decomposition K mcols r) :
    ∃ E : Decomposition K mcols r,
      E.alpha (colUnit 0, 0) = 1 ∧ E.SmallClasses := by
  classical
  let D₀ := D.removeZeroForms
  let u : Fin r → Fin 3 → K := fun i p => D₀.alpha (colUnit p, 0) i
  let v : Fin r → Fin 3 → K := fun i p => D₀.alpha (0, colUnit p) i
  have huv : ∀ i, u i ≠ 0 ∨ v i ≠ 0 := by
    intro i
    by_contra hh
    push_neg at hh
    obtain ⟨hu, hv⟩ := hh
    have hz : D₀.coefficient i = 0 := by
      apply MM325.linear_form_ext
      · intro p
        have hp := congrFun hu p
        simpa [u, coefficient, colUnit] using hp
      · intro p
        have hp := congrFun hv p
        simpa [v, coefficient, colUnit] using hp
    obtain ⟨a, ha⟩ := D.removeZeroForms_nonzero i
    apply ha
    have he := LinearMap.congr_fun hz a
    exact he
  obtain ⟨t, s, d, hd, hde, hforms⟩ := MM325.generic_normal_form u v huv
  let C := D₀.changeCoordinates t (normalizationShear s) (normalizationShear_zero s)
  let E := C.rescale d hd
  have hf : ∀ i p, E.coefficient i (Pi.single p 1, 0) =
      (d i)⁻¹ * MM325.coefficientRowChange s (MM325.pencilVector u v i t) p := by
    intro i p
    change (d i)⁻¹ * D₀.coefficient i
      (shearLeft t (normalizationShear s) (colUnit p, 0)) = _
    rw [shear_form_first]
    rfl
  have hg : ∀ i p, E.coefficient i (0, Pi.single p 1) =
      (d i)⁻¹ * MM325.coefficientRowChange s (v i) p := by
    intro i p
    change (d i)⁻¹ * D₀.coefficient i
      (shearLeft t (normalizationShear s) (0, colUnit p)) = _
    rw [shear_form_second]
    rfl
  obtain ⟨hnorm, hclasses⟩ := hforms E.coefficient hf hg
  refine ⟨E, ?_, ?_⟩
  · ext i
    exact hnorm i
  · intro i₀
    obtain ⟨U, hdim, hU⟩ := hclasses i₀
    refine ⟨U, hdim, ?_⟩
    intro i hi₁ hi₂
    exact hU i hi₁ hi₂

/-- The requested lower bound over every infinite field. -/
theorem rank_strict_of_infinite [Infinite K] (D : Decomposition K mcols r)
    (hm : 0 < mcols) : 24 * mcols < 5 * r := by
  obtain ⟨E, hnorm, hclasses⟩ := D.exists_normalized_small_classes
  exact E.rank_strict_of_normalized_small_classes hm hnorm hclasses

end Decomposition
end MatrixMultiplicationLowerBound


/-! ## ScalarExtension -/
/-! Extension of an exact coordinate bilinear algorithm along a field homomorphism. -/

namespace MatrixMultiplicationLowerBound

variable {mcols : ℕ}

open scoped BigOperators

variable {K L : Type*} [Field K] [Field L]

noncomputable def pairBasis (F : Type*) [Field F] (n : ℕ) :
    Basis (Fin n ⊕ Fin n) F ((Fin n → F) × (Fin n → F)) :=
  (Pi.basisFun F (Fin n)).prod (Pi.basisFun F (Fin n))

def mapVec (φ : K →+* L) {ι : Type*} (v : ι → K) : ι → L := fun i => φ (v i)

def mapPair (φ : K →+* L) {ι : Type*} (v : (ι → K) × (ι → K)) :
    (ι → L) × (ι → L) := (mapVec φ v.1, mapVec φ v.2)

def mapOut (φ : K →+* L) (o : Output K mcols) : Output L mcols := fun i j => φ (o i j)

@[simp] theorem mapPair_basis (φ : K →+* L) (n : ℕ) (q : Fin n ⊕ Fin n) :
    mapPair φ (pairBasis K n q) = pairBasis L n q := by
  classical
  cases q <;> ext i <;>
    simp [pairBasis, Basis.prod_apply, mapPair, mapVec, Pi.basisFun_apply,
      Pi.single_apply]

@[simp] theorem mapOut_matrixMul (φ : K →+* L)
    (a : LeftInput K) (b : RightInput K mcols) :
    mapOut φ (matrixMul a b) = matrixMul (mapPair φ a) (mapPair φ b) := by
  ext i j
  simp [mapOut, matrixMul, mapPair, mapVec]

namespace Decomposition

variable {r : ℕ} (D : Decomposition K mcols r) (φ : K →+* L)

noncomputable def extendAlpha : LeftInput L →ₗ[L] Products L r :=
  (pairBasis L 3).constr L (fun q => mapVec φ (D.alpha (pairBasis K 3 q)))

noncomputable def extendBeta : RightInput L mcols →ₗ[L] Products L r :=
  (pairBasis L mcols).constr L (fun q => mapVec φ (D.beta (pairBasis K mcols q)))

noncomputable def extendOutput : Products L r →ₗ[L] Output L mcols :=
  (Pi.basisFun L (Fin r)).constr L
    (fun k => mapOut φ (D.output (Pi.basisFun K (Fin r) k)))

@[simp] theorem extendAlpha_basis (q : Fin 3 ⊕ Fin 3) :
    D.extendAlpha φ (pairBasis L 3 q) = mapVec φ (D.alpha (pairBasis K 3 q)) := by
  simp [extendAlpha]

@[simp] theorem extendBeta_basis (q : Fin mcols ⊕ Fin mcols) :
    D.extendBeta φ (pairBasis L mcols q) = mapVec φ (D.beta (pairBasis K mcols q)) := by
  simp [extendBeta]

@[simp] theorem extendOutput_mapVec (v : Products K r) :
    D.extendOutput φ (mapVec φ v) = mapOut φ (D.output v) := by
  classical
  have hv : D.output v = ∑ k : Fin r, v k • D.output (Pi.basisFun K (Fin r) k) := by
    conv_lhs => rw [← (Pi.basisFun K (Fin r)).sum_repr v]
    simp
  ext i j
  simp [extendOutput, Basis.constr_apply_fintype, hv, mapOut, mapVec,
    Pi.basisFun_equivFun, Finset.sum_apply, map_sum]

end Decomposition

noncomputable def algorithmBilin {r : ℕ}
    (α : LeftInput K →ₗ[K] Products K r)
    (β : RightInput K mcols →ₗ[K] Products K r)
    (ω : Products K r →ₗ[K] Output K mcols) :
    LeftInput K →ₗ[K] RightInput K mcols →ₗ[K] Output K mcols :=
  LinearMap.mk₂ K (fun a b => ω (α a * β b))
    (by intros; simp [map_add, add_mul])
    (by intros; simp [map_smul, smul_mul_assoc])
    (by intros; simp [map_add, mul_add])
    (by intros; simp [map_smul, mul_smul_comm])

def matrixMulBilin : LeftInput K →ₗ[K] RightInput K mcols →ₗ[K] Output K mcols :=
  LinearMap.mk₂ K matrixMul
    (by intros; ext i j; simp [matrixMul, add_mul]; ring)
    (by intros; ext i j; simp [matrixMul, mul_add, mul_assoc])
    (by intros; ext i j; simp [matrixMul, mul_add]; ring)
    (by intros; ext i j; simp [matrixMul, mul_add, mul_left_comm, mul_assoc])

namespace Decomposition

variable {r : ℕ} (D : Decomposition K mcols r) (φ : K →+* L)

theorem extend_correct (a : LeftInput L) (b : RightInput L mcols) :
    D.extendOutput φ (D.extendAlpha φ a * D.extendBeta φ b) = matrixMul a b := by
  have h : algorithmBilin (D.extendAlpha φ) (D.extendBeta φ) (D.extendOutput φ) =
      (matrixMulBilin : LeftInput L →ₗ[L] RightInput L mcols →ₗ[L] Output L mcols) := by
    apply (pairBasis L 3).ext
    intro p
    apply (pairBasis L mcols).ext
    intro q
    change D.extendOutput φ
      (D.extendAlpha φ (pairBasis L 3 p) * D.extendBeta φ (pairBasis L mcols q)) = _
    rw [D.extendAlpha_basis, D.extendBeta_basis]
    have hm (x y : Products K r) : mapVec φ x * mapVec φ y = mapVec φ (x * y) := by
      ext k
      simp [mapVec]
    rw [hm, D.extendOutput_mapVec, D.correct, mapOut_matrixMul,
      mapPair_basis, mapPair_basis]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

/-- Extending coefficients to another field preserves the number of products. -/
noncomputable def extendScalars : Decomposition L mcols r where
  alpha := D.extendAlpha φ
  beta := D.extendBeta φ
  output := D.extendOutput φ
  correct := D.extend_correct φ

end Decomposition

theorem ratFunc_infinite (F : Type*) [Field F] : Infinite (RatFunc F) :=
  Infinite.of_injective (algebraMap (Polynomial F) (RatFunc F))
    (RatFunc.algebraMap_injective F)

end MatrixMultiplicationLowerBound


/-! ## ArbitraryFieldTheorem -/
/-! The main theorem: every exact bilinear algorithm for multiplying
3-by-2 and 2-by-m matrices uses strictly more than 24m/5 scalar products.
No infiniteness or characteristic hypothesis is assumed. -/

namespace MatrixMultiplicationLowerBound

variable {mcols : ℕ}

theorem matrix_multiplication_rank_strict
    {K : Type*} [Field K] {r : ℕ} (D : Decomposition K mcols r)
    (hm : 0 < mcols) : 24 * mcols < 5 * r := by
  letI : Infinite (RatFunc K) := ratFunc_infinite K
  exact (D.extendScalars (algebraMap K (RatFunc K))).rank_strict_of_infinite hm

end MatrixMultiplicationLowerBound


/-! ## MatrixInterface -/
/-! The lower bound stated using the usual matrix notation and scalar linear forms. -/

namespace MatrixMultiplicationLowerBound

variable {mcols : ℕ}

open scoped BigOperators

variable {K : Type*} [Field K]

/-- Assemble the two columns of a 3-by-2 matrix. -/
def columnsToMatrix : LeftInput K →ₗ[K] Matrix (Fin 3) (Fin 2) K where
  toFun a i j := if j = 0 then a.1 i else a.2 i
  map_add' a b := by
    ext i j
    by_cases hj : j = 0 <;> simp [hj]
  map_smul' c a := by
    ext i j
    by_cases hj : j = 0 <;> simp [hj]

/-- Assemble the two rows of a 2-by-m matrix. -/
def rowsToMatrix : RightInput K mcols →ₗ[K] Matrix (Fin 2) (Fin mcols) K where
  toFun b i j := if i = 0 then b.1 j else b.2 j
  map_add' a b := by
    ext i j
    by_cases hi : i = 0 <;> simp [hi]
  map_smul' c a := by
    ext i j
    by_cases hi : i = 0 <;> simp [hi]

theorem assembled_matrices_mul (a : LeftInput K) (b : RightInput K mcols) :
    columnsToMatrix a * rowsToMatrix b = matrixMul a b := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_two, columnsToMatrix, rowsToMatrix, matrixMul]

/-- Interpret an ordinary matrix algorithm as the coordinate decomposition used in the proof. -/
noncomputable def fromMatrixAlgorithm {r : ℕ}
    (α : Fin r → (Matrix (Fin 3) (Fin 2) K →ₗ[K] K))
    (β : Fin r → (Matrix (Fin 2) (Fin mcols) K →ₗ[K] K))
    (C : Fin r → Matrix (Fin 3) (Fin mcols) K)
    (h : ∀ A B, A * B = ∑ k : Fin r, (α k A * β k B) • C k) :
    Decomposition K mcols r where
  alpha := LinearMap.pi (fun k => (α k).comp columnsToMatrix)
  beta := LinearMap.pi (fun k => (β k).comp rowsToMatrix)
  output :=
    { toFun := fun z => ∑ k : Fin r, z k • C k
      map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [smul_smul, Finset.smul_sum] }
  correct := by
    intro a b
    change (∑ k : Fin r, (α k (columnsToMatrix a) * β k (rowsToMatrix b)) • C k) =
      matrixMul a b
    rw [← h]
    exact assembled_matrices_mul a b

/-- Theorem 1: every exact bilinear decomposition has length strictly greater
than 24m/5, over every field and for every positive integer m. The conclusion
uses natural-number arithmetic and is meaningful in every characteristic. -/
theorem matrix_algorithm_rank_strict {r : ℕ} (hm : 0 < mcols)
    (α : Fin r → (Matrix (Fin 3) (Fin 2) K →ₗ[K] K))
    (β : Fin r → (Matrix (Fin 2) (Fin mcols) K →ₗ[K] K))
    (C : Fin r → Matrix (Fin 3) (Fin mcols) K)
    (h : ∀ A B, A * B = ∑ k : Fin r, (α k A * β k B) • C k) :
    24 * mcols < 5 * r :=
  matrix_multiplication_rank_strict (fromMatrixAlgorithm α β C h) hm

/-- The original m = 5 result is a corollary of the general theorem. -/
theorem matrix_algorithm_rank_ge25 {r : ℕ}
    (α : Fin r → (Matrix (Fin 3) (Fin 2) K →ₗ[K] K))
    (β : Fin r → (Matrix (Fin 2) (Fin 5) K →ₗ[K] K))
    (C : Fin r → Matrix (Fin 3) (Fin 5) K)
    (h : ∀ A B, A * B = ∑ k : Fin r, (α k A * β k B) • C k) :
    25 ≤ r := by
  have hstrict := matrix_algorithm_rank_strict (by decide : 0 < 5) α β C h
  omega

end MatrixMultiplicationLowerBound


/-! ## Minimum rank and Theorem 1 -/
namespace MatrixMultiplicationLowerBound

open scoped BigOperators

variable {K : Type*} [Field K] {mcols : ℕ}

/-- The ordinary entrywise algorithm gives an exact finite decomposition. -/
theorem exists_decomposition (K : Type*) [Field K] (mcols : ℕ) :
    ∃ r, Nonempty (Decomposition K mcols r) := by
  classical
  let I := Fin 3 × Fin 2 × Fin mcols
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let α : Fin (Fintype.card I) → (Matrix (Fin 3) (Fin 2) K →ₗ[K] K) :=
    fun k =>
      { toFun := fun A => A (e.symm k).1 (e.symm k).2.1
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
  let β : Fin (Fintype.card I) → (Matrix (Fin 2) (Fin mcols) K →ₗ[K] K) :=
    fun k =>
      { toFun := fun B => B (e.symm k).2.1 (e.symm k).2.2
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
  let C : Fin (Fintype.card I) → Matrix (Fin 3) (Fin mcols) K :=
    fun k i j => if i = (e.symm k).1 ∧ j = (e.symm k).2.2 then 1 else 0
  have h : ∀ A B, A * B = ∑ k, (α k A * β k B) • C k := by
    intro A B
    rw [← e.sum_comp (fun k => (α k A * β k B) • C k)]
    ext i j
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change (∑ k : Fin 2, A i k * B k j) =
      ∑ t : I, (A (e.symm (e t)).1 (e.symm (e t)).2.1 *
        B (e.symm (e t)).2.1 (e.symm (e t)).2.2) *
        (if i = (e.symm (e t)).1 ∧ j = (e.symm (e t)).2.2 then 1 else 0)
    simp only [Equiv.symm_apply_apply]
    simp [I, Fintype.sum_prod_type, ite_and, Finset.sum_add_distrib, eq_comm]
  exact ⟨Fintype.card I, ⟨fromMatrixAlgorithm α β C h⟩⟩

/-- The tensor rank R_K(<3,2,m>): the minimum length of an exact bilinear
decomposition. Existence is proved by the entrywise matrix algorithm. -/
noncomputable def matrixMultiplicationRank (K : Type*) [Field K] (mcols : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_decomposition K mcols)

/-- The minimum is attained by an exact decomposition. -/
theorem matrixMultiplicationRank_attained :
    Nonempty (Decomposition K mcols (matrixMultiplicationRank K mcols)) := by
  classical
  exact Nat.find_spec (exists_decomposition K mcols)

/-- Every exact decomposition bounds the rank from above. -/
theorem matrixMultiplicationRank_le {r : ℕ} (D : Decomposition K mcols r) :
    matrixMultiplicationRank K mcols ≤ r := by
  classical
  exact Nat.find_min' (exists_decomposition K mcols) ⟨D⟩

/-- Theorem 1 in integer form; all arithmetic here is in the natural numbers. -/
theorem theorem_one (K : Type*) [Field K] (mcols : ℕ) (hm : 0 < mcols) :
    24 * mcols < 5 * matrixMultiplicationRank K mcols := by
  obtain ⟨D⟩ := matrixMultiplicationRank_attained (K := K) (mcols := mcols)
  exact matrix_multiplication_rank_strict D hm

/-- Theorem 1 exactly as printed in the paper. The quotient is in Q,
independently of the characteristic of the coefficient field K. -/
theorem theorem_one_rational (K : Type*) [Field K] (mcols : ℕ) (hm : 0 < mcols) :
    (24 * (mcols : ℚ)) / 5 < (matrixMultiplicationRank K mcols : ℚ) := by
  have h := theorem_one K mcols hm
  apply (div_lt_iff₀ (by norm_num : (0 : ℚ) < 5)).mpr
  exact_mod_cast (by omega : 24 * mcols < matrixMultiplicationRank K mcols * 5)

/-- The integer rounding corollary from the paper. -/
theorem theorem_one_rounded (K : Type*) [Field K] (mcols : ℕ) (hm : 0 < mcols) :
    24 * mcols / 5 + 1 ≤ matrixMultiplicationRank K mcols := by
  have h := theorem_one K mcols hm
  omega

/-- The requested numerical lower bound is the m = 5 specialization. -/
theorem rank_325_ge25 (K : Type*) [Field K] :
    25 ≤ matrixMultiplicationRank K 5 := by
  have h := theorem_one K 5 (by decide)
  omega

end MatrixMultiplicationLowerBound


/-! ## Equivalence with the ordinary matrix model -/
namespace MatrixMultiplicationLowerBound

open scoped BigOperators

variable {K : Type*} [Field K] {mcols r : ℕ}

/-- A length-r bilinear algorithm written entirely in the ordinary matrix model. -/
structure MatrixAlgorithm (K : Type*) [Field K] (mcols r : ℕ) where
  alpha : Fin r → (Matrix (Fin 3) (Fin 2) K →ₗ[K] K)
  beta : Fin r → (Matrix (Fin 2) (Fin mcols) K →ₗ[K] K)
  coeff : Fin r → Matrix (Fin 3) (Fin mcols) K
  correct : ∀ A B, A * B = ∑ k : Fin r, (alpha k A * beta k B) • coeff k

/-- Extract the two columns of an ordinary matrix. -/
def matrixToColumns : Matrix (Fin 3) (Fin 2) K →ₗ[K] LeftInput K where
  toFun A := (fun i => A i 0, fun i => A i 1)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Extract the two rows of an ordinary matrix. -/
def matrixToRows : Matrix (Fin 2) (Fin mcols) K →ₗ[K] RightInput K mcols where
  toFun B := (B 0, B 1)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Convert a coordinate decomposition into an ordinary matrix algorithm,
preserving its length exactly, including any zero summands. -/
noncomputable def Decomposition.toMatrixAlgorithm (D : Decomposition K mcols r) :
    MatrixAlgorithm K mcols r where
  alpha k := (LinearMap.proj k).comp (D.alpha.comp matrixToColumns)
  beta k := (LinearMap.proj k).comp (D.beta.comp matrixToRows)
  coeff k := D.output (Pi.single k 1)
  correct A B := by
    have hv (v : Products K r) : D.output v = ∑ k, v k • D.output (Pi.single k 1) := by
      conv_lhs => rw [← (Pi.basisFun K (Fin r)).sum_repr v]
      simp [Pi.basisFun_apply, Pi.basisFun_equivFun]
    change A * B = ∑ k, (D.alpha (matrixToColumns A) * D.beta (matrixToRows B)) k •
      D.output (Pi.single k 1)
    rw [← hv, D.correct]
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_two, matrixMul, matrixToColumns, matrixToRows]

/-- Convert an ordinary matrix algorithm back to the coordinate model. -/
noncomputable def MatrixAlgorithm.toDecomposition (alg : MatrixAlgorithm K mcols r) :
    Decomposition K mcols r :=
  fromMatrixAlgorithm alg.alpha alg.beta alg.coeff alg.correct

/-- The two models admit precisely the same decomposition lengths. -/
theorem decomposition_iff_matrixAlgorithm :
    Nonempty (Decomposition K mcols r) ↔ Nonempty (MatrixAlgorithm K mcols r) := by
  constructor
  · rintro ⟨D⟩
    exact ⟨D.toMatrixAlgorithm⟩
  · rintro ⟨alg⟩
    exact ⟨alg.toDecomposition⟩

theorem exists_matrixAlgorithm (K : Type*) [Field K] (mcols : ℕ) :
    ∃ r, Nonempty (MatrixAlgorithm K mcols r) := by
  obtain ⟨r, h⟩ := exists_decomposition K mcols
  exact ⟨r, decomposition_iff_matrixAlgorithm.mp h⟩

/-- R_K(<3,2,m>) in the ordinary matrix model: the minimum number of products
of scalar linear forms needed for exact matrix multiplication. -/
noncomputable def matrixTensorRank (K : Type*) [Field K] (mcols : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_matrixAlgorithm K mcols)

theorem matrixTensorRank_attained :
    Nonempty (MatrixAlgorithm K mcols (matrixTensorRank K mcols)) := by
  classical
  exact Nat.find_spec (exists_matrixAlgorithm K mcols)

theorem matrixTensorRank_le (alg : MatrixAlgorithm K mcols r) :
    matrixTensorRank K mcols ≤ r := by
  classical
  exact Nat.find_min' (exists_matrixAlgorithm K mcols) ⟨alg⟩

/-- The rank used in Theorem 1 equals the ordinary matrix-model tensor rank.
This holds over every field and also for m = 0. -/
theorem rank_eq (K : Type*) [Field K] (mcols : ℕ) :
    matrixMultiplicationRank K mcols = matrixTensorRank K mcols := by
  apply le_antisymm
  · obtain ⟨alg⟩ := matrixTensorRank_attained (K := K) (mcols := mcols)
    exact matrixMultiplicationRank_le alg.toDecomposition
  · obtain ⟨D⟩ := matrixMultiplicationRank_attained (K := K) (mcols := mcols)
    exact matrixTensorRank_le D.toMatrixAlgorithm

/-- Theorem 1 explicitly in terms of the ordinary matrix-model tensor rank. -/
theorem theorem_one_tensorRank (K : Type*) [Field K] (mcols : ℕ) (hm : 0 < mcols) :
    (24 * (mcols : ℚ)) / 5 < (matrixTensorRank K mcols : ℚ) := by
  rw [← rank_eq K mcols]
  exact theorem_one_rational K mcols hm

end MatrixMultiplicationLowerBound
