module

public import SKConstants.Completion.LGram.Compression
public import SKConstants.Completion.LGram.WholeGram
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
namespace SKConstants.Completion.LGram
open LC5
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {N d k : ℕ}

def empiricalGram (z : Fin N → EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => (∑ l, z l i * z l j) / (N:ℝ)

def populationGram {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (Z : Ξ → EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∫ w, Z w i * Z w j ∂μ

def rowGramEvent (P : Matrix (Fin d) (Fin d) ℝ) (N : ℕ) (η : ℝ) :
    Set (Fin N → EuclideanSpace ℝ (Fin d)) := {z | ‖empiricalGram z - P‖ ≤ η}

theorem measurableSet_rowGramEvent (P : Matrix (Fin d) (Fin d) ℝ) (N : ℕ) (η : ℝ) :
    MeasurableSet (rowGramEvent P N η) := by
  have hm : Measurable (fun z : Fin N → EuclideanSpace ℝ (Fin d) => empiricalGram z-P) := by
    unfold empiricalGram
    fun_prop
  exact measurableSet_le hm.norm measurable_const

def sampleColumn (z : Fin N → EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    EuclideanSpace ℝ (Fin N) :=
  (Real.sqrt (N:ℝ))⁻¹ • WithLp.toLp 2 (fun l => z l i)

theorem sampleColumn_inner (z : Fin N → EuclideanSpace ℝ (Fin d)) (i j : Fin d) :
    inner (𝕜 := ℝ) (sampleColumn z i) (sampleColumn z j) = empiricalGram z i j := by
  have hs : (Real.sqrt (N:ℝ))⁻¹ * (Real.sqrt (N:ℝ))⁻¹ = (N:ℝ)⁻¹ := by
    rw [← mul_inv, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg N)]
  unfold sampleColumn
  rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, hs]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
    star_trivial, empiricalGram, div_eq_inv_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  exact mul_comm _ _

theorem rowGramEvent_blocks (P : Matrix (Fin d) (Fin d) ℝ)
    (e f : Fin k → Fin d) (he : Function.Injective e) (hf : Function.Injective f)
    (j : Fin d) (z : Fin N → EuclideanSpace ℝ (Fin d)) (η : ℝ)
    (hz : z ∈ rowGramEvent P N η) (hP : P.submatrix e e = 1) :
    ‖familyGram (fun i => sampleColumn z (e i))-1‖ ≤ η ∧
    ‖familyCross (fun i => sampleColumn z (e i)) (fun i => sampleColumn z (f i))-
      P.submatrix e f‖ ≤ η ∧
    ‖familyCoordinates (fun i => sampleColumn z (e i)) (sampleColumn z j)-
      WithLp.toLp 2 (fun i => P (e i) j)‖ ≤ η ∧
    ‖familyCoordinates (fun i => sampleColumn z (f i)) (sampleColumn z j)-
      WithLp.toLp 2 (fun i => P (f i) j)‖ ≤ η := by
  have hA : familyGram (fun i => sampleColumn z (e i))-1 =
      (empiricalGram z-P).submatrix e e := by
    rw [← hP]
    ext i j
    simp [familyGram, sampleColumn_inner]
  have hH : familyCross (fun i => sampleColumn z (e i)) (fun i => sampleColumn z (f i))-
      P.submatrix e f = (empiricalGram z-P).submatrix e f := by
    ext i j
    simp [familyCross, sampleColumn_inner]
  have hq : familyCoordinates (fun i => sampleColumn z (e i)) (sampleColumn z j)-
      WithLp.toLp 2 (fun i => P (e i) j) =
      WithLp.toLp 2 (fun i => (empiricalGram z-P) (e i) j) := by
    ext i
    simp [familyCoordinates, sampleColumn_inner]
  have hv : familyCoordinates (fun i => sampleColumn z (f i)) (sampleColumn z j)-
      WithLp.toLp 2 (fun i => P (f i) j) =
      WithLp.toLp 2 (fun i => (empiricalGram z-P) (f i) j) := by
    ext i
    simp [familyCoordinates, sampleColumn_inner]
  rw [hA, hH, hq, hv]
  exact ⟨(coordinateBlock_norm_le _ e e he he).trans hz,
    (coordinateBlock_norm_le _ e f he hf).trans hz,
    (coordinateColumn_norm_le _ e he j).trans hz,
    (coordinateColumn_norm_le _ f hf j).trans hz⟩

def posteriorIndex (k : ℕ) (i : Fin k) : Fin (k+(k+1)) := i.castAdd (k+1)
def queryIndex (k : ℕ) (i : Fin k) : Fin (k+(k+1)) := (i.castAdd 1).natAdd k
def spinIndex (k : ℕ) : Fin (k+(k+1)) := ((0 : Fin 1).natAdd k).natAdd k

theorem posteriorIndex_injective (k : ℕ) : Function.Injective (posteriorIndex k) := by
  intro i j h
  have hh := congrArg (fun z : Fin (k+(k+1)) => z.val) h
  exact Fin.ext hh

theorem queryIndex_injective (k : ℕ) : Function.Injective (queryIndex k) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa only [queryIndex, Fin.val_natAdd, Fin.val_castAdd, Nat.add_right_inj] using hv

theorem centeredEmpiricalCovariance_eq_empirical_sub_population
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (X : Fin N → Ξ → EuclideanSpace ℝ (Fin d))
    (P : Matrix (Fin d) (Fin d) ℝ) (hN : 0 < N)
    (hP : ∀ l i j, (∫ w, X l w i * X l w j ∂μ) = P i j) (w : Ξ) :
    Concentration.centeredEmpiricalCovariance μ X w = empiricalGram (fun l => X l w)-P := by
  have hn : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  ext i j
  simp only [Concentration.centeredEmpiricalCovariance, hP, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_div,
    mul_div_cancel_left₀ _ hn, Matrix.sub_apply, empiricalGram]

end SKConstants.Completion.LGram
