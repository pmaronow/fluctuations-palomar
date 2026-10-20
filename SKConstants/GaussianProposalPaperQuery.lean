module

public import SKConstants.GaussianProposalSKNormalization
import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix
namespace SKConstants.GaussianProposal

variable {Ambient : Type*} [Fintype Ambient] [DecidableEq Ambient]

@[expose] def unitNormalize (v : Ambient → ℝ) : Ambient → ℝ :=
  (Real.sqrt (dot v v))⁻¹ • v

theorem dot_self_nonneg (v : Ambient → ℝ) : 0 ≤ dot v v := by
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

theorem dot_self_eq_zero_iff (v : Ambient → ℝ) : dot v v = 0 ↔ v = 0 := by
  constructor
  · intro h
    ext i
    have hterm : v i * v i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (v j))).mp h i
        (Finset.mem_univ i)
    exact (mul_self_eq_zero.mp hterm)
  · rintro rfl
    simp [dot]

theorem unitNormalize_unit (v : Ambient → ℝ) (hv : v ≠ 0) :
    dot (unitNormalize v) (unitNormalize v) = 1 := by
  have hpos : 0 < dot v v := lt_of_le_of_ne (dot_self_nonneg v)
    (Ne.symm (fun h => hv ((dot_self_eq_zero_iff v).mp h)))
  have hs : Real.sqrt (dot v v) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hterm (i : Ambient) : ((Real.sqrt (dot v v))⁻¹ * v i) *
      ((Real.sqrt (dot v v))⁻¹ * v i) = (Real.sqrt (dot v v))⁻¹ ^ 2 * (v i * v i) := by ring
  change (∑ i, ((Real.sqrt (dot v v))⁻¹ * v i) *
    ((Real.sqrt (dot v v))⁻¹ * v i)) = 1
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  change (Real.sqrt (dot v v))⁻¹ ^ 2 * dot v v = 1
  calc
    _ = (Real.sqrt (dot v v))⁻¹ ^ 2 * (Real.sqrt (dot v v)) ^ 2 := by
      rw [Real.sq_sqrt (dot_self_nonneg v)]
    _ = 1 := by field_simp

@[expose] def firstNonzeroVector {m : ℕ} : (n : ℕ) → (Fin n → Fin m → ℝ) → Fin m → ℝ
  | 0, _ => 0
  | n + 1, vs => if vs 0 = 0 then firstNonzeroVector n (fun j => vs j.succ) else vs 0

theorem firstNonzeroVector_nonzero {m : ℕ} (n : ℕ) (vs : Fin n → Fin m → ℝ)
    (hv : ∃ j, vs j ≠ 0) : firstNonzeroVector n vs ≠ 0 := by
  induction n with
  | zero => obtain ⟨j, _⟩ := hv; exact Fin.elim0 j
  | succ n ih =>
    by_cases h0 : vs 0 = 0
    · simp only [firstNonzeroVector, h0, ↓reduceIte]
      apply ih
      obtain ⟨j, hj⟩ := hv
      refine Fin.cases ?_ (fun j hj => ⟨j, hj⟩) j hj
      simpa [h0] using hj
    · simp only [firstNonzeroVector, h0, ↓reduceIte]
      exact h0

theorem firstNonzeroVector_selected {m : ℕ} (n : ℕ) (vs : Fin n → Fin m → ℝ)
    (hv : ∃ j, vs j ≠ 0) : ∃ j, firstNonzeroVector n vs = vs j ∧
      vs j ≠ 0 ∧ ∀ i, i < j → vs i = 0 := by
  induction n with
  | zero => obtain ⟨j, _⟩ := hv; exact Fin.elim0 j
  | succ n ih =>
    by_cases h0 : vs 0 = 0
    · have htail : ∃ j : Fin n, vs j.succ ≠ 0 := by
        obtain ⟨j, hj⟩ := hv
        refine Fin.cases ?_ (fun j hj => ⟨j, hj⟩) j hj
        simpa [h0] using hj
      obtain ⟨j, hj, hn, hmin⟩ := ih (fun j => vs j.succ) htail
      refine ⟨j.succ, ?_, hn, ?_⟩
      · simpa only [firstNonzeroVector, h0, ↓reduceIte] using hj
      · intro i hi
        refine Fin.cases ?_ (fun i hi => hmin i (by simpa using hi)) i hi
        exact fun _ => h0
    · refine ⟨0, ?_, h0, ?_⟩
      · simp only [firstNonzeroVector, h0, ↓reduceIte]
      · intro i hi
        exact False.elim (Fin.not_lt_zero i hi)

@[expose] def paperDirection {m n : ℕ} (embedding : Matrix (Fin (m + 1)) (Fin n) ℝ)
    (target : Fin n → ℝ) : Fin (m + 1) → ℝ :=
  unitNormalize (if embedding *ᵥ target = 0 then
    firstNonzeroVector n (fun j i => embedding i j) else embedding *ᵥ target)

theorem paperDirection_unit {m n : ℕ}
    (embedding : Matrix (Fin (m + 1)) (Fin n) ℝ) (target : Fin n → ℝ)
    (horth : ∀ i j, dot (embedding i) (embedding j) = if i = j then 1 else 0) :
    dot (paperDirection embedding target) (paperDirection embedding target) = 1 := by
  apply unitNormalize_unit
  split_ifs with h
  · apply firstNonzeroVector_nonzero
    by_contra hnone
    push_neg at hnone
    have hzero : embedding 0 = 0 := by
      ext j
      exact congrFun (hnone j) 0
    have hnorm := horth 0 0
    simp [hzero, dot] at hnorm
  · exact h

theorem unitNormalize_measurable {A : Type*} [MeasurableSpace A]
    (v : A → Ambient → ℝ) (hv : ∀ i, Measurable (fun a => v a i)) :
    Measurable (fun a => unitNormalize (v a)) := by
  apply Measurable.of_eval
  intro i
  have hd : Measurable (fun a => dot (v a) (v a)) := by
    unfold dot
    fun_prop
  exact hd.sqrt.inv.mul (hv i)

theorem firstNonzeroVector_measurable {A : Type*} [MeasurableSpace A] {m : ℕ}
    (n : ℕ) (vs : A → Fin n → Fin m → ℝ)
    (hv : ∀ j i, Measurable (fun a => vs a j i)) :
    Measurable (fun a => firstNonzeroVector n (vs a)) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun a => if vs a 0 = 0 then
      firstNonzeroVector n (fun j => vs a j.succ) else vs a 0)
    exact Measurable.ite (measurableSet_eq_fun
      (Measurable.of_eval (hv 0)) measurable_const)
      (ih (fun a j => vs a j.succ) (fun j => hv j.succ))
      (Measurable.of_eval (hv 0))

theorem paperDirection_measurable {A : Type*} [MeasurableSpace A] {m n : ℕ}
    (embedding : A → Matrix (Fin (m + 1)) (Fin n) ℝ) (target : A → Fin n → ℝ)
    (he : ∀ i j, Measurable (fun a => embedding a i j))
    (ht : ∀ j, Measurable (fun a => target a j)) :
    Measurable (fun a => paperDirection (embedding a) (target a)) := by
  have hw : Measurable (fun a => embedding a *ᵥ target a) := by
    apply Measurable.of_eval
    intro i
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  apply unitNormalize_measurable
  intro i
  exact (measurable_pi_apply i).comp ((Measurable.ite (measurableSet_eq_fun hw measurable_const)
    (firstNonzeroVector_measurable n (fun a j i => embedding a i j) (fun j i => he i j))
    hw))

@[expose] def paperFrame {m n : ℕ} (embedding : Matrix (Fin (m + 1)) (Fin n) ℝ)
    (target : Fin n → ℝ) : Matrix (Fin (m + 1)) (Fin n) ℝ :=
  completionFrame 0 (paperDirection embedding target) * embedding

theorem rotateRectangularFrame_orthogonal {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (B : Matrix ι ι ℝ) (E : Matrix ι κ ℝ)
    (hB : ∀ i j, dot (B i) (B j) = if i = j then 1 else 0)
    (hE : ∀ i j, dot (E i) (E j) = if i = j then 1 else 0) (i j : ι) :
    dot ((B * E) i) ((B * E) j) = if i = j then 1 else 0 := by
  have hEE : E * Eᵀ = 1 := by
    ext i j
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, dot] using hE i j
  have hBB : B * Bᵀ = 1 := by
    ext i j
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, dot] using hB i j
  have hprod : (B * E) * (B * E)ᵀ = 1 := by
    rw [Matrix.transpose_mul]
    calc
      _ = B * (E * Eᵀ) * Bᵀ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hEE, Matrix.mul_one, hBB]
  have hh := congrArg (fun M : Matrix ι ι ℝ => M i j) hprod
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, dot] using hh

theorem paperFrame_orthogonal {m n : ℕ}
    (embedding : Matrix (Fin (m + 1)) (Fin n) ℝ) (target : Fin n → ℝ)
    (horth : ∀ i j, dot (embedding i) (embedding j) = if i = j then 1 else 0) (i j) :
    dot (paperFrame embedding target i) (paperFrame embedding target j) =
      if i = j then 1 else 0 :=
  rotateRectangularFrame_orthogonal _ _
    (completionFrame_orthogonal 0 (paperDirection embedding target)) horth i j

theorem paperFrame_designated_row {m n : ℕ}
    (embedding : Matrix (Fin (m + 1)) (Fin n) ℝ) (target : Fin n → ℝ)
    (horth : ∀ i j, dot (embedding i) (embedding j) = if i = j then 1 else 0) :
    paperFrame embedding target 0 = (paperDirection embedding target) ᵥ* embedding := by
  ext j
  unfold paperFrame
  rw [Matrix.mul_apply]
  simp_rw [completionFrame_designated_row 0 (paperDirection embedding target)
    (paperDirection_unit embedding target horth)]
  rfl

theorem paperFrame_projected_target {m n : ℕ}
    (embedding : Matrix (Fin (m + 1)) (Fin n) ℝ) (target : Fin n → ℝ)
    (horth : ∀ i j, dot (embedding i) (embedding j) = if i = j then 1 else 0)
    (h : embedding *ᵥ target ≠ 0) :
    paperFrame embedding target 0 =
      (Real.sqrt (dot (embedding *ᵥ target) (embedding *ᵥ target)))⁻¹ •
        ((embeddingᵀ * embedding) *ᵥ target) := by
  rw [paperFrame_designated_row embedding target horth]
  simp only [paperDirection, h, ↓reduceIte, unitNormalize, Matrix.smul_vecMul]
  rw [Matrix.vecMul_mulVec, ← Matrix.mulVec_transpose]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]

theorem paperFrame_zero_fallback {m n : ℕ}
    (embedding : Matrix (Fin (m + 1)) (Fin n) ℝ) (target : Fin n → ℝ)
    (horth : ∀ i j, dot (embedding i) (embedding j) = if i = j then 1 else 0)
    (h : embedding *ᵥ target = 0) :
    ∃ j : Fin n,
      paperFrame embedding target 0 = unitNormalize (fun i => embedding i j) ᵥ* embedding ∧
      (fun i => embedding i j) ≠ 0 ∧ ∀ l, l < j → (fun i => embedding i l) = 0 := by
  have hex : ∃ j, (fun i => embedding i j) ≠ 0 := by
    by_contra hn
    push Not at hn
    have he0 : embedding 0 = 0 := by ext j; exact congrFun (hn j) 0
    have hh := horth 0 0
    simp [he0, dot] at hh
  obtain ⟨j, hj, hnonzero, hfirst⟩ := firstNonzeroVector_selected n
    (fun j i => embedding i j) hex
  refine ⟨j, ?_, hnonzero, hfirst⟩
  rw [paperFrame_designated_row embedding target horth]
  simp only [paperDirection, h, ↓reduceIte, hj]

theorem paperFrame_measurable {A : Type*} [MeasurableSpace A] {m n : ℕ}
    (embedding : A → Matrix (Fin (m + 1)) (Fin n) ℝ) (target : A → Fin n → ℝ)
    (he : ∀ i j, Measurable (fun a => embedding a i j))
    (ht : ∀ j, Measurable (fun a => target a j)) (i j) :
    Measurable (fun a => paperFrame (embedding a) (target a) i j) := by
  have hd (i) : Measurable (fun a => paperDirection (embedding a) (target a) i) :=
    (measurable_pi_apply i).comp (paperDirection_measurable embedding target he ht)
  have hH (i j) : Measurable (fun a => completionFrame 0
      (paperDirection (embedding a) (target a)) i j) :=
    completionFrame_measurable 0 (fun a => paperDirection (embedding a) (target a)) hd i j
  unfold paperFrame
  simp only [Matrix.mul_apply]
  fun_prop

end SKConstants.GaussianProposal
