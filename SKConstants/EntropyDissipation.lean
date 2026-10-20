module

public import SKConstants.EntropyCoverage
public import SKConstants.FiniteChainSemigroup
public import SKConstants.FiniteGibbs
public import SKConstants.FiniteChainDirichlet
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

public section
noncomputable section
open scoped Classical Matrix

namespace SKConstants

theorem log_ratio_lower_bound (x : ℝ) (hx : 1 ≤ x) :
    2 * (x - 1) ≤ (x + 1) * Real.log x := by
  let g : ℝ → ℝ := fun y ↦ (y + 1) * Real.log y - 2 * (y - 1)
  have hg : ∀ y ∈ Set.Ici (1 : ℝ),
      HasDerivAt g (Real.log y + y⁻¹ - 1) y := by
    intro y hy
    have hypos : 0 < y := by simp only [Set.mem_Ici] at hy; linarith
    convert (((hasDerivAt_id y).add_const 1).mul (Real.hasDerivAt_log hypos.ne')) |>.sub
      (((hasDerivAt_id y).sub_const 1).const_mul 2) using 1
    · funext z
      change (z + 1) * Real.log z - 2 * (z - 1) =
        (z + 1) * Real.log z - 2 * (z - 1)
      rfl
    · dsimp
      field_simp
      ring
  have hmono : MonotoneOn g (Set.Ici (1 : ℝ)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (1 : ℝ))
      (fun y hy ↦ (hg y hy).continuousAt.continuousWithinAt)
      (fun y hy ↦ (hg y (interior_subset hy)).hasDerivWithinAt)
    intro y hy
    have hypos : 0 < y := by have := interior_subset hy; simp only [Set.mem_Ici] at this; linarith
    have h := Real.one_sub_inv_le_log_of_pos hypos
    linarith
  have h := hmono (by simp) hx hx
  dsimp [g] at h
  simp only [Real.log_one, mul_zero, sub_self] at h
  linarith

theorem log_sqrt_dissipation (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    4 * (Real.sqrt a - Real.sqrt b) ^ 2 ≤
      (a - b) * (Real.log a - Real.log b) := by
  wlog hab : b ≤ a generalizing a b
  · have h := this b a hb ha (le_of_not_ge hab)
    nlinarith
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsorder : Real.sqrt b ≤ Real.sqrt a := Real.sqrt_le_sqrt hab
  have hx : 1 ≤ Real.sqrt a / Real.sqrt b := (le_div_iff₀ hsb).mpr (by simpa using hsorder)
  have h := log_ratio_lower_bound (Real.sqrt a / Real.sqrt b) hx
  rw [Real.log_div hsa.ne' hsb.ne', Real.log_sqrt ha.le, Real.log_sqrt hb.le] at h
  have hmul := mul_le_mul_of_nonneg_left h
    (mul_nonneg (sub_nonneg.mpr hsorder) hsb.le)
  have hsa2 := Real.sq_sqrt ha.le
  have hsb2 := Real.sq_sqrt hb.le
  field_simp at hmul
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b)]

@[expose] def finiteShannonEntropy {V : Type*} [Fintype V] (pi : V → ℝ) : ℝ :=
  - ∑ x, pi x * Real.log (pi x)

@[expose] def finiteDensityEntropy {V : Type*} [Fintype V]
    (pi f : V → ℝ) : ℝ := ∑ x, pi x * (f x * Real.log (f x))

theorem finiteShannonEntropy_nonneg {V : Type*} [Fintype V]
    (pi : V → ℝ) (hpi : ∀ x, 0 < pi x) (hsum : ∑ x, pi x = 1) :
    0 ≤ finiteShannonEntropy pi := by
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro x _
  have hle : pi x ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun y _ ↦ (hpi y).le) (Finset.mem_univ x)
  exact mul_nonpos_of_nonneg_of_nonpos (hpi x).le (Real.log_nonpos (hpi x).le hle)

theorem finiteShannonEntropy_le_log_card {V : Type*} [Fintype V] [Nonempty V]
    (pi : V → ℝ) (hpi : ∀ x, 0 < pi x) (hsum : ∑ x, pi x = 1) :
    finiteShannonEntropy pi ≤ Real.log (Fintype.card V) := by
  have hcard : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have hq : ∀ _x : V, 0 < (1 : ℝ) / Fintype.card V := fun _ ↦ by positivity
  have hqsum : ∑ _x : V, (1 : ℝ) / Fintype.card V = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have h := finiteKL_nonneg pi (fun _ ↦ (1 : ℝ) / Fintype.card V) hpi hq hsum hqsum
  have hlog : ∀ x, Real.log (pi x / (1 / Fintype.card V)) =
      Real.log (pi x) + Real.log (Fintype.card V) := by
    intro x
    rw [div_div_eq_mul_div, div_one, Real.log_mul (hpi x).ne' hcard.ne']
  simp only [finiteKL, hlog, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, hsum, one_mul] at h
  unfold finiteShannonEntropy
  linarith

theorem finiteDensityEntropy_nonneg {V : Type*} [Fintype V]
    (pi f : V → ℝ) (hpi : ∀ x, 0 < pi x) (hf : ∀ x, 0 < f x)
    (hpi_sum : ∑ x, pi x = 1) (hf_sum : ∑ x, pi x * f x = 1) :
    0 ≤ finiteDensityEntropy pi f := by
  have h := finiteKL_nonneg (fun x ↦ pi x * f x) pi
    (fun x ↦ mul_pos (hpi x) (hf x)) hpi hf_sum hpi_sum
  have hratio : ∀ x, pi x * f x / pi x = f x :=
    fun x ↦ mul_div_cancel_left₀ (f x) (hpi x).ne'
  simpa only [finiteKL, hratio, finiteDensityEntropy, mul_assoc] using h

theorem finiteDensityEntropy_regularization_le {V : Type*} [Fintype V]
    (pi f : V → ℝ) (hpi : ∀ x, 0 ≤ pi x) (hf : ∀ x, 0 ≤ f x)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    finiteDensityEntropy pi (fun x ↦ (1 - eta) * f x + eta) ≤
      (1 - eta) * finiteDensityEntropy pi f := by
  have hpoint : ∀ x,
      ((1 - eta) * f x + eta) * Real.log ((1 - eta) * f x + eta) ≤
        (1 - eta) * (f x * Real.log (f x)) := by
    intro x
    have h := Real.convexOn_mul_log.2 (hf x) (show (0 : ℝ) ≤ 1 by norm_num)
      (sub_nonneg.mpr heta1) heta0 (show (1 - eta) + eta = 1 by ring)
    simpa only [smul_eq_mul, mul_one, Real.log_one, mul_zero, add_zero] using h
  unfold finiteDensityEntropy
  calc
    (∑ x, pi x * (((1 - eta) * f x + eta) * Real.log ((1 - eta) * f x + eta))) ≤
        ∑ x, pi x * ((1 - eta) * (f x * Real.log (f x))) :=
      Finset.sum_le_sum (fun x _ ↦ mul_le_mul_of_nonneg_left (hpoint x) (hpi x))
    _ = (1 - eta) * ∑ x, pi x * (f x * Real.log (f x)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

theorem finiteDensityEntropy_regularized_atom_le {V : Type*}
    [Fintype V] [DecidableEq V] (pi : V → ℝ) (hpi : ∀ x, 0 < pi x)
    (hsum : ∑ x, pi x = 1) (x : V) (eta : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    finiteDensityEntropy pi
      (fun y ↦ (1 - eta) * (if y = x then 1 / pi x else 0) + eta) ≤
        -Real.log (pi x) := by
  have h := finiteDensityEntropy_regularization_le pi
    (fun y ↦ if y = x then 1 / pi x else 0) (fun y ↦ (hpi y).le)
    (fun y ↦ by split_ifs; exact (one_div_pos.mpr (hpi x)).le; exact le_rfl) eta heta0 heta1
  have hatom : finiteDensityEntropy pi (fun y ↦ if y = x then 1 / pi x else 0) =
      -Real.log (pi x) := by
    unfold finiteDensityEntropy
    rw [Finset.sum_eq_single x]
    · simp only [↓reduceIte, Real.log_div one_ne_zero (hpi x).ne', Real.log_one]
      field_simp [(hpi x).ne']
      ring
    · intro y _ hyx
      simp [hyx]
    · simp
  rw [hatom] at h
  have hle : pi x ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun y _ ↦ (hpi y).le) (Finset.mem_univ x)
  have hlog : 0 ≤ -Real.log (pi x) := neg_nonneg.mpr (Real.log_nonpos (hpi x).le hle)
  exact h.trans (mul_le_of_le_one_left hlog (by linarith))

theorem gibbsShannonEntropy_le {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) :
    finiteShannonEntropy (gibbsProbability beta W) ≤ (n : ℝ) * Real.log 2 := by
  have h := finiteShannonEntropy_le_log_card (gibbsProbability beta W)
    (gibbsProbability_pos beta W) (gibbsProbability_sum beta W)
  simpa [Spin, Fintype.card_fun, Real.log_pow] using h

@[expose] def finiteEntropyProduction {V : Type*} [Fintype V]
    (pi : V → ℝ) (K : Matrix V V ℝ) (f : V → ℝ) : ℝ :=
  (1 / 2) * ∑ x, ∑ y, pi x * K x y *
    (f x - f y) * (Real.log (f x) - Real.log (f y))

theorem finiteDensityEntropy_hasDerivAt {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : K ∈ Matrix.rowStochastic ℝ V) (pi : V → ℝ)
    (hbalance : ∀ x y, pi x * K x y = pi y * K y x)
    (f : ℝ → V → ℝ) (t : ℝ) (hf : ∀ x, 0 < f t x)
    (hderiv : ∀ x, HasDerivAt (fun s ↦ f s x)
      ((finiteChainGenerator K *ᵥ f t) x) t) :
    HasDerivAt (fun s ↦ finiteDensityEntropy pi (f s))
      (-finiteEntropyProduction pi K (f t)) t := by
  have hd : ∀ x, HasDerivAt (fun s ↦ pi x * (f s x * Real.log (f s x)))
      (pi x * (Real.log (f t x) + 1) * (finiteChainGenerator K *ᵥ f t) x) t := by
    intro x
    convert ((Real.hasDerivAt_mul_log (hf x).ne').comp t (hderiv x)).const_mul (pi x)
      using 1
    · funext s
      simp only [Function.comp_def]
    · ring
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun x _ ↦ hd x)
  have hfun : (∑ x, fun s ↦ pi x * (f s x * Real.log (f s x))) =
      (fun s ↦ finiteDensityEntropy pi (f s)) := by
    funext s
    simp only [Finset.sum_apply, finiteDensityEntropy]
  rw [hfun] at hsum
  rw [finiteChain_summation_by_parts K hK pi hbalance] at hsum
  have heq : (∑ x, ∑ y, pi x * K x y *
      ((Real.log (f t x) + 1) - (Real.log (f t y) + 1)) * (f t x - f t y)) =
      ∑ x, ∑ y, pi x * K x y * (f t x - f t y) *
        (Real.log (f t x) - Real.log (f t y)) := by
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  simpa only [heq, finiteEntropyProduction, neg_mul] using hsum

theorem finiteEntropyProduction_ge_four_dirichlet {V : Type*}
    [Fintype V] [DecidableEq V] (K : Matrix V V ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ V) (pi f : V → ℝ)
    (hpi : ∀ x, 0 ≤ pi x) (hf : ∀ x, 0 < f x) :
    4 * finiteDirichletForm pi K (fun x ↦ Real.sqrt (f x)) ≤
      finiteEntropyProduction pi K f := by
  have hsum : (∑ x, ∑ y, pi x * K x y *
      (4 * (Real.sqrt (f x) - Real.sqrt (f y)) ^ 2)) ≤
      ∑ x, ∑ y, pi x * K x y * ((f x - f y) *
        (Real.log (f x) - Real.log (f y))) := by
    apply Finset.sum_le_sum
    intro x _
    apply Finset.sum_le_sum
    intro y _
    exact mul_le_mul_of_nonneg_left (log_sqrt_dissipation _ _ (hf x) (hf y))
      (mul_nonneg (hpi x) (Matrix.nonneg_of_mem_rowStochastic hK))
  have h := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  convert h using 1 <;> simp only [finiteDirichletForm, finiteEntropyProduction,
    Finset.mul_sum] <;>
    apply Finset.sum_congr rfl <;> intro x hx <;>
    apply Finset.sum_congr rfl <;> intro y hy <;> ring

theorem finiteEntropyProduction_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : K ∈ Matrix.rowStochastic ℝ V)
    (pi f : V → ℝ) (hpi : ∀ x, 0 ≤ pi x) (hf : ∀ x, 0 < f x) :
    0 ≤ finiteEntropyProduction pi K f :=
  (mul_nonneg (by norm_num) (finiteDirichletForm_nonneg K hK pi hpi _)).trans
    (finiteEntropyProduction_ge_four_dirichlet K hK pi f hpi hf)

theorem finiteChain_integrated_entropy_dissipation {V : Type*}
    [Fintype V] [DecidableEq V] (K : Matrix V V ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ V) (pi : V → ℝ)
    (hpi : ∀ x, 0 < pi x) (hpi_sum : ∑ x, pi x = 1)
    (hbalance : ∀ x y, pi x * K x y = pi y * K y x)
    (f : ℝ → V → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hfpos : ∀ s ∈ Set.uIcc 0 T, ∀ x, 0 < f s x)
    (hfnorm : ∑ x, pi x * f T x = 1)
    (hfderiv : ∀ s ∈ Set.uIcc 0 T, ∀ x,
      HasDerivAt (fun t ↦ f t x) ((finiteChainGenerator K *ᵥ f s) x) s) :
    (∫ s in 0..T, finiteDirichletForm pi K (fun x ↦ Real.sqrt (f s x))) ≤
      finiteDensityEntropy pi (f 0) / 4 := by
  have hfc : ∀ x, ContinuousOn (fun s ↦ f s x) (Set.uIcc 0 T) :=
    fun x s hs ↦ (hfderiv s hs x).continuousAt.continuousWithinAt
  have hlc : ∀ x, ContinuousOn (fun s ↦ Real.log (f s x)) (Set.uIcc 0 T) :=
    fun x ↦ (hfc x).log (fun s hs ↦ (hfpos s hs x).ne')
  have hpc : ContinuousOn (fun s ↦ finiteEntropyProduction pi K (f s)) (Set.uIcc 0 T) := by
    unfold finiteEntropyProduction
    apply continuousOn_const.mul
    apply continuousOn_finsetSum
    intro x _
    apply continuousOn_finsetSum
    intro y _
    exact (continuousOn_const.mul ((hfc x).sub (hfc y))).mul ((hlc x).sub (hlc y))
  have hec : ContinuousOn
      (fun s ↦ finiteDirichletForm pi K (fun x ↦ Real.sqrt (f s x)))
      (Set.uIcc 0 T) := by
    unfold finiteDirichletForm
    apply continuousOn_const.mul
    apply continuousOn_finsetSum
    intro x _
    apply continuousOn_finsetSum
    intro y _
    exact continuousOn_const.mul (((Real.continuous_sqrt.comp_continuousOn (hfc x)).sub
      (Real.continuous_sqrt.comp_continuousOn (hfc y))).pow 2)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs ↦ finiteDensityEntropy_hasDerivAt K hK pi hbalance f s
      (hfpos s hs) (hfderiv s hs)) (hpc.neg.intervalIntegrable (μ := MeasureTheory.volume))
  rw [intervalIntegral.integral_neg] at hFTC
  have hint := intervalIntegral.integral_mono_on hT
    ((hec.const_mul 4).intervalIntegrable (μ := MeasureTheory.volume))
    (hpc.intervalIntegrable (μ := MeasureTheory.volume))
    (fun s hs ↦ finiteEntropyProduction_ge_four_dirichlet K hK pi (f s)
      (fun x ↦ (hpi x).le) (hfpos s (by rwa [Set.uIcc_of_le hT]) ))
  rw [intervalIntegral.integral_const_mul] at hint
  have hnonneg := finiteDensityEntropy_nonneg pi (f T) hpi
    (hfpos T (Set.right_mem_uIcc)) hpi_sum hfnorm
  linarith

theorem finiteChain_regularized_dissipation_bound {V : Type*}
    [Fintype V] [DecidableEq V] (K : Matrix V V ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ V) (pi : V → ℝ)
    (hpi : ∀ x, 0 < pi x) (hpi_sum : ∑ x, pi x = 1)
    (hbalance : ∀ x y, pi x * K x y = pi y * K y x)
    (eta T : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1) (hT : 0 ≤ T) (x : V) :
    (∫ s in 0..T, finiteDirichletForm pi K
      (fun y ↦ Real.sqrt (finiteChainRegularizedDensity K pi eta s x y))) ≤
        -Real.log (pi x) / 4 := by
  have h := finiteChain_integrated_entropy_dissipation K hK pi hpi hpi_sum hbalance
    (fun s ↦ finiteChainRegularizedDensity K pi eta s x) T hT
    (fun s hs ↦ finiteChainRegularizedDensity_pos K hK pi hpi eta heta heta1 s
      (by rw [Set.uIcc_of_le hT] at hs; exact hs.1) x)
    (finiteChainRegularizedDensity_sum K hK pi hpi hpi_sum eta T hT x)
    (fun s _ ↦ finiteChainRegularizedDensity_hasDerivAt K hK pi hpi hbalance eta s x)
  have hzero : finiteChainRegularizedDensity K pi eta 0 x =
      fun y ↦ (1 - eta) * (if y = x then 1 / pi x else 0) + eta := by
    funext y
    by_cases hy : y = x
    · subst y
      simp [finiteChainRegularizedDensity, finiteChainDensity]
    · simp [finiteChainRegularizedDensity, finiteChainDensity,
        hy, Ne.symm hy]
  rw [hzero] at h
  exact h.trans (div_le_div_of_nonneg_right
    (finiteDensityEntropy_regularized_atom_le pi hpi hpi_sum x eta heta.le heta1)
    (by norm_num))

@[expose] def finiteChainAverageRegularizedDirichlet {V : Type*}
    [Fintype V] [DecidableEq V] (K : Matrix V V ℝ) (pi : V → ℝ)
    (eta t : ℝ) : ℝ :=
  ∑ x, pi x * finiteDirichletForm pi K
    (fun y ↦ Real.sqrt (finiteChainRegularizedDensity K pi eta t x y))

theorem finiteChain_regularized_average_dissipation {V : Type*}
    [Fintype V] [DecidableEq V] (K : Matrix V V ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ V) (pi : V → ℝ)
    (hpi : ∀ x, 0 < pi x) (hpi_sum : ∑ x, pi x = 1)
    (hbalance : ∀ x y, pi x * K x y = pi y * K y x)
    (eta T : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1) (hT : 0 ≤ T) :
    (∫ t in 0..T, finiteChainAverageRegularizedDirichlet K pi eta t) ≤
      finiteShannonEntropy pi / 4 := by
  have hfc : ∀ x y, Continuous (fun t ↦ finiteChainRegularizedDensity K pi eta t x y) :=
    fun x y ↦ continuous_iff_continuousAt.mpr
      (fun t ↦ (finiteChainRegularizedDensity_hasDerivAt K hK pi hpi hbalance eta t x y).continuousAt)
  have hec : ∀ x, Continuous (fun t ↦ finiteDirichletForm pi K
      (fun y ↦ Real.sqrt (finiteChainRegularizedDensity K pi eta t x y))) := by
    intro x
    unfold finiteDirichletForm
    apply continuous_const.mul
    apply continuous_finsetSum
    intro y _
    apply continuous_finsetSum
    intro z _
    exact continuous_const.mul (((Real.continuous_sqrt.comp (hfc x y)).sub
      (Real.continuous_sqrt.comp (hfc x z))).pow 2)
  unfold finiteChainAverageRegularizedDirichlet
  rw [intervalIntegral.integral_finsetSum
    (fun x _ ↦ ((hec x).const_mul (pi x)).intervalIntegrable 0 T)]
  simp_rw [intervalIntegral.integral_const_mul]
  calc
    (∑ x, pi x * ∫ t in 0..T, finiteDirichletForm pi K
        (fun y ↦ Real.sqrt (finiteChainRegularizedDensity K pi eta t x y))) ≤
        ∑ x, pi x * (-Real.log (pi x) / 4) :=
      Finset.sum_le_sum (fun x _ ↦ mul_le_mul_of_nonneg_left
        (finiteChain_regularized_dissipation_bound K hK pi hpi hpi_sum hbalance
          eta T heta heta1 hT x) (hpi x).le)
    _ = finiteShannonEntropy pi / 4 := by
      simp only [finiteShannonEntropy, mul_div_assoc, mul_neg, Finset.sum_div,
        Finset.sum_neg_distrib, neg_div]

end SKConstants
