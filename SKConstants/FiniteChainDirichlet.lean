module

public import SKConstants.FiniteChainSemigroup
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp

public section
noncomputable section
open scoped Matrix Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[expose] def finiteDirichletForm (pi : Ω → ℝ) (K : Matrix Ω Ω ℝ) (u : Ω → ℝ) : ℝ :=
  (1 / 2) * ∑ x, ∑ y, pi x * K x y * (u x - u y) ^ 2

theorem finiteChainSemigroup_hasDerivAt (K : Matrix Ω Ω ℝ) (t : ℝ) :
    HasDerivAt (finiteChainSemigroup K)
      (finiteChainSemigroup K t * finiteChainGenerator K) t :=
  hasDerivAt_exp_smul_const (finiteChainGenerator K) t

theorem finiteChainSemigroup_entry_hasDerivAt (K : Matrix Ω Ω ℝ) (t : ℝ) (x y : Ω) :
    HasDerivAt (fun s => finiteChainSemigroup K s x y)
      ((finiteChainSemigroup K t * finiteChainGenerator K) x y) t := by
  let ev : Matrix Ω Ω ℝ →L[ℝ] ℝ := {
    toLinearMap := {
      toFun := fun M => M x y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    cont := (continuous_apply y).comp (continuous_apply x) }
  have h := ev.hasFDerivAt.comp_hasDerivAt t (finiteChainSemigroup_hasDerivAt K t)
  simpa only [ev, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
    Function.comp_def] using h

theorem finiteChain_generator_pairing (K : Matrix Ω Ω ℝ)
    (pi g u : Ω → ℝ) :
    (∑ x, pi x * g x * (finiteChainGenerator K *ᵥ u) x) =
      (∑ x, ∑ y, pi x * K x y * g x * u y) - ∑ x, pi x * g x * u x := by
  have hLu : (finiteChainGenerator K *ᵥ u) = K *ᵥ u - u := by
    unfold finiteChainGenerator
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [hLu]
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, mul_sub,
    Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem finiteChain_pair_sum_diagonal (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (pi g u : Ω → ℝ) :
    (∑ x, ∑ y, pi x * K x y * g x * u x) = ∑ x, pi x * g x * u x := by
  apply Finset.sum_congr rfl
  intro x _
  calc
    (∑ y, pi x * K x y * g x * u x) =
        pi x * g x * u x * ∑ y, K x y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = pi x * g x * u x := by
      rw [Matrix.sum_row_of_mem_rowStochastic hK, mul_one]

omit [DecidableEq Ω] in
theorem finiteChain_pair_sum_swap (K : Matrix Ω Ω ℝ) (pi : Ω → ℝ)
    (hbalance : ∀ x y, pi x * K x y = pi y * K y x) (f : Ω → Ω → ℝ) :
    (∑ x, ∑ y, pi x * K x y * f x y) =
      ∑ x, ∑ y, pi x * K x y * f y x := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  rw [hbalance x y]

theorem finiteChain_summation_by_parts (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (pi : Ω → ℝ)
    (hbalance : ∀ x y, pi x * K x y = pi y * K y x) (g u : Ω → ℝ) :
    (∑ x, pi x * g x * (finiteChainGenerator K *ᵥ u) x) =
      -(1 / 2) * ∑ x, ∑ y, pi x * K x y * (g x - g y) * (u x - u y) := by
  have hdiag := finiteChain_pair_sum_diagonal K hK pi g u
  have hdiag' : (∑ x, ∑ y, pi x * K x y * g y * u y) = ∑ x, pi x * g x * u x := by
    calc
      (∑ x, ∑ y, pi x * K x y * g y * u y) =
          ∑ x, ∑ y, pi x * K x y * g x * u x := by
        simpa only [mul_assoc] using
          finiteChain_pair_sum_swap K pi hbalance (fun x y => g y * u y)
      _ = ∑ x, pi x * g x * u x := hdiag
  have hcross : (∑ x, ∑ y, pi x * K x y * g y * u x) =
      ∑ x, ∑ y, pi x * K x y * g x * u y := by
    simpa only [mul_assoc] using
      finiteChain_pair_sum_swap K pi hbalance (fun x y => g y * u x)
  have hexpand : (∑ x, ∑ y, pi x * K x y * (g x - g y) * (u x - u y)) =
      (∑ x, ∑ y, pi x * K x y * g x * u x) +
        (∑ x, ∑ y, pi x * K x y * g y * u y) -
        (∑ x, ∑ y, pi x * K x y * g x * u y) -
        (∑ x, ∑ y, pi x * K x y * g y * u x) := by
    calc
      (∑ x, ∑ y, pi x * K x y * (g x - g y) * (u x - u y)) =
          ∑ x, ∑ y, (pi x * K x y * g x * u x + pi x * K x y * g y * u y -
            pi x * K x y * g x * u y - pi x * K x y * g y * u x) := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [finiteChain_generator_pairing, hexpand, hdiag, hdiag', hcross]
  ring

theorem finiteDirichletForm_eq_neg_generator (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (pi : Ω → ℝ)
    (hbalance : ∀ x y, pi x * K x y = pi y * K y x) (u : Ω → ℝ) :
    finiteDirichletForm pi K u = -(∑ x, pi x * u x * (finiteChainGenerator K *ᵥ u) x) := by
  rw [finiteChain_summation_by_parts K hK pi hbalance u u]
  simp only [finiteDirichletForm, pow_two, mul_assoc]
  ring

theorem finiteDirichletForm_nonneg (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (pi : Ω → ℝ)
    (hpi : ∀ x, 0 ≤ pi x) (u : Ω → ℝ) :
    0 ≤ finiteDirichletForm pi K u := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg (mul_nonneg (hpi x) (Matrix.nonneg_of_mem_rowStochastic hK)) (sq_nonneg _)

@[expose] def finiteChainDensity (K : Matrix Ω Ω ℝ) (pi : Ω → ℝ)
    (t : ℝ) (x y : Ω) : ℝ := finiteChainSemigroup K t x y / pi y

@[expose] def finiteChainRegularizedDensity (K : Matrix Ω Ω ℝ) (pi : Ω → ℝ)
    (eta t : ℝ) (x y : Ω) : ℝ :=
  (1 - eta) * finiteChainDensity K pi t x y + eta

theorem finiteChainDensity_nonneg (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (pi : Ω → ℝ)
    (hpi : ∀ y, 0 < pi y) (t : ℝ) (ht : 0 ≤ t) (x y : Ω) :
    0 ≤ finiteChainDensity K pi t x y :=
  div_nonneg (Matrix.nonneg_of_mem_rowStochastic
    (finiteChainSemigroup_stochastic K hK t ht)) (hpi y).le

theorem finiteChainDensity_sum (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (pi : Ω → ℝ)
    (hpi : ∀ y, 0 < pi y) (t : ℝ) (ht : 0 ≤ t) (x : Ω) :
    (∑ y, pi y * finiteChainDensity K pi t x y) = 1 := by
  simp only [finiteChainDensity, mul_div_cancel₀ _ (hpi _).ne']
  exact Matrix.sum_row_of_mem_rowStochastic (finiteChainSemigroup_stochastic K hK t ht) x

theorem finiteChainDensity_stationary_average (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (pi : Ω → ℝ)
    (hpi : ∀ y, 0 < pi y)
    (hbalance : ∀ x y, pi x * K x y = pi y * K y x)
    (t : ℝ) (ht : 0 ≤ t) (y : Ω) :
    (∑ x, pi x * finiteChainDensity K pi t x y) = 1 := by
  simp only [finiteChainDensity, ← mul_div_assoc, ← Finset.sum_div]
  rw [finiteChainSemigroup_stationary K hK pi hbalance t ht y]
  exact div_self (hpi y).ne'

theorem finiteChainRegularizedDensity_pos (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (pi : Ω → ℝ)
    (hpi : ∀ y, 0 < pi y) (eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) (x y : Ω) :
    0 < finiteChainRegularizedDensity K pi eta t x y := by
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (sub_nonneg.mpr heta1) (finiteChainDensity_nonneg K hK pi hpi t ht x y)) heta

theorem finiteChainRegularizedDensity_sum (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (pi : Ω → ℝ)
    (hpi : ∀ y, 0 < pi y) (hpisum : ∑ y, pi y = 1)
    (eta t : ℝ) (ht : 0 ≤ t) (x : Ω) :
    (∑ y, pi y * finiteChainRegularizedDensity K pi eta t x y) = 1 := by
  simp only [finiteChainRegularizedDensity, mul_add]
  rw [Finset.sum_add_distrib]
  have hleft : (∑ y, pi y * ((1 - eta) * finiteChainDensity K pi t x y)) =
      (1 - eta) * ∑ y, pi y * finiteChainDensity K pi t x y := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hleft, finiteChainDensity_sum K hK pi hpi t ht x, ← Finset.sum_mul, hpisum]
  ring

theorem finiteChainDensity_generator (K : Matrix Ω Ω ℝ) (pi : Ω → ℝ)
    (hpi : ∀ y, 0 < pi y)
    (hbalance : ∀ x y, pi x * K x y = pi y * K y x)
    (t : ℝ) (x y : Ω) :
    ((finiteChainSemigroup K t * finiteChainGenerator K) x y) / pi y =
      (finiteChainGenerator K *ᵥ finiteChainDensity K pi t x) y := by
  have hterm : ∀ z, finiteChainSemigroup K t x z * K z y / pi y =
      K y z * (finiteChainSemigroup K t x z / pi z) := by
    intro z
    have h := hbalance z y
    field_simp [(hpi y).ne', (hpi z).ne']
    linear_combination finiteChainSemigroup K t x z * h
  unfold finiteChainGenerator
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mulVec, Matrix.one_mulVec]
  simp only [Matrix.sub_apply, Matrix.mul_apply, sub_div, Finset.sum_div,
    Pi.sub_apply, Matrix.mulVec, dotProduct, finiteChainDensity, hterm]

theorem finiteChainDensity_hasDerivAt (K : Matrix Ω Ω ℝ) (pi : Ω → ℝ)
    (hpi : ∀ y, 0 < pi y)
    (hbalance : ∀ x y, pi x * K x y = pi y * K y x)
    (t : ℝ) (x y : Ω) :
    HasDerivAt (fun s => finiteChainDensity K pi s x y)
      ((finiteChainGenerator K *ᵥ finiteChainDensity K pi t x) y) t := by
  have h := (finiteChainSemigroup_entry_hasDerivAt K t x y).div_const (pi y)
  rw [finiteChainDensity_generator K pi hpi hbalance t x y] at h
  exact h

theorem finiteChainGenerator_regularized (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (f : Ω → ℝ) (eta : ℝ) (y : Ω) :
    (finiteChainGenerator K *ᵥ (fun z => (1 - eta) * f z + eta)) y =
      (1 - eta) * (finiteChainGenerator K *ᵥ f) y := by
  unfold finiteChainGenerator
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  have hleft : (∑ z, K y z * ((1 - eta) * f z)) = (1 - eta) * ∑ z, K y z * f z := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [hleft, ← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hK]
  ring

theorem finiteChainRegularizedDensity_hasDerivAt (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (pi : Ω → ℝ)
    (hpi : ∀ y, 0 < pi y)
    (hbalance : ∀ x y, pi x * K x y = pi y * K y x)
    (eta t : ℝ) (x y : Ω) :
    HasDerivAt (fun s => finiteChainRegularizedDensity K pi eta s x y)
      ((finiteChainGenerator K *ᵥ finiteChainRegularizedDensity K pi eta t x) y) t := by
  have h := ((finiteChainDensity_hasDerivAt K pi hpi hbalance t x y).const_mul
    (1 - eta)).add_const eta
  rw [← finiteChainGenerator_regularized K hK (finiteChainDensity K pi t x) eta y] at h
  exact h

theorem finiteChainRegularizedDensity_stationary_average (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (pi : Ω → ℝ)
    (hpi : ∀ y, 0 < pi y) (hpisum : ∑ x, pi x = 1)
    (hbalance : ∀ x y, pi x * K x y = pi y * K y x)
    (eta t : ℝ) (ht : 0 ≤ t) (y : Ω) :
    (∑ x, pi x * finiteChainRegularizedDensity K pi eta t x y) = 1 := by
  simp only [finiteChainRegularizedDensity, mul_add, Finset.sum_add_distrib]
  have hleft : (∑ x, pi x * ((1 - eta) * finiteChainDensity K pi t x y)) =
      (1 - eta) * ∑ x, pi x * finiteChainDensity K pi t x y := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hleft, finiteChainDensity_stationary_average K hK pi hpi hbalance t ht y,
    ← Finset.sum_mul, hpisum]
  ring

end SKConstants
