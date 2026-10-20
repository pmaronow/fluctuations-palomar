module

public import SKConstants.EntropyCoverage
public import SKConstants.Crossing
public import SKConstants.FiniteGibbs

public section
noncomputable section
open scoped Classical

namespace SKConstants

@[expose] def finiteEventMass {Ω : Type*} [Fintype Ω]
    (r : Ω → ℝ) (P : Ω → Prop) : ℝ :=
  ∑ ω, if P ω then r ω else 0

theorem finiteEventMass_mono {Ω : Type*} [Fintype Ω]
    (r : Ω → ℝ) {P Q : Ω → Prop} (hr : ∀ ω, 0 ≤ r ω)
    (hPQ : ∀ ω, P ω → Q ω) : finiteEventMass r P ≤ finiteEventMass r Q := by
  unfold finiteEventMass
  apply Finset.sum_le_sum
  intro ω _
  by_cases hP : P ω
  · simp [hP, hPQ ω hP]
  · by_cases hQ : Q ω <;> simp [hP, hQ, hr ω]

theorem finiteEventMass_compl {Ω : Type*} [Fintype Ω]
    (r : Ω → ℝ) (P : Ω → Prop) (hr_sum : ∑ ω, r ω = 1) :
    finiteEventMass r (fun ω ↦ ¬ P ω) = 1 - finiteEventMass r P := by
  have hsum : finiteEventMass r P + finiteEventMass r (fun ω ↦ ¬ P ω) = 1 := by
    unfold finiteEventMass
    rw [← Finset.sum_add_distrib]
    convert hr_sum using 1
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hP : P ω <;> simp [hP]
  linarith

theorem finite_endpoint_rectangle_mass {V Ω : Type*}
    [Fintype V] [DecidableEq V] [Fintype Ω]
    (r : Ω → ℝ) (q : V → ℝ) (X Y : Ω → V) (A B : Finset V)
    (hjoint : ∀ u v, finiteEventMass r (fun ω ↦ X ω = u ∧ Y ω = v) = q u * q v) :
    finiteEventMass r (fun ω ↦ X ω ∈ A ∧ Y ω ∈ B) =
      (∑ u ∈ A, q u) * (∑ v ∈ B, q v) := by
  classical
  simp only [finiteEventMass]
  calc
    _ = ∑ ω, ∑ u ∈ A, ∑ v ∈ B,
          if X ω = u ∧ Y ω = v then r ω else 0 := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hx : X ω ∈ A
      · by_cases hy : Y ω ∈ B <;> simp [hx, hy, ite_and]
      · simp [hx, ite_and]
    _ = ∑ u ∈ A, ∑ v ∈ B, ∑ ω,
          if X ω = u ∧ Y ω = v then r ω else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
    _ = ∑ u ∈ A, ∑ v ∈ B, q u * q v := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      calc
        _ = finiteEventMass r (fun ω ↦ X ω = u ∧ Y ω = v) := by
          unfold finiteEventMass
          apply Finset.sum_congr rfl
          intro ω _
          by_cases h : X ω = u ∧ Y ω = v <;> simp [h]
        _ = q u * q v := hjoint u v
    _ = (∑ u ∈ A, q u) * (∑ v ∈ B, q v) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]

theorem finiteKL_balanced_endpoint_crossing {V Ω : Type*}
    [Fintype V] [DecidableEq V] [Fintype Ω]
    (p q : V → ℝ) (r : Ω → ℝ) (X Y : Ω → V)
    (A : Finset V) (K alpha : ℝ)
    (hp : ∀ u, 0 < p u) (hq : ∀ u, 0 < q u)
    (hp_sum : ∑ u, p u = 1) (hq_sum : ∑ u, q u = 1)
    (hKL : finiteKL p q ≤ K) (hAlpha : 0 < alpha)
    (hA : alpha ≤ ∑ u ∈ A, p u) (hAc : alpha ≤ ∑ u ∈ Aᶜ, p u)
    (hjoint : ∀ u v, finiteEventMass r (fun ω ↦ X ω = u ∧ Y ω = v) = q u * q v) :
    Real.exp (-2 * (K + Real.log 2) / alpha) ≤
      finiteEventMass r (fun ω ↦ X ω ∈ A ∧ Y ω ∉ A) := by
  have h₁ := finiteKL_uniform_coverage p q A K alpha hp hq hp_sum hq_sum
    hKL hAlpha hA
  have h₂ := finiteKL_uniform_coverage p q Aᶜ K alpha hp hq hp_sum hq_sum
    hKL hAlpha hAc
  have hprod := mul_le_mul h₁ h₂ (Real.exp_pos _).le
    (Finset.sum_nonneg (fun u _ ↦ (hq u).le))
  have hexp : Real.exp (-2 * (K + Real.log 2) / alpha) =
      Real.exp (-(K + Real.log 2) / alpha) *
        Real.exp (-(K + Real.log 2) / alpha) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  have hrect := finite_endpoint_rectangle_mass r q X Y A Aᶜ hjoint
  simpa only [Finset.mem_compl] using hprod.trans_eq hrect.symm

theorem finite_crossing_implies_bad {V Ω : Type*}
    (G : SimpleGraph V) (A : Set V) (f : Ω → ℕ → V)
    (coarse : Ω → ℕ → Prop) (good : Ω → Prop) (N R : ℕ)
    (hsteps : ∀ ω, good ω → ∀ i < N,
      G.edist (f ω i) (f ω (i + 1)) ≤ (R : ℕ∞))
    (hcoarse : ∀ ω, good ω → ∀ i < N, coarse ω i ∨ coarse ω (i + 1))
    (havoid : ∀ ω, good ω → ∀ i ≤ N, coarse ω i →
      f ω i ∉ graphTwoSidedBoundaryNeighborhood G A R) :
    ∀ ω, f ω 0 ∈ A ∧ f ω N ∉ A → ¬ good ω := by
  intro ω hcross hgood
  obtain ⟨i, hi, hflag, hnear⟩ := coarse_sampled_path_hits_twoSidedBoundary
    G A (f ω) (coarse ω) N R hcross.1 hcross.2
    (hsteps ω hgood) (hcoarse ω hgood)
  exact havoid ω hgood i hi hflag hnear

theorem finite_balanced_coarse_avoidance_bad_mass {V Ω : Type*}
    [Fintype V] [DecidableEq V] [Fintype Ω]
    (G : SimpleGraph V) (p q : V → ℝ) (r : Ω → ℝ)
    (A : Finset V) (f : Ω → ℕ → V)
    (coarse : Ω → ℕ → Prop) (good : Ω → Prop) (N R : ℕ) (K alpha : ℝ)
    (hp : ∀ u, 0 < p u) (hq : ∀ u, 0 < q u)
    (hp_sum : ∑ u, p u = 1) (hq_sum : ∑ u, q u = 1)
    (hr : ∀ ω, 0 ≤ r ω) (hr_sum : ∑ ω, r ω = 1)
    (hKL : finiteKL p q ≤ K) (hAlpha : 0 < alpha)
    (hA : alpha ≤ ∑ u ∈ A, p u) (hAc : alpha ≤ ∑ u ∈ Aᶜ, p u)
    (hjoint : ∀ u v,
      finiteEventMass r (fun ω ↦ f ω 0 = u ∧ f ω N = v) = q u * q v)
    (hsteps : ∀ ω, good ω → ∀ i < N,
      G.edist (f ω i) (f ω (i + 1)) ≤ (R : ℕ∞))
    (hcoarse : ∀ ω, good ω → ∀ i < N, coarse ω i ∨ coarse ω (i + 1))
    (havoid : ∀ ω, good ω → ∀ i ≤ N, coarse ω i →
      f ω i ∉ graphTwoSidedBoundaryNeighborhood G (A : Set V) R) :
    Real.exp (-2 * (K + Real.log 2) / alpha) ≤
      finiteEventMass r (fun ω ↦ ¬ good ω) ∧
    finiteEventMass r good ≤ 1 - Real.exp (-2 * (K + Real.log 2) / alpha) := by
  have hcross := finiteKL_balanced_endpoint_crossing p q r
    (fun ω ↦ f ω 0) (fun ω ↦ f ω N) A K alpha hp hq hp_sum hq_sum
    hKL hAlpha hA hAc hjoint
  have hbad := finite_crossing_implies_bad G (A : Set V) f coarse good N R
    hsteps hcoarse havoid
  have hmass : Real.exp (-2 * (K + Real.log 2) / alpha) ≤
      finiteEventMass r (fun ω ↦ ¬ good ω) :=
    hcross.trans (finiteEventMass_mono r hr hbad)
  refine ⟨hmass, ?_⟩
  rw [finiteEventMass_compl r good hr_sum] at hmass
  linarith

theorem finite_balanced_coarse_avoidance_contradiction {V Ω : Type*}
    [Fintype V] [DecidableEq V] [Fintype Ω]
    (G : SimpleGraph V) (p q : V → ℝ) (r : Ω → ℝ)
    (A : Finset V) (f : Ω → ℕ → V)
    (coarse : Ω → ℕ → Prop) (good : Ω → Prop) (N R : ℕ) (K alpha : ℝ)
    (hp : ∀ u, 0 < p u) (hq : ∀ u, 0 < q u)
    (hp_sum : ∑ u, p u = 1) (hq_sum : ∑ u, q u = 1)
    (hr : ∀ ω, 0 ≤ r ω) (hr_sum : ∑ ω, r ω = 1)
    (hKL : finiteKL p q ≤ K) (hAlpha : 0 < alpha)
    (hA : alpha ≤ ∑ u ∈ A, p u) (hAc : alpha ≤ ∑ u ∈ Aᶜ, p u)
    (hjoint : ∀ u v,
      finiteEventMass r (fun ω ↦ f ω 0 = u ∧ f ω N = v) = q u * q v)
    (hsteps : ∀ ω, good ω → ∀ i < N,
      G.edist (f ω i) (f ω (i + 1)) ≤ (R : ℕ∞))
    (hcoarse : ∀ ω, good ω → ∀ i < N, coarse ω i ∨ coarse ω (i + 1))
    (havoid : ∀ ω, good ω → ∀ i ≤ N, coarse ω i →
      f ω i ∉ graphTwoSidedBoundaryNeighborhood G (A : Set V) R)
    (hsmall : finiteEventMass r (fun ω ↦ ¬ good ω) <
      Real.exp (-2 * (K + Real.log 2) / alpha)) : False := by
  have h := (finite_balanced_coarse_avoidance_bad_mass G p q r A f coarse good
    N R K alpha hp hq hp_sum hq_sum hr hr_sum hKL hAlpha hA hAc
    hjoint hsteps hcoarse havoid).1
  exact (not_lt_of_ge h) hsmall

@[expose] def finiteEndpointProductLaw {V : Type*}
    (q : V → ℝ) (uv : V × V) : ℝ := q uv.1 * q uv.2

theorem finiteEndpointProductLaw_sum {V : Type*} [Fintype V]
    (q : V → ℝ) (hq_sum : ∑ u, q u = 1) :
    (∑ uv : V × V, finiteEndpointProductLaw q uv) = 1 := by
  unfold finiteEndpointProductLaw
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, hq_sum, one_mul]

theorem finiteEndpointProductLaw_joint {V : Type*}
    [Fintype V] [DecidableEq V] (q : V → ℝ) (u v : V) :
    finiteEventMass (finiteEndpointProductLaw q)
      (fun uv ↦ uv.1 = u ∧ uv.2 = v) = q u * q v := by
  simp [finiteEventMass, finiteEndpointProductLaw, Fintype.sum_prod_type, ite_and]

theorem finite_product_balanced_coarse_avoidance_bad_mass {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (p q : V → ℝ) (A : Finset V)
    (f : (V × V) → ℕ → V) (coarse : (V × V) → ℕ → Prop)
    (good : (V × V) → Prop) (N R : ℕ) (K alpha : ℝ)
    (hp : ∀ u, 0 < p u) (hq : ∀ u, 0 < q u)
    (hp_sum : ∑ u, p u = 1) (hq_sum : ∑ u, q u = 1)
    (hKL : finiteKL p q ≤ K) (hAlpha : 0 < alpha)
    (hA : alpha ≤ ∑ u ∈ A, p u) (hAc : alpha ≤ ∑ u ∈ Aᶜ, p u)
    (hfirst : ∀ uv, f uv 0 = uv.1) (hlast : ∀ uv, f uv N = uv.2)
    (hsteps : ∀ uv, good uv → ∀ i < N,
      G.edist (f uv i) (f uv (i + 1)) ≤ (R : ℕ∞))
    (hcoarse : ∀ uv, good uv → ∀ i < N, coarse uv i ∨ coarse uv (i + 1))
    (havoid : ∀ uv, good uv → ∀ i ≤ N, coarse uv i →
      f uv i ∉ graphTwoSidedBoundaryNeighborhood G (A : Set V) R) :
    Real.exp (-2 * (K + Real.log 2) / alpha) ≤
      finiteEventMass (finiteEndpointProductLaw q) (fun uv ↦ ¬ good uv) ∧
    finiteEventMass (finiteEndpointProductLaw q) good ≤
      1 - Real.exp (-2 * (K + Real.log 2) / alpha) := by
  apply finite_balanced_coarse_avoidance_bad_mass G p q
    (finiteEndpointProductLaw q) A f coarse good N R K alpha
    hp hq hp_sum hq_sum
    (fun uv ↦ mul_nonneg (hq uv.1).le (hq uv.2).le)
    (finiteEndpointProductLaw_sum q hq_sum) hKL hAlpha hA hAc
    ?_ hsteps hcoarse havoid
  intro u v
  simpa only [hfirst, hlast] using finiteEndpointProductLaw_joint q u v

theorem finiteGibbs_balanced_coarse_avoidance_bad_mass {n : ℕ}
    {Ω : Type*} [Fintype Ω]
    (beta : ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (G : SimpleGraph (Spin n)) (q : Spin n → ℝ) (r : Ω → ℝ)
    (A : Finset (Spin n)) (f : Ω → ℕ → Spin n)
    (coarse : Ω → ℕ → Prop) (good : Ω → Prop) (N R : ℕ) (K alpha : ℝ)
    (hq : ∀ u, 0 < q u) (hq_sum : ∑ u, q u = 1)
    (hr : ∀ ω, 0 ≤ r ω) (hr_sum : ∑ ω, r ω = 1)
    (hKL : finiteKL (gibbsProbability beta W) q ≤ K) (hAlpha : 0 < alpha)
    (hA : alpha ≤ ∑ u ∈ A, gibbsProbability beta W u)
    (hAc : alpha ≤ ∑ u ∈ Aᶜ, gibbsProbability beta W u)
    (hjoint : ∀ u v,
      finiteEventMass r (fun ω ↦ f ω 0 = u ∧ f ω N = v) = q u * q v)
    (hsteps : ∀ ω, good ω → ∀ i < N,
      G.edist (f ω i) (f ω (i + 1)) ≤ (R : ℕ∞))
    (hcoarse : ∀ ω, good ω → ∀ i < N, coarse ω i ∨ coarse ω (i + 1))
    (havoid : ∀ ω, good ω → ∀ i ≤ N, coarse ω i →
      f ω i ∉ graphTwoSidedBoundaryNeighborhood G (A : Set (Spin n)) R) :
    Real.exp (-2 * (K + Real.log 2) / alpha) ≤
      finiteEventMass r (fun ω ↦ ¬ good ω) ∧
    finiteEventMass r good ≤ 1 - Real.exp (-2 * (K + Real.log 2) / alpha) := by
  exact finite_balanced_coarse_avoidance_bad_mass G (gibbsProbability beta W)
    q r A f coarse good N R K alpha (gibbsProbability_pos beta W) hq
    (gibbsProbability_sum beta W) hq_sum hr hr_sum hKL hAlpha hA hAc
    hjoint hsteps hcoarse havoid

end SKConstants
