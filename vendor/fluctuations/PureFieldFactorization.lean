module

public import SKFluctuationsOAI.Probability.SKFluctuations.CavityFactorization
public import SKFluctuationsOAI.Probability.SKFluctuations.NonnegativeProfileValueStep
public import SKFluctuationsOAI.Probability.SKFluctuations.OrderedSKRateDirection

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def independentSiteFeature {ι : Type*} [Fintype ι] (σ : ι → Bool) :
    (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, spinValue (σ i) • ContinuousLinearMap.proj i

def independentSiteWeight {ι : Type*} [Fintype ι] (_ : ι → Bool) : ℝ :=
  ∏ _i : ι, (1 / 2 : ℝ)

def siteSteps {ι : Type*} (steps : List (GaussianStep ι)) (i : ι) :
    List (GaussianStep (Fin 1)) :=
  steps.map (fun p => (p.1, fun _ => p.2 i))

theorem siteSteps_ordered {ι : Type*} {steps : List (GaussianStep ι)} {a : ℝ}
    (ha : OrderedSteps a steps) (i : ι) : OrderedSteps a (siteSteps steps i) := by
  induction steps generalizing a with
  | nil => exact ha
  | cons p tail ih =>
    exact ⟨ha.1, ha.2.1, ha.2.2.1, ih ha.2.2.2⟩

theorem independent_site_log_partition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) :
    spinLogPartition (independentSiteWeight (ι := ι)) independentSiteFeature x =
      ∑ i, spinLogPartition (fun _ : Bool => (1 / 2 : ℝ)) scalarFeature
        (fun _ => x i) := by
  classical
  have hp : spinPartition (independentSiteWeight (ι := ι)) independentSiteFeature x =
      ∏ i, spinPartition (fun _ : Bool => (1 / 2 : ℝ)) scalarFeature
        (fun _ => x i) := by
    simp only [spinPartition, independentSiteWeight, independentSiteFeature,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, Real.exp_sum]
    simp_rw [← Finset.prod_mul_distrib]
    simpa [scalarFeature, spinValue] using
      (Fintype.prod_sum (fun i (σ : Bool) =>
        (1 / 2 : ℝ) * Real.exp (spinValue σ * x i))).symm
  unfold spinLogPartition
  rw [hp, Real.log_prod]
  intro i _
  exact (spinPartition_pos (by intro σ; norm_num)
    scalarFeature (fun _ => x i)).ne'

theorem independent_site_hierarchy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps)
    (x : ι → ℝ) :
    gaussianHierarchy (independentSiteWeight (ι := ι)) independentSiteFeature steps x =
      ∑ i, gaussianHierarchy (fun _ : Bool => (1 / 2 : ℝ)) scalarFeature
        (siteSteps steps i) (fun _ => x i) := by
  classical
  induction steps generalizing a x with
  | nil => exact independent_site_log_partition x
  | cons p tail ih =>
    obtain ⟨m, q⟩ := p
    have ht := ha.2.2.2
    have hfun := funext (fun y => ih ht y)
    have hr (i : ι) (z : Fin 1 → ℝ) :
        (fun _ : Fin 1 => x i + z 0) = (fun _ => x i) + z := by
      funext j
      simp only [Fin.fin_one_eq_zero j, Pi.add_apply]
    have hcont (i : ι) : Continuous (fun z : ℝ => Real.exp
        (m * gaussianHierarchy (fun _ : Bool => (1 / 2 : ℝ))
          scalarFeature (siteSteps tail i) (fun _ => x i + z))) := by
      apply Real.continuous_exp.comp
      apply Continuous.const_mul
      exact (gaussianHierarchy_continuous (by intro σ; norm_num)
        scalarFeature _ (siteSteps_ordered ht i)).comp (by fun_prop)
    simp only [gaussianHierarchy, siteSteps, List.map_cons]
    rw [hfun]
    unfold shiftedContinuation
    simp_rw [Finset.mul_sum, Real.exp_sum, Pi.add_apply]
    rw [integral_fintype_prod_eq_prod (fun i (z : ℝ) =>
      Real.exp (m * gaussianHierarchy (fun _ : Bool => (1 / 2 : ℝ))
        scalarFeature (siteSteps tail i) (fun _ => x i + z))), Real.log_prod]
    · rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      have he := integral_gaussian_eval (0 : Fin 1) (q i)
        (f := fun z => Real.exp (m * gaussianHierarchy
          (fun _ : Bool => (1 / 2 : ℝ)) scalarFeature (siteSteps tail i)
          (fun _ => x i + z))) (hcont i)
      simp_rw [hr] at he
      exact congrArg (fun z => Real.log z / m) he.symm
    · intro i _
      have hi := gaussianHierarchy_integrable (w := fun _ : Bool => (1 / 2 : ℝ))
        (by intro σ; norm_num)
        scalarFeature (siteSteps tail i) (siteSteps_ordered ht i) m
        (fun _ => q i) (fun _ => x i)
      have he := integral_gaussian_eval (0 : Fin 1) (q i)
        (f := fun z => Real.exp (m * gaussianHierarchy
          (fun _ : Bool => (1 / 2 : ℝ)) scalarFeature (siteSteps tail i)
          (fun _ => x i + z))) (hcont i)
      have hp := partition_pos m hi
      simp_rw [hr] at he
      rw [← he]
      exact hp.ne'

theorem diagonalBoundarySteps_zeroRow {ι κ : Type*} (as : List PositiveMass)
    (l : ι → ℝ) (q : ℕ → ι → ℝ) :
    diagonalBoundarySteps as (Sum.elim l (fun _ : κ => 0))
        (fun j => Sum.elim (q j) (fun _ => 0)) =
      zeroRowSteps (diagonalBoundarySteps as l q) := by
  induction as generalizing l q with
  | nil => rfl
  | cons a as ih =>
    simp only [diagonalBoundarySteps, zeroRowSteps, List.map_cons]
    congr 1
    · congr 1
      funext i
      cases i <;> simp
    · exact ih _ _

theorem disorderPressure_zeroRow {ι κ S : Type*} [Fintype ι] [Fintype κ]
    [Fintype S] (w : S → ℝ) (φ : S → (ι ⊕ κ → ℝ) →L[ℝ] ℝ)
    (C : ι ⊕ κ → ℝ) (as : List PositiveMass) (l : ι → ℝ)
    (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    disorderPressure w φ C as (Sum.elim l (fun _ => 0))
        (fun j => Sum.elim (q j) (fun _ => 0)) (cavityEmbed x) =
      disorderPressure w (fun s => (φ s).comp cavityEmbed)
        (fun i => C (.inl i)) as l q x := by
  unfold disorderPressure zeroContinuation
  rw [diagonalBoundarySteps_zeroRow]
  have hq : (fun i : ι ⊕ κ => Real.toNNReal
      (Sum.elim (q 0) (fun _ => 0) i - Sum.elim l (fun _ => 0) i)) =
      Sum.elim (fun i => Real.toNNReal (q 0 i - l i)) (fun _ => 0) := by
    funext i
    cases i <;> simp
  simp_rw [show ∀ i : ι ⊕ κ, Real.toNNReal
    (Sum.elim (q 0) (fun _ => 0) i - Sum.elim l (fun _ => 0) i) =
      Sum.elim (fun i => Real.toNNReal (q 0 i - l i)) (fun _ => 0) i from
        fun i => congrFun hq i]
  rw [integral_zeroRowGaussian]
  simp_rw [← map_add, gaussianHierarchy_zeroRow]
  simp [Fintype.sum_sum_type]

theorem siteSteps_diagonalBoundarySteps {ι : Type*} (as : List PositiveMass)
    (l : ι → ℝ) (q : ℕ → ι → ℝ) (i : ι) :
    siteSteps (diagonalBoundarySteps as l q) i =
      diagonalBoundarySteps as (fun _ : Fin 1 => l i) (fun j _ => q j i) := by
  induction as generalizing l q with
  | nil => rfl
  | cons a as ih =>
    simp only [diagonalBoundarySteps, siteSteps, List.map_cons]
    exact congrArg _ (ih _ _)

def scalarFieldPressure (as : List PositiveMass) (h : ℕ → ℝ) : ℝ :=
  disorderPressure (fun _ : Bool => (1 / 2 : ℝ)) scalarFeature
    (fun _ => 1) as 0 (fun j _ => h j) 0

theorem independent_site_pressure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (as : List PositiveMass) (ho : as.Pairwise (fun a b => a.val ≤ b.val))
    (hu : ∀ a ∈ as, a.val ≤ 1) (h : ℕ → ℝ) :
    disorderPressure (independentSiteWeight (ι := ι)) independentSiteFeature
        (fun _ => 1) as 0 (fun j _ => h j) 0 =
      (Fintype.card ι : ℝ) * scalarFieldPressure as h := by
  classical
  let steps : List (GaussianStep ι) :=
    diagonalBoundarySteps as (fun _ => h 0) (fun j _ => h (j + 1))
  let scalarSteps : List (GaussianStep (Fin 1)) :=
    diagonalBoundarySteps as (fun _ => h 0) (fun j _ => h (j + 1))
  have ha : OrderedSteps 0 steps :=
    diagonalBoundarySteps_ordered as le_rfl zero_le_one ho hu
      (fun a _ => a.property.le) _ _
  have hsa : OrderedSteps 0 scalarSteps :=
    diagonalBoundarySteps_ordered as le_rfl zero_le_one ho hu
      (fun a _ => a.property.le) _ _
  have hs (i : ι) : siteSteps steps i = scalarSteps :=
    siteSteps_diagonalBoundarySteps as _ _ i
  have hc : Continuous (fun z : ℝ => gaussianHierarchy
      (fun _ : Bool => (1 / 2 : ℝ)) scalarFeature scalarSteps (fun _ => z)) :=
    (gaussianHierarchy_continuous (by intro σ; norm_num) scalarFeature _ hsa).comp
      (by fun_prop)
  have hi (i : ι) : Integrable (fun z : ι → ℝ => gaussianHierarchy
      (fun _ : Bool => (1 / 2 : ℝ)) scalarFeature scalarSteps (fun _ => z i))
      (Measure.pi fun _ : ι => gaussianReal 0 (Real.toNNReal (h 0))) := by
    obtain ⟨L, hL⟩ := (gaussianHierarchy_regular
      (w := fun _ : Bool => (1 / 2 : ℝ)) (by intro σ; norm_num)
      scalarFeature scalarSteps hsa 0).1
    let P : (ι → ℝ) →L[ℝ] (Fin 1 → ℝ) :=
      ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.proj i)
    have hp := hL.comp P.lipschitzWith
    have h := (exponentialIncrement_gaussian
      (fun _ : ι => Real.toNNReal (h 0))).integrable_lipschitz hp 0
    have heP (z : ι → ℝ) : P z = (fun _ : Fin 1 => z i) := by
      funext j
      rfl
    simpa only [zero_add, Function.comp_def, heP] using h
  unfold scalarFieldPressure disorderPressure zeroContinuation
  simp only [Pi.zero_apply, sub_zero, zero_add, mul_one]
  have hf (z : ι → ℝ) : gaussianHierarchy (independentSiteWeight (ι := ι))
      independentSiteFeature steps z = ∑ i, gaussianHierarchy
        (fun _ : Bool => (1 / 2 : ℝ)) scalarFeature scalarSteps (fun _ => z i) := by
    rw [independent_site_hierarchy steps ha]
    simp_rw [hs]
  change (∫ z, gaussianHierarchy _ _ steps z
      ∂Measure.pi fun _ : ι => gaussianReal 0 (Real.toNNReal (h 0))) -
      (1 / 2 : ℝ) * ∑ _i : ι, h as.length = _
  simp_rw [hf]
  rw [integral_finset_sum _ (fun i _ => hi i)]
  simp_rw [integral_gaussian_eval _ _ hc]
  have he := integral_gaussian_eval (0 : Fin 1) (Real.toNNReal (h 0)) hc
  have hfin (z : Fin 1 → ℝ) : (fun _ : Fin 1 => z 0) = z := by
    funext j
    simp only [Fin.fin_one_eq_zero j]
  simp_rw [hfin] at he
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [he]
  simp only [scalarSteps, Fintype.card_fin, Nat.cast_one, mul_one]
  ring

theorem orderedFeature_field_restriction (n : ℕ) (σ : Spin n) :
    (orderedFeature n σ).comp (cavityEmbed (κ := Fin n × Fin n)) =
      independentSiteFeature σ := by
  ext x
  simp [orderedFeature_apply, independentSiteFeature, Fintype.sum_sum_type,
    orderedFeatureCoefficient]

theorem uniformWeight_eq_independentSiteWeight (n : ℕ) :
    uniformWeight n = independentSiteWeight (ι := Fin n) := by
  funext σ
  simp [uniformWeight, independentSiteWeight, zpow_neg, one_div_pow]

theorem orderedSKPressure_pure_field (n : ℕ) (hn : 0 < n)
    (as : List PositiveMass) (ho : as.Pairwise (fun a b => a.val ≤ b.val))
    (hu : ∀ a ∈ as, a.val ≤ 1) (h : ℕ → ℝ) :
    orderedSKPressure n as (fun _ => 0) h 0 = scalarFieldPressure as h := by
  classical
  have hq : orderedClock n (fun _ => 0) h =
      fun j => Sum.elim (fun _ : Fin n => h j) (fun _ => 0) := by
    funext j i
    cases i <;> rfl
  have hl : Sum.elim (0 : Fin n → ℝ) (fun _ : Fin n × Fin n => 0) =
      (0 : OrderedFeatureIndex n → ℝ) := by
    funext i
    cases i <;> rfl
  have hx : cavityEmbed (κ := Fin n × Fin n) (0 : Fin n → ℝ) =
      (0 : OrderedFeatureIndex n → ℝ) := by
    funext i
    cases i <;> rfl
  have hd := disorderPressure_zeroRow (uniformWeight n) (orderedFeature n)
    (fun i => (orderedAmplitude n i) ^ 2) as (0 : Fin n → ℝ)
    (fun j _ => h j) (0 : Fin n → ℝ)
  simp only [hl, hx] at hd
  unfold orderedSKPressure
  rw [hq, hd]
  simp_rw [orderedFeature_field_restriction]
  simp only [orderedAmplitude, one_pow]
  rw [uniformWeight_eq_independentSiteWeight,
    independent_site_pressure as ho hu h, Fintype.card_fin]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn.ne')

theorem realOrderedSKPathPressure_pure_field (n : ℕ) (hn : 0 < n)
    (h : ℝ → ℝ) (hh : MonotoneOn h (Icc (0 : ℝ) 1)) (hh0 : 0 ≤ h 0) :
    realOrderedSKPathPressure n (fun _ => 0) h 0 =
      realOrderedSKPathPressure 1 (fun _ => 0) h 0 := by
  have htn := orderedSKPressure_samples_tendsto n hn (fun _ => 0) h
    (fun _ _ _ _ _ => le_rfl) hh le_rfl hh0 0
  have ht1 := orderedSKPressure_samples_tendsto 1 (by norm_num) (fun _ => 0) h
    (fun _ _ _ _ _ => le_rfl) hh le_rfl hh0 0
  apply tendsto_nhds_unique htn
  apply ht1.congr'
  apply Eventually.of_forall
  intro k
  have ha := uniformMasses_ordered k
  dsimp only
  rw [orderedSKPressure_pure_field n hn _ ha.pairwise ha.members_le_one,
    orderedSKPressure_pure_field 1 (by norm_num) _ ha.pairwise ha.members_le_one]

theorem scalar_boundarySchedule_eq_hierarchy (as : List PositiveMass)
    (l : ℝ) (q : ℕ → ℝ) (x : Fin 1 → ℝ) :
    (scalarTerminal.boundarySchedule as l q).F x =
      gaussianHierarchy (fun _ : Bool => (1 / 2 : ℝ)) scalarFeature
        (diagonalBoundarySteps as (fun _ => l) (fun j _ => q j)) x := by
  induction as generalizing l q x with
  | nil =>
    change spinLogPartition (fun _ : Bool => (1 / 2 : ℝ)) scalarFeature (0 + x) = _
    rw [zero_add]
    rfl
  | cons a as ih =>
    simp only [HeatJet.boundarySchedule, diagonalBoundarySteps, gaussianHierarchy]
    change clockContinuation a.val (scalarTerminal.boundarySchedule as
      (q 0) (fun j => q (j + 1))).F (q 0 - l) x = _
    unfold clockContinuation
    rw [funext (ih (q 0) (fun j => q (j + 1)))]

theorem scalarFieldPressure_eq_rootBoundarySchedule
    (as : List PositiveMass) (h : ℕ → ℝ) :
    scalarFieldPressure as h = scalarTerminal.rootBoundarySchedule as 0 h 0 -
      h as.length / 2 := by
  unfold scalarFieldPressure disorderPressure HeatJet.rootBoundarySchedule
  rw [funext (scalar_boundarySchedule_eq_hierarchy as (h 0) (fun j => h (j + 1)))]
  simp [Fin.sum_univ_one, zeroContinuation]
  ring

end OAI.SKFluctuations.LaplaceWindowFormalization
