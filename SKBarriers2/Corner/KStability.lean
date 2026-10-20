module

public import SKBarriers2.Corner.CrudeC1
public import SKBarriers2.Corner.TerminalJets
public import SKBarriers2.Analysis.ParamStep

@[expose] public section

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic
open scoped Topology BigOperators

namespace SKBarriers2.Corner

local notation "E" => (Fin 3 → ℝ)

def quadraticGridMass (α : ℝ → ℝ) (s h a b c : ℝ) (k : ℝ) : ℝ :=
  α (s + h * (a + b * k ^ 2)) / c

theorem quadraticGridTime_hasDerivAt (s h a b k : ℝ) :
    HasDerivAt (fun t : ℝ => s + h * (a + b * t ^ 2)) (2 * h * b * k) k := by
  convert! (((((hasDerivAt_id k).pow 2).const_mul b).const_add a).const_mul h).const_add s
    using 1
  simp only [id_eq]
  ring

theorem quadraticGridMass_hasDerivAt {α : ℝ → ℝ} {s h a b c k : ℝ}
    (hα : DifferentiableAt ℝ α (s + h * (a + b * k ^ 2))) :
    HasDerivAt (quadraticGridMass α s h a b c)
      (deriv α (s + h * (a + b * k ^ 2)) * (2 * h * b * k) / c) k := by
  exact (hα.hasDerivAt.comp k (quadraticGridTime_hasDerivAt s h a b k)).div_const c

theorem quadraticGridMass_second_deriv {α : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hα : ContDiffOn ℝ 2 α U) {s h a b c k : ℝ}
    (ht : s + h * (a + b * k ^ 2) ∈ U) :
    deriv (deriv (quadraticGridMass α s h a b c)) k =
      (deriv (deriv α) (s + h * (a + b * k ^ 2)) * (2 * h * b * k) ^ 2 +
        deriv α (s + h * (a + b * k ^ 2)) * (2 * h * b)) / c := by
  let τ : ℝ → ℝ := fun t => s + h * (a + b * t ^ 2)
  have hτ : Continuous τ := by fun_prop
  have hα₁ : ContDiffAt ℝ 1 (deriv α) (τ k) :=
    (hα.deriv_of_isOpen hU (by norm_num)).contDiffAt (hU.mem_nhds ht)
  have heq : deriv (quadraticGridMass α s h a b c) =ᶠ[𝓝 k]
      (fun t => deriv α (τ t) * (2 * h * b * t) / c) := by
    have hmem : ∀ᶠ t in 𝓝 k, τ t ∈ U := hτ.continuousAt.eventually (hU.mem_nhds ht)
    filter_upwards [hmem] with t htm
    exact (quadraticGridMass_hasDerivAt
      ((hα.contDiffAt (hU.mem_nhds htm)).differentiableAt (by norm_num))).deriv
  have hlin : HasDerivAt (fun t : ℝ => 2 * h * b * t) (2 * h * b) k := by
    simpa only [mul_one, id_eq] using (hasDerivAt_id k).const_mul (2 * h * b)
  have hD := (((hα₁.differentiableAt (by norm_num)).hasDerivAt.comp k
    (quadraticGridTime_hasDerivAt s h a b k)).mul hlin).div_const c
  change HasDerivAt (fun t => deriv α (τ t) * (2 * h * b * t) / c)
    ((deriv (deriv α) (τ k) * (2 * h * b * k) * (2 * h * b * k) +
      deriv α (τ k) * (2 * h * b)) / c) k at hD
  rw [heq.deriv_eq]
  rw [hD.deriv]
  dsimp only [τ]
  ring

theorem quadraticGridMass_contDiffAt {α : ℝ → ℝ} {s h a b c k : ℝ}
    (hα : ContDiffAt ℝ 2 α (s + h * (a + b * k ^ 2))) :
    ContDiffAt ℝ 2 (quadraticGridMass α s h a b c) k := by
  exact (hα.comp k (by fun_prop)).div_const c

theorem quadraticGridMass_deriv_bounds {α : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hα : ContDiffOn ℝ 2 α U) {s h a b c k M A : ℝ}
    (ht : s + h * (a + b * k ^ 2) ∈ U)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hk : |k| ≤ 1 / 2)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hb : |b| ≤ A) (hc : 1 ≤ c)
    (hfirst : |deriv α (s + h * (a + b * k ^ 2))| ≤ M)
    (hsecond : |deriv (deriv α) (s + h * (a + b * k ^ 2))| ≤ M) :
    |deriv (quadraticGridMass α s h a b c) k| ≤ (M * A) * h ∧
    |deriv (deriv (quadraticGridMass α s h a b c)) k| ≤
      (M * (A ^ 2 + 2 * A)) * h := by
  have hc0 : 0 < c := by linarith
  have htα := (hα.contDiffAt (hU.mem_nhds ht)).differentiableAt (by norm_num)
  have htime : |2 * h * b * k| ≤ h * A := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg hh]
    calc
      2 * h * |b| * |k| ≤ 2 * h * A * (1 / 2) := by gcongr
      _ = h * A := by ring
  have haccel : |2 * h * b| ≤ 2 * h * A := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hh]
    gcongr
  have hsquare : (h * A) ^ 2 ≤ h * A ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg hh (sub_nonneg.mpr hh1)) (sq_nonneg A)]
  constructor
  · rw [(quadraticGridMass_hasDerivAt htα).deriv, abs_div, abs_mul, abs_of_pos hc0]
    calc
      _ ≤ (M * (h * A)) / c := by gcongr
      _ ≤ M * (h * A) := div_le_self (by positivity) hc
      _ = (M * A) * h := by ring
  · rw [quadraticGridMass_second_deriv hU hα ht, abs_div, abs_of_pos hc0]
    apply (div_le_self (abs_nonneg _) hc).trans
    calc
      _ ≤ |deriv (deriv α) (s + h * (a + b * k ^ 2)) * (2 * h * b * k) ^ 2| +
          |deriv α (s + h * (a + b * k ^ 2)) * (2 * h * b)| := abs_add_le _ _
      _ ≤ M * (h * A) ^ 2 + M * (2 * h * A) := by
        apply add_le_add
        · rw [abs_mul, abs_pow]
          exact mul_le_mul hsecond (pow_le_pow_left₀ (abs_nonneg _) htime 2)
            (by positivity) hM
        · rw [abs_mul]
          exact mul_le_mul hfirst haccel (abs_nonneg _) hM
      _ ≤ M * (h * A ^ 2) + M * (2 * h * A) := by gcongr
      _ = (M * (A ^ 2 + 2 * A)) * h := by ring

def kStageTimeConstant (x : ℝ) : Fin 6 → ℝ :=
  ![x, 1 + x / 2, 1 + x / 2, 3 / 2 + x / 2, 2, 2 + 2 * x]

def kStageTimeQuadratic (x : ℝ) : Fin 6 → ℝ :=
  ![0, 0, 0, 0, (44 / 9) * x, (44 / 9) * (1 - x)]

def kStageMassDivisor : Fin 6 → ℝ := ![3, 2, 1, 1, 1, 1]

def kStageMass (α : ℝ → ℝ) (s h x : ℝ) (σ : Fin 6) : ℝ → ℝ :=
  quadraticGridMass α s h (kStageTimeConstant x σ)
    (kStageTimeQuadratic x σ) (kStageMassDivisor σ)

theorem kStageMass_repair_tail (α : ℝ → ℝ) (s h x k : ℝ) :
    kStageMass α s h x 4 k = α (s + h * (2 + OW.repairLength (1 / 2) k * x)) ∧
    kStageMass α s h x 5 k =
      α (s + h * (2 + OW.repairLength (1 / 2) k +
        (2 - OW.repairLength (1 / 2) k) * x)) := by
  have hL : OW.repairLength (1 / 2) k = (44 / 9) * k ^ 2 := by
    norm_num [OW.repairLength, SKOptimized.Overshoot.varianceCoefficient,
      SKOptimized.Overshoot.tentWeight, SKOptimized.Overshoot.rampWeight]
    ring
  constructor
  · change α (s + h * (2 + (44 / 9) * x * k ^ 2)) / 1 = _
    rw [div_one, hL]
    congr 1
    ring
  · change α (s + h * (2 + 2 * x + (44 / 9) * (1 - x) * k ^ 2)) / 1 = _
    rw [div_one, hL]
    congr 1
    ring

theorem kStageMass_coefficients {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (σ : Fin 6) :
    |kStageTimeQuadratic x σ| ≤ 5 ∧ 1 ≤ kStageMassDivisor σ := by
  fin_cases σ <;>
    norm_num [kStageTimeQuadratic, kStageMassDivisor] <;>
    rw [abs_of_nonneg (by nlinarith [hx.1, hx.2])] <;> nlinarith [hx.1, hx.2]

theorem kStageTime_mem {x k : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hk : |k| ≤ 1 / 2) (σ : Fin 6) :
    kStageTimeConstant x σ + kStageTimeQuadratic x σ * k ^ 2 ∈ Icc (0 : ℝ) 4 := by
  have hk2 : k ^ 2 ≤ 1 / 4 := by
    have H := (sq_le_sq₀ (abs_nonneg k) (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr hk
    nlinarith [sq_abs k]
  have hxk : 0 ≤ x * k ^ 2 := mul_nonneg hx.1 (sq_nonneg k)
  have hxk' : 0 ≤ (1 - x) * k ^ 2 := mul_nonneg (sub_nonneg.mpr hx.2) (sq_nonneg k)
  have hupper : (1 - x) * k ^ 2 ≤ (1 - x) * (1 / 4) :=
    mul_le_mul_of_nonneg_left hk2 (sub_nonneg.mpr hx.2)
  have hupper' : x * k ^ 2 ≤ x * (1 / 4) := mul_le_mul_of_nonneg_left hk2 hx.1
  fin_cases σ <;>
    norm_num [kStageTimeConstant, kStageTimeQuadratic] <;>
    constructor <;> nlinarith [hx.1, hx.2]

theorem kStageMass_deriv_bounds {α : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hα : ContDiffOn ℝ 2 α U) {s h x k M : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hk : |k| ≤ 1 / 2)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hM : 0 ≤ M) (σ : Fin 6)
    (ht : s + h * (kStageTimeConstant x σ + kStageTimeQuadratic x σ * k ^ 2) ∈ U)
    (hfirst : |deriv α (s + h *
      (kStageTimeConstant x σ + kStageTimeQuadratic x σ * k ^ 2))| ≤ M)
    (hsecond : |deriv (deriv α) (s + h *
      (kStageTimeConstant x σ + kStageTimeQuadratic x σ * k ^ 2))| ≤ M) :
    ContDiffAt ℝ 2 (kStageMass α s h x σ) k ∧
      |deriv (kStageMass α s h x σ) k| ≤ (35 * M) * h ∧
      |deriv (deriv (kStageMass α s h x σ)) k| ≤ (35 * M) * h := by
  obtain ⟨hb, hc⟩ := kStageMass_coefficients hx σ
  have H := quadraticGridMass_deriv_bounds hU hα ht hh hh1 hk hM
    (by norm_num : (0 : ℝ) ≤ 5) hb hc hfirst hsecond
  refine ⟨quadraticGridMass_contDiffAt (hα.contDiffAt (hU.mem_nhds ht)), ?_, ?_⟩
  · exact H.1.trans (by nlinarith [mul_nonneg hM hh])
  · simpa only [kStageMass, show (5 : ℝ) ^ 2 + 2 * 5 = 35 from by norm_num,
      mul_comm M 35] using H.2

def kStabilityInteriorRadius (q l u : ℝ) : ℝ :=
  min 1 (min (l / 2) ((q - u) / 6))

theorem kStabilityInteriorRadius_pos {q l u : ℝ} (hl : 0 < l) (hu : u < q) :
    0 < kStabilityInteriorRadius q l u := by
  exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))

theorem kStability_time_mem {q l u r h t : ℝ} (hr : r ∈ Icc l u)
    (hh : 0 ≤ h) (hh0 : h ≤ kStabilityInteriorRadius q l u)
    (ht : t ∈ Icc (0 : ℝ) 4) :
    r - h + h * t ∈ Icc (l / 2) ((u + q) / 2) := by
  have hh₁ : h ≤ l / 2 := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hh₂ : h ≤ (q - u) / 6 := hh0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hprod : 0 ≤ h * t := mul_nonneg hh ht.1
  have hprod' : h * t ≤ 4 * h := by nlinarith [mul_nonneg hh (sub_nonneg.mpr ht.2)]
  constructor <;> linarith [hr.1, hr.2]

theorem scalarData_profile_two_derivs_bounded {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hu : u < D.q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (l / 2) ((u + D.q) / 2),
      |deriv (cdf (D.μ : Measure ℝ)) t| ≤ M ∧
      |deriv (deriv (cdf (D.μ : Measure ℝ))) t| ≤ M := by
  have hsub : Icc (l / 2) ((u + D.q) / 2) ⊆ Ioo (0 : ℝ) D.q := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hd₁ := D.smooth.deriv_of_isOpen isOpen_Ioo (m := 2) (by simp)
  have hd₂ := hd₁.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hc : ContinuousOn (fun t => |deriv (cdf (D.μ : Measure ℝ)) t| +
      |deriv (deriv (cdf (D.μ : Measure ℝ))) t|)
      (Icc (l / 2) ((u + D.q) / 2)) :=
    (hd₁.continuousOn.abs.add hd₂.continuousOn.abs).mono hsub
  have hne : (Icc (l / 2) ((u + D.q) / 2)).Nonempty :=
    nonempty_Icc.mpr (by linarith)
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hc
  refine ⟨|deriv (cdf (D.μ : Measure ℝ)) t| +
    |deriv (deriv (cdf (D.μ : Measure ℝ))) t|,
    add_nonneg (abs_nonneg _) (abs_nonneg _), ?_⟩
  intro y hy
  have H := hmax hy
  change |deriv (cdf (D.μ : Measure ℝ)) y| +
    |deriv (deriv (cdf (D.μ : Measure ℝ))) y| ≤
    |deriv (cdf (D.μ : Measure ℝ)) t| +
    |deriv (deriv (cdf (D.μ : Measure ℝ))) t| at H
  constructor <;> linarith [abs_nonneg (deriv (cdf (D.μ : Measure ℝ)) y),
    abs_nonneg (deriv (deriv (cdf (D.μ : Measure ℝ))) y)]

theorem scalarData_window_mass_budget {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hu : u < D.q) :
    ∃ C h₀ : ℝ, 0 ≤ C ∧ 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ N : ℕ, 1 ≤ N → ∀ j : ℕ, j < N → ∀ σ : Fin 6,
      ∀ k : ℝ, |k| ≤ 1 / 2 →
        ContDiffAt ℝ 2 (kStageMass (cdf (D.μ : Measure ℝ))
          (r - h) h ((j : ℝ) / (N : ℝ)) σ) k ∧
        |deriv (kStageMass (cdf (D.μ : Measure ℝ))
          (r - h) h ((j : ℝ) / (N : ℝ)) σ) k| ≤ C * h ∧
        |deriv (deriv (kStageMass (cdf (D.μ : Measure ℝ))
          (r - h) h ((j : ℝ) / (N : ℝ)) σ)) k| ≤ C * h := by
  obtain ⟨M, hM, hbound⟩ := scalarData_profile_two_derivs_bounded D hl hlu hu
  refine ⟨35 * M, kStabilityInteriorRadius D.q l u, by positivity,
    kStabilityInteriorRadius_pos hl hu, ?_⟩
  intro r hr h hh hh0 N hN j hj σ k hk
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hx : (j : ℝ) / (N : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg j) hNr.le
    · exact (div_le_one hNr).mpr (by exact_mod_cast hj.le)
  have ht := kStability_time_mem hr hh.le hh0 (kStageTime_mem hx hk σ)
  have ht' : r - h + h * (kStageTimeConstant ((j : ℝ) / (N : ℝ)) σ +
      kStageTimeQuadratic ((j : ℝ) / (N : ℝ)) σ * k ^ 2) ∈ Ioo (0 : ℝ) D.q := by
    constructor <;> linarith [ht.1, ht.2]
  exact kStageMass_deriv_bounds isOpen_Ioo (D.smooth.of_le (by simp)) hx hk hh.le
    (hh0.trans (min_le_left _ _)) hM σ ht' (hbound _ ht).1 (hbound _ ht).2

def kDirectionShape : Fin 12 → ℝ → E :=
  ![SKOptimized.Overshoot.commonVector (1 / 2),
    (fun k => Real.sqrt (1 / 2) • SKOptimized.Overshoot.sharedVector (1 / 2) k),
    (fun k => Real.sqrt (1 / 2) • SKOptimized.Overshoot.rampVector (1 / 2) k),
    (fun k => Real.sqrt (1 / 2) • SKOptimized.Overshoot.rampVector (1 / 2) k),
    (fun k => Real.sqrt (1 / 2) • SKOptimized.Overshoot.postXVector (1 / 2) k),
    (fun k => Real.sqrt (1 / 2) • SKOptimized.Overshoot.postYVector (1 / 2) k),
    (fun k => (k * Real.sqrt (44 / 9)) • SKOptimized.Overshoot.rampVector (1 / 2) 0),
    (fun k => (k * Real.sqrt (44 / 9)) •
      ((1 / Real.sqrt 2) • SKOptimized.Overshoot.sharedVector (1 / 2) 0)),
    (fun k => (k * Real.sqrt (44 / 9)) •
      ((1 / 2 : ℝ) • SKOptimized.Overshoot.contrast)),
    (fun k => Real.sqrt (2 - (44 / 9) * k ^ 2) • Pi.single 0 1),
    (fun k => Real.sqrt (2 - (44 / 9) * k ^ 2) • Pi.single 1 1),
    (fun k => Real.sqrt (2 - (44 / 9) * k ^ 2) • Pi.single 2 1)]

theorem kDirectionShape_contDiffOn (σ : Fin 12) :
    ContDiffOn ℝ 2 (kDirectionShape σ) (Ioo (-(3 / 5) : ℝ) (3 / 5)) := by
  have htail : ContDiffOn ℝ 2 (fun k : ℝ => Real.sqrt (2 - (44 / 9) * k ^ 2))
      (Ioo (-(3 / 5) : ℝ) (3 / 5)) := by
    apply ContDiffOn.sqrt (by fun_prop)
    intro k hk
    have hsq : k ^ 2 < 9 / 25 := by nlinarith [hk.1, hk.2]
    have hpos : 0 < 2 - (44 / 9) * k ^ 2 := by nlinarith
    exact hpos.ne'
  fin_cases σ <;> dsimp only [kDirectionShape]
  all_goals first
    | exact htail.smul contDiffOn_const
    | apply contDiffOn_pi.mpr
      intro i
      fin_cases i <;>
        norm_num [SKOptimized.Overshoot.commonVector, SKOptimized.Overshoot.sharedVector,
          SKOptimized.Overshoot.rampVector, SKOptimized.Overshoot.postXVector,
          SKOptimized.Overshoot.postYVector, SKOptimized.Overshoot.contrast,
          Pi.smul_apply] <;> fun_prop

theorem exists_kDirectionShape_bound :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ σ : Fin 12, ∀ k : ℝ, |k| ≤ 1 / 2 →
      ‖kDirectionShape σ k‖ ≤ A ∧ ‖deriv (kDirectionShape σ) k‖ ≤ A ∧
        ‖deriv (deriv (kDirectionShape σ)) k‖ ≤ A := by
  have hb (σ : Fin 12) : ∃ A : ℝ, 0 ≤ A ∧ ∀ k ∈ Icc (-(1 / 2) : ℝ) (1 / 2),
      ‖kDirectionShape σ k‖ + ‖deriv (kDirectionShape σ) k‖ +
        ‖deriv (deriv (kDirectionShape σ)) k‖ ≤ A := by
    have hf := kDirectionShape_contDiffOn σ
    have hd := hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
    have hdd := hd.deriv_of_isOpen isOpen_Ioo (m := 0) (by norm_num)
    have hsub : Icc (-(1 / 2) : ℝ) (1 / 2) ⊆ Ioo (-(3 / 5) : ℝ) (3 / 5) := by
      intro k hk
      constructor <;> linarith [hk.1, hk.2]
    have hc : ContinuousOn (fun k => ‖kDirectionShape σ k‖ +
        ‖deriv (kDirectionShape σ) k‖ + ‖deriv (deriv (kDirectionShape σ)) k‖)
        (Icc (-(1 / 2) : ℝ) (1 / 2)) :=
      ((hf.continuousOn.norm.add hd.continuousOn.norm).add hdd.continuousOn.norm).mono hsub
    obtain ⟨k, hk, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (show (Icc (-(1 / 2) : ℝ) (1 / 2)).Nonempty from ⟨0, by norm_num⟩) hc
    refine ⟨‖kDirectionShape σ k‖ + ‖deriv (kDirectionShape σ) k‖ +
      ‖deriv (deriv (kDirectionShape σ)) k‖, by positivity, ?_⟩
    intro t ht
    exact hmax ht
  choose A hA hbound using hb
  refine ⟨∑ σ, A σ, Finset.sum_nonneg (fun σ _ => hA σ), ?_⟩
  intro σ k hk
  have H := hbound σ k (abs_le.mp hk)
  have hsum : A σ ≤ ∑ τ, A τ :=
    Finset.single_le_sum (fun τ _ => hA τ) (Finset.mem_univ σ)
  refine ⟨?_, ?_, ?_⟩ <;>
    linarith [norm_nonneg (kDirectionShape σ k), norm_nonneg (deriv (kDirectionShape σ) k),
      norm_nonneg (deriv (deriv (kDirectionShape σ)) k)]

theorem window_direction_budget :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ β h : ℝ, 0 ≤ h → ∀ N : ℕ, ∀ σ : Fin 12,
      ∀ k : ℝ, |k| ≤ 1 / 2 →
      let v : ℝ → E := fun t => (β * Real.sqrt (h / (N : ℝ))) • kDirectionShape σ t
      ContDiffAt ℝ 2 v k ∧
        ‖v k‖ ≤ A * |β| * Real.sqrt (h / (N : ℝ)) ∧
        ‖deriv v k‖ ≤ A * |β| * Real.sqrt (h / (N : ℝ)) ∧
        ‖deriv (deriv v) k‖ ≤ A * |β| * Real.sqrt (h / (N : ℝ)) := by
  obtain ⟨A, hA, hbound⟩ := exists_kDirectionShape_bound
  refine ⟨A, hA, ?_⟩
  intro β h _ N σ k hk
  dsimp only
  have hmem : k ∈ Ioo (-(3 / 5) : ℝ) (3 / 5) := by
    obtain ⟨hk₁, hk₂⟩ := abs_le.mp hk
    constructor <;> linarith
  have hf := (kDirectionShape_contDiffOn σ).contDiffAt (isOpen_Ioo.mem_nhds hmem)
  have hderiv : deriv (fun t => (β * Real.sqrt (h / (N : ℝ))) • kDirectionShape σ t) =
      fun t => (β * Real.sqrt (h / (N : ℝ))) • deriv (kDirectionShape σ) t := by
    funext t
    exact deriv_fun_const_smul_field _ _
  have hsecond : deriv (deriv (fun t =>
      (β * Real.sqrt (h / (N : ℝ))) • kDirectionShape σ t)) k =
      (β * Real.sqrt (h / (N : ℝ))) • deriv (deriv (kDirectionShape σ)) k := by
    rw [hderiv]
    exact deriv_fun_const_smul_field _ _
  have hnorm {v : E} (hv : ‖v‖ ≤ A) :
      ‖(β * Real.sqrt (h / (N : ℝ))) • v‖ ≤ A * |β| * Real.sqrt (h / (N : ℝ)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [mul_le_mul_of_nonneg_left hv
      (show 0 ≤ |β| * Real.sqrt (h / (N : ℝ)) by positivity)]
  refine ⟨hf.const_smul _, hnorm (hbound σ k hk).1, ?_, ?_⟩
  · rw [hderiv]
    exact hnorm (hbound σ k hk).2.1
  · rw [hsecond]
    exact hnorm (hbound σ k hk).2.2

def kStageShapes : Fin 6 → List (Fin 12) :=
  ![[0], [1], [2], [3, 4, 5], [6, 7, 8], [9, 10, 11]]

def windowKCurves (β : ℝ) (α : ℝ → ℝ) (s h : ℝ) (N : ℕ) : List (ℝ → ℝ × E) :=
  (List.finRange 6).flatMap fun σ =>
    (List.range N).flatMap fun (j : ℕ) =>
      (kStageShapes σ).map fun i k =>
        (kStageMass α s h ((j : ℝ) / (N : ℝ)) σ k,
          (β * Real.sqrt (h / (N : ℝ))) • kDirectionShape i k)

private theorem sqrt_grid_factor {h : ℝ} (hh : 0 ≤ h) (len : ℝ) (N : ℕ) :
    Real.sqrt (h * len / (N : ℝ)) = Real.sqrt (h / (N : ℝ)) * Real.sqrt len := by
  rw [show h * len / (N : ℝ) = (h / (N : ℝ)) * len from by ring,
    Real.sqrt_mul (div_nonneg hh (Nat.cast_nonneg N))]

theorem windowKCurves_apply (β : ℝ) (α : ℝ → ℝ) (s h k : ℝ) (N : ℕ)
    (hh : 0 ≤ h) :
    (windowKCurves β α s h N).map (fun p => p k) =
      (OW.window α (1 / 2) s h k N).map (fun p => (p.1, β • p.2)) := by
  have hFin : List.finRange 6 = ([0, 1, 2, 3, 4, 5] : List (Fin 6)) := by decide
  have hL : OW.repairLength (1 / 2) k = (44 / 9) * k ^ 2 := by
    norm_num [OW.repairLength, SKOptimized.Overshoot.varianceCoefficient,
      SKOptimized.Overshoot.tentWeight, SKOptimized.Overshoot.rampWeight]
    ring
  simp only [windowKCurves, hFin, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.map_append, List.map_flatMap, List.map_map, Function.comp_def,
    OW.window_eq, OW.windowGrid, OW.windowRepairGrid, List.append_assoc]
  norm_num [kStageShapes, kStageMass, quadraticGridMass, kStageTimeConstant,
    kStageTimeQuadratic, kStageMassDivisor, kDirectionShape, hL,
    SKOptimized.Overshoot.varianceCoefficient, SKOptimized.Overshoot.tentWeight,
    SKOptimized.Overshoot.rampWeight, sqrt_grid_factor hh, smul_smul]
  have hshared (x : ℝ) : x / (N : ℝ) / 2 = (1 / 2) * x / (N : ℝ) := by ring
  have hrepair (x : ℝ) : (44 / 9) * (x / (N : ℝ)) * k ^ 2 =
      (44 / 9) * k ^ 2 * x / (N : ℝ) := by ring
  have htail (x : ℝ) : 2 + 2 * (x / (N : ℝ)) + (44 / 9) * (1 - x / (N : ℝ)) * k ^ 2 =
      2 + (44 / 9) * k ^ 2 + (2 - (44 / 9) * k ^ 2) * x / (N : ℝ) := by ring
  simp only [hshared, hrepair, htail]
  simp only [mul_assoc, mul_left_comm (Real.sqrt h / Real.sqrt (N : ℝ)) k]

theorem windowKCurves_length (β : ℝ) (α : ℝ → ℝ) (s h : ℝ) (N : ℕ) :
    (windowKCurves β α s h N).length = 12 * N := by
  have hFin : List.finRange 6 = ([0, 1, 2, 3, 4, 5] : List (Fin 6)) := by decide
  simp only [windowKCurves, List.length_flatMap, List.length_map,
    List.map_const', List.length_range, List.sum_replicate, nsmul_eq_mul]
  norm_num [hFin, kStageShapes]
  omega

theorem scalarData_window_parameter_budget {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hu : u < D.q) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ N : ℕ, 1 ≤ N →
      ∀ p ∈ windowKCurves β (cdf (D.μ : Measure ℝ)) (r - h) h N,
      ∀ k : ℝ, |k| ≤ 1 / 2 →
        ContDiffAt ℝ 2 p k ∧
        |deriv (fun t => (p t).1) k| ≤ C * h ∧
        |deriv (deriv (fun t => (p t).1)) k| ≤ C * h ∧
        ‖(p k).2‖ ≤ C * |β| * Real.sqrt (h / (N : ℝ)) ∧
        ‖deriv (fun t => (p t).2) k‖ ≤ C * |β| * Real.sqrt (h / (N : ℝ)) ∧
        ‖deriv (deriv (fun t => (p t).2)) k‖ ≤ C * |β| * Real.sqrt (h / (N : ℝ)) := by
  obtain ⟨M, h₀, hM, hh₀, hmass⟩ := scalarData_window_mass_budget D hl hlu hu
  obtain ⟨A, hA, hdir⟩ := window_direction_budget
  refine ⟨M + A + 1, h₀, by positivity, hh₀, ?_⟩
  intro r hr h hh hh0 N hN p hp k hk
  obtain ⟨σ, _, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨j, hj, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
  have hmass' := hmass r hr h hh hh0 N hN j (List.mem_range.mp hj) σ k hk
  have hdir' := hdir β h hh.le N i k hk
  refine ⟨hmass'.1.prodMk hdir'.1, ?_, ?_, ?_, ?_, ?_⟩
  · exact hmass'.2.1.trans (by nlinarith)
  · exact hmass'.2.2.trans (by nlinarith)
  · apply hdir'.2.1.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : A ≤ M + A + 1) (abs_nonneg β))
      (Real.sqrt_nonneg _)
  · apply hdir'.2.2.1.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : A ≤ M + A + 1) (abs_nonneg β))
      (Real.sqrt_nonneg _)
  · apply hdir'.2.2.2.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : A ≤ M + A + 1) (abs_nonneg β))
      (Real.sqrt_nonneg _)

private theorem windowKCurves_sum_square_le {β h C : ℝ} {α : ℝ → ℝ} {s : ℝ}
    {N : ℕ} (hh : 0 ≤ h) (hC : 0 ≤ C) (hN : 1 ≤ N)
    (test : (ℝ → ℝ × E) → E)
    (hbound : ∀ p ∈ windowKCurves β α s h N,
      ‖test p‖ ≤ C * |β| * Real.sqrt (h / (N : ℝ))) :
    ((windowKCurves β α s h N).map fun p => ‖test p‖ ^ 2).sum ≤
      12 * C ^ 2 * β ^ 2 * h := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have H := List.sum_le_length_nsmul
    ((windowKCurves β α s h N).map fun p => ‖test p‖ ^ 2)
    ((C * |β| * Real.sqrt (h / (N : ℝ))) ^ 2) (by
      intro a ha
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hbound p hp))
  simp only [List.length_map, windowKCurves_length, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_ofNat] at H
  apply H.trans_eq
  rw [mul_pow, mul_pow, sq_abs, Real.sq_sqrt (div_nonneg hh hNr.le)]
  field_simp

theorem scalarData_window_parameter_energies {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hu : u < D.q) :
    ∃ C h₀ : ℝ, 0 ≤ C ∧ 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ N : ℕ, 1 ≤ N →
      ∀ k : ℝ, |k| ≤ 1 / 2 →
      let ps := windowKCurves β (cdf (D.μ : Measure ℝ)) (r - h) h N
      (ps.map fun p => ‖(p k).2‖ ^ 2).sum ≤ C * h ∧
      (ps.map fun p => ‖deriv (fun t => (p t).2) k‖ ^ 2).sum ≤ C * h ∧
      (ps.map fun p => ‖deriv (deriv (fun t => (p t).2)) k‖ ^ 2).sum ≤ C * h := by
  obtain ⟨A, h₀, hA, hh₀, hbound⟩ := scalarData_window_parameter_budget D hl hlu hu
  refine ⟨12 * A ^ 2 * β ^ 2, h₀, by positivity, hh₀, ?_⟩
  intro r hr h hh hh0 N hN k hk
  refine ⟨?_, ?_, ?_⟩
  · exact windowKCurves_sum_square_le hh.le hA.le hN (fun p => (p k).2)
      (fun p hp => (hbound r hr h hh hh0 N hN p hp k hk).2.2.2.1)
  · exact windowKCurves_sum_square_le hh.le hA.le hN (fun p => deriv (fun t => (p t).2) k)
      (fun p hp => (hbound r hr h hh hh0 N hN p hp k hk).2.2.2.2.1)
  · exact windowKCurves_sum_square_le hh.le hA.le hN
      (fun p => deriv (deriv (fun t => (p t).2)) k)
      (fun p hp => (hbound r hr h hh hh0 N hN p hp k hk).2.2.2.2.2)

theorem scalarData_window_mass_floor {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ a₀ h₀ : ℝ, 0 < a₀ ∧ 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ N : ℕ, 1 ≤ N →
      ∀ p ∈ windowKCurves β (cdf (D.μ : Measure ℝ)) (r - h) h N,
      ∀ k : ℝ, |k| ≤ 1 / 2 → (p k).1 ∈ Icc a₀ 1 := by
  obtain ⟨c, T, hc, hT, hlinear⟩ := D.lin_lower
  let t : ℝ := min (l / 2) T
  have htpos : 0 < t := lt_min (by positivity) hT
  refine ⟨c * t / 3, kStabilityInteriorRadius D.q l u, by positivity,
    kStabilityInteriorRadius_pos hl hu, ?_⟩
  intro r hr h hh hh0 N hN p hp k hk
  obtain ⟨σ, _, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨j, hj, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hx : (j : ℝ) / (N : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg j) hNr.le
    · exact (div_le_one hNr).mpr (by exact_mod_cast (List.mem_range.mp hj).le)
  let τ : ℝ := r - h + h * (kStageTimeConstant ((j : ℝ) / (N : ℝ)) σ +
    kStageTimeQuadratic ((j : ℝ) / (N : ℝ)) σ * k ^ 2)
  have hτ : τ ∈ Icc (l / 2) ((u + D.q) / 2) :=
    kStability_time_mem hr hh.le hh0 (kStageTime_mem hx hk σ)
  have hlow : c * t ≤ cdf (D.μ : Measure ℝ) τ :=
    (hlinear t ⟨htpos.le, min_le_right _ _⟩).trans
      ((cdf (D.μ : Measure ℝ)).mono ((min_le_left _ _).trans hτ.1))
  have hd₁ : 1 ≤ kStageMassDivisor σ := (kStageMass_coefficients hx σ).2
  have hd₃ : kStageMassDivisor σ ≤ 3 := by
    fin_cases σ <;> norm_num [kStageMassDivisor]
  have hdpos : 0 < kStageMassDivisor σ := by linarith
  change c * t / 3 ≤ cdf (D.μ : Measure ℝ) τ / kStageMassDivisor σ ∧
    cdf (D.μ : Measure ℝ) τ / kStageMassDivisor σ ≤ 1
  constructor
  · apply (le_div_iff₀ hdpos).mpr
    calc
      c * t / 3 * kStageMassDivisor σ ≤ c * t / 3 * 3 :=
        mul_le_mul_of_nonneg_left hd₃ (by positivity)
      _ = c * t := by ring
      _ ≤ cdf (D.μ : Measure ℝ) τ := hlow
  · exact (div_le_self (cdf_nonneg _ _) hd₁).trans (cdf_le_one _ _)

theorem scalarData_window_step_contDiffAt {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ N : ℕ, 1 ≤ N →
      ∀ p ∈ windowKCurves β (cdf (D.μ : Measure ℝ)) (r - h) h N,
      ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ B : ℝ, ∀ f : E → ℝ, QPotential 2 B f →
      ∀ x : E, ContDiffAt ℝ 2 (fun t => vectorStep (p t).1 (p t).2 f x) k := by
  obtain ⟨C, h₁, _, hh₁, hparam⟩ := scalarData_window_parameter_budget D hl hlu hu
  obtain ⟨a₀, h₂, ha₀, hh₂, hmass⟩ := scalarData_window_mass_floor D hl hu
  refine ⟨min h₁ h₂, lt_min hh₁ hh₂, ?_⟩
  intro r hr h hh hh0 N hN p hp k hk B f hf x
  have hpreg := (hparam r hr h hh (hh0.trans (min_le_left _ _)) N hN p hp k hk).1
  have hpositive := ha₀.trans_le (hmass r hr h hh
    (hh0.trans (min_le_right _ _)) N hN p hp k hk).1
  exact StepCalculus.contDiffAt_paramStep hf le_rfl hpreg.fst hpreg.snd hpositive.ne' x

theorem scalarData_boundary_differentiable {β : ℝ} (D : ScalarData β)
    {r h : ℝ} (ht : r - h + 4 * h ∈ Icc (0 : ℝ) 1) (k : ℝ) (N : ℕ) (z : ℝ) :
    DifferentiableAt ℝ
      (OW.boundary β (cdf (D.μ : Measure ℝ)) (1 / 2) (r - h) h k N) z := by
  have hterminal := scalarData_terminal_regular D ht
  have hchain := vectorIncrementChain_regular
    ((OW.window (cdf (D.μ : Measure ℝ)) (1 / 2) (r - h) h k N).map
      (fun p => (p.1, β • p.2))) hterminal
  have hdiag : DifferentiableAt ℝ (fun y : ℝ => (fun _ : Fin 3 => y)) z := by
    exact differentiableAt_pi.mpr (fun _ => differentiableAt_id)
  exact (hchain.1.differentiable (by norm_num) (fun _ : Fin 3 => z)).comp z hdiag

theorem scalarData_boundary_spatial_uniform {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ N : ℕ, ∀ k z : ℝ, DifferentiableAt ℝ
        (OW.boundary β (cdf (D.μ : Measure ℝ)) (1 / 2) (r - h) h k N) z := by
  refine ⟨kStabilityInteriorRadius D.q l u, kStabilityInteriorRadius_pos hl hu, ?_⟩
  intro r hr h hh hh0 N k z
  have ht := kStability_time_mem hr hh.le hh0 (show (4 : ℝ) ∈ Icc (0 : ℝ) 4 by norm_num)
  apply scalarData_boundary_differentiable D ?_ k N z
  constructor <;> linarith [ht.1, ht.2, D.q_mem.2]

end SKBarriers2.Corner
