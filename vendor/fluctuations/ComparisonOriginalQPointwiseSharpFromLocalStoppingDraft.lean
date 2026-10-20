module

public import ComparisonActualHighWallThetaZeroConcreteSharpCost
public import ComparisonActualHighWallThetaZeroDensityBasics
public import ComparisonActualHighWallThetaZeroSelectedScale
public import ComparisonConcretePositiveWallMeanWrapperDraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy PositiveLaplaceAssembly
open scoped Topology NNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
namespace OriginalQLocalSharpReductionDraft

abbrev SweepAttains {n : ℕ} {delta : ℝ} (a : ActualHighWallData n delta)
    (lam : ℝ) (alpha : a.Profile) : Prop :=
  omittedComparisonSweepObjective a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc
    a.hm a.hM n a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h a.d lam alpha =
  omittedComparisonSweepMinimum a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc
    a.hm a.hM n a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h a.d lam

abbrev GlobalSweepMinimum {n : ℕ} {delta : ℝ} (a : ActualHighWallData n delta)
    (lam : ℝ) (hlam : lam ∈ Ioo ((n : ℝ)^(-(10 : ℝ))) (a.d^2))
    (alpha : a.Profile) : Prop :=
  ∀ beta : a.Profile,
    (a.thetaZeroShiftedParentData lam
      ((Real.rpow_pos_of_pos a.hN _).trans hlam.1) hlam.2.le).objective alpha ≤
    (a.thetaZeroShiftedParentData lam
      ((Real.rpow_pos_of_pos a.hN _).trans hlam.1) hlam.2.le).objective beta

abbrev BaseRegular {n : ℕ} {delta : ℝ} (a : ActualHighWallData n delta)
    (cl cu lam : ℝ) (alpha : a.Profile) : Prop :=
  ∀ r ∈ Icc (min (2*comparisonConditionalScale a.N delta a.E lam) 1) 1,
    cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r

def StopsSelectedBadAtStrength {n : ℕ} {delta : ℝ}
    (a : ActualHighWallData n delta) (m cl cu lam : ℝ) : Prop :=
  ∀ Q : ActualThetaZeroOverlapMinimum n m delta cl cu 2 1 1 1 a.T,
    Q.data = a → Q.lam = lam →
    Q.xs ∈ Icc (comparisonConditionalScale a.N delta a.E lam) 1 →
    (Q.alpha.val.val Q.xs < cl*Q.xs ∨ cu*Q.xs < Q.alpha.val.val Q.xs) → False

structure LocalStoppingGates {n : ℕ} {delta : ℝ}
    (a : ActualHighWallData n delta) (m cl cu : ℝ) : Prop where
  stopping : ∀ lam ∈ Ioo ((n : ℝ)^(-(10 : ℝ))) (a.d^2),
    (n : ℝ)^(10*delta)*a.E < 2*lam →
    comparisonConditionalScale a.N delta a.E lam < 1 →
    StopsSelectedBadAtStrength a m cl cu lam
  regular : ∀ (lam : ℝ)
    (hlam : lam ∈ Ioo ((n : ℝ)^(-(10 : ℝ))) (a.d^2)),
    (n : ℝ)^(10*delta)*a.E < 2*lam →
    comparisonConditionalScale a.N delta a.E lam < 1 →
    ∀ alpha : a.Profile, GlobalSweepMinimum a lam hlam alpha →
    BaseRegular a cl cu lam alpha →
    a.thetaZeroOriginalSweepDensity lam alpha ≤ (n : ℝ)^(10*delta)*a.E
  macroGate : ∀ (lam : ℝ)
    (hlam : lam ∈ Ioo ((n : ℝ)^(-(10 : ℝ))) (a.d^2)),
    (n : ℝ)^(10*delta)*a.E < 2*lam →
    1 ≤ comparisonConditionalScale a.N delta a.E lam →
    ∀ alpha : a.Profile, GlobalSweepMinimum a lam hlam alpha →
    a.thetaZeroOriginalSweepDensity lam alpha ≤ (n : ℝ)^(10*delta)*a.E

abbrev AllOriginalAttainerDensity {n : ℕ} {delta : ℝ}
    (a : ActualHighWallData n delta) : Prop :=
  ∀ lam ∈ Ioo ((n : ℝ)^(-(10 : ℝ))) (a.d^2), ∀ alpha : a.Profile,
    SweepAttains a lam alpha →
    a.thetaZeroOriginalSweepDensity lam alpha ≤ (n : ℝ)^(10*delta)*a.E

theorem concrete_original_q_origin_le_lower_scale
    {m : ℝ} (hm : 0 < m) {n : ℕ} (hn : 1 ≤ n)
    (a : ActualHighWallData n (m/10000))
    (hE : a.E = wallHighError m n)
    (hd : a.d = wallHighD m n)
    (hs : a.s = wallHighMass m n) :
    a.rmin ≤ a.s ∧
      a.s ≤ comparisonLowerScale a.N a.E a.d := by
  have hn0 : 0 < n := by omega
  have hN1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hU : 0 < comparisonSmallMass a.N a.E := a.hU
  have hcap : 2 ≤ a.M a.s :=
    a.hq.trans (concreteWallCap_ge a.hN a.hE a.hd a.hs.1.le)
  have hrU : a.rmin ≤ comparisonSmallMass a.N a.E := by
    have hden : 0 < 2*a.M a.s := by linarith
    change comparisonSmallMass a.N a.E/(2*a.M a.s) ≤ _
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hU.le (show 0 ≤ 2*a.M a.s-1 by linarith)]
  have hUs : comparisonSmallMass a.N a.E ≤ a.s := by
    rw [hE, hs]
    have hUlit : 0 < comparisonSmallMass (n : ℝ) (wallHighError m n) :=
      concreteWallSmallMass_pos (Nat.cast_pos.mpr hn0) (wallHighError_pos m hn0)
    have hpow : 1 ≤ (n : ℝ)^(30*m) :=
      Real.one_le_rpow hN1 (by linarith)
    have hratio : 1 ≤ wallHighMass m n /
        comparisonSmallMass (n : ℝ) (wallHighError m n) := by
      rw [wallHighMass_div_smallMass m hn0]
      exact hpow
    exact (by simpa only [one_mul] using
      (le_div_iff₀ hUlit).mp hratio)
  have hsScale : a.s ≤ comparisonLowerScale a.N a.E a.d := by
    rw [hE, hd, hs]
    rw [wallHighLowerScale_eq m hn0]
    unfold wallHighMass
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  exact ⟨hrU.trans hUs,hsScale⟩

theorem concrete_original_q_selected_origin_gates
    {m : ℝ} (hm : 0 < m) {n : ℕ} (hn : 1 ≤ n)
    (a : ActualHighWallData n (m/10000))
    (hE : a.E = wallHighError m n)
    (hd : a.d = wallHighD m n)
    (hs : a.s = wallHighMass m n)
    {lam : ℝ} (hlam : 0 < lam) (hld : lam ≤ a.d^2) :
    a.s ≤ comparisonConditionalScale a.N (m/10000) a.E lam ∧
      a.rmin ≤ comparisonConditionalScale a.N (m/10000) a.E lam := by
  have horigin := concrete_original_q_origin_le_lower_scale
    hm hn a hE hd hs
  have hN1 : 1 ≤ a.N := by
    dsimp only [ActualHighWallData.N]
    exact_mod_cast hn
  have hscale := comparison_conditional_scale_ge_lower hN1
    (show (0:ℝ) ≤ m/10000 by positivity) a.hE a.hd hlam hld
  exact ⟨horigin.2.trans hscale,horigin.1.trans (horigin.2.trans hscale)⟩

theorem original_attainer_is_global_sweep_minimum
    {n : ℕ} {delta : ℝ} (a : ActualHighWallData n delta)
    (lam : ℝ) (hlam : lam ∈ Ioo ((n : ℝ)^(-(10 : ℝ))) (a.d^2))
    (alpha : a.Profile) (hattained : SweepAttains a lam alpha) :
    GlobalSweepMinimum a lam hlam alpha := by
  let hpos := (Real.rpow_pos_of_pos a.hN (-(10 : ℝ))).trans hlam.1
  obtain ⟨P⟩ := a.theta_zero_shifted_minimum_attained lam hpos hlam.2.le
  have hsame : (a.thetaZeroShiftedParentData lam hpos hlam.2.le).objective alpha =
      (a.thetaZeroShiftedParentData lam hpos hlam.2.le).objective P.alpha := by
    rw [a.theta_zero_objective_eq_omitted, hattained,
      ← a.theta_zero_wall_value_eq_omitted lam hpos hlam.2.le,
      a.theta_zero_wall_value_attained lam hpos hlam.2.le P]
  intro beta
  rw [hsame]
  exact P.minimum beta

theorem original_base_regular_of_density_free_stopping
    {n : ℕ} {m delta cl cu : ℝ} (a : ActualHighWallData n delta)
    (lam : ℝ) (hlam : lam ∈ Ioo ((n : ℝ)^(-(10 : ℝ))) (a.d^2))
    (alpha : a.Profile) (hminimum : GlobalSweepMinimum a lam hlam alpha)
    (hdelta : 0 ≤ delta) (hcl : cl ≤ 1) (hcu : 1 ≤ cu)
    (hsA : a.s ≤ comparisonConditionalScale a.N delta a.E lam)
    (hrA : a.rmin ≤ comparisonConditionalScale a.N delta a.E lam)
    (hupper : Real.sqrt a.N*a.E ≤ a.d^2)
    (hlower : a.N^(-(2 : ℝ)/3+m)*a.d ≤ a.E)
    (hstop : StopsSelectedBadAtStrength a m cl cu lam) :
    BaseRegular a cl cu lam alpha := by
  have hall : ∀ r ∈ Icc (min (comparisonConditionalScale a.N delta a.E lam) 1) 1,
      cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r := by
    intro r hr
    by_contra hbad
    have hbadRadius : ∃ r ∈ Icc (min (comparisonConditionalScale a.N delta a.E lam) 1) 1,
        alpha.val.val r < cl*r ∨ cu*r < alpha.val.val r := by
      refine ⟨r,hr,?_⟩
      rcases not_and_or.mp hbad with hlow | hhigh
      · exact Or.inl (lt_of_not_ge hlow)
      · exact Or.inr (lt_of_not_ge hhigh)
    obtain ⟨Q,hdata,hQlam,hAlpha,hxs,hz,hbadQ⟩ :=
      a.exists_theta_zero_selected_bad_scale_minimum
        (m := m) (C0 := 1) (D := 1) (Bclock := a.T) lam
        ((Real.rpow_pos_of_pos a.hN _).trans hlam.1) hlam.2.le alpha hminimum
        hdelta hcl hcu hsA hrA a.hd1 hupper
        (by simpa only [one_mul] using hlower) le_rfl
        (by norm_num : (2 : ℝ) ≤ 2) (by norm_num : (1 : ℝ) ≤ 1) hbadRadius
    exact hstop Q hdata hQlam hxs hbadQ
  have hA : 0 < comparisonConditionalScale a.N delta a.E lam :=
    comparison_conditional_scale_pos a.hN a.hE ((Real.rpow_pos_of_pos a.hN _).trans hlam.1)
  intro r hr
  exact hall r ⟨(min_le_min (by linarith :
    comparisonConditionalScale a.N delta a.E lam ≤
      2*comparisonConditionalScale a.N delta a.E lam) le_rfl).trans hr.1,hr.2⟩

theorem all_original_density_of_local_stopping_gates
    {n : ℕ} {m delta cl cu : ℝ} (a : ActualHighWallData n delta)
    (hdelta : 0 ≤ delta) (hcl : cl ≤ 1) (hcu : 1 ≤ cu)
    (hsA : ∀ lam ∈ Ioo ((n : ℝ)^(-(10 : ℝ))) (a.d^2),
      a.s ≤ comparisonConditionalScale a.N delta a.E lam)
    (hrA : ∀ lam ∈ Ioo ((n : ℝ)^(-(10 : ℝ))) (a.d^2),
      a.rmin ≤ comparisonConditionalScale a.N delta a.E lam)
    (hupper : Real.sqrt a.N*a.E ≤ a.d^2)
    (hlower : a.N^(-(2 : ℝ)/3+m)*a.d ≤ a.E)
    (H : LocalStoppingGates a m cl cu) :
    AllOriginalAttainerDensity a := by
  intro lam hlam alpha hattained
  have hpos : 0 < lam := (Real.rpow_pos_of_pos a.hN _).trans hlam.1
  by_cases heasy : 2*lam ≤ (n : ℝ)^(10*delta)*a.E
  · exact (a.theta_zero_density_le_two_strength alpha hpos hlam.2.le).trans heasy
  have hunresolved := lt_of_not_ge heasy
  have hmin := original_attainer_is_global_sweep_minimum a lam hlam alpha hattained
  by_cases hA : comparisonConditionalScale a.N delta a.E lam < 1
  · have hregular := original_base_regular_of_density_free_stopping a lam hlam alpha hmin
      hdelta hcl hcu (hsA lam hlam) (hrA lam hlam) hupper hlower
      (H.stopping lam hlam hunresolved hA)
    exact H.regular lam hlam hunresolved hA alpha hmin hregular
  · exact H.macroGate lam hlam hunresolved (le_of_not_gt hA) alpha hmin

theorem original_bare_pressure_eq_physical_shell
    {n : ℕ} {delta : ℝ} (a : ActualHighWallData n delta) :
    realOrderedSKPathPressure n a.thetaZeroHighOnlyData.b
      a.thetaZeroHighOnlyData.h 0 = physicalShellPressure n a.T a.s a.epsilon := by
  have hb : a.thetaZeroHighOnlyData.b = initialShellMatrixClock a.T a.epsilon a.s := by
    funext u
    by_cases hu : u < a.s <;>
      simp [ActualHighWallData.thetaZeroHighOnlyData,wallBareMatrix,
        initialShellMatrixClock,hu]
  rw [hb]
  rfl

theorem eventually_concrete_sharp_of_all_original_density
    {T m : ℝ} (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop, ∀ hp : ActualConcreteHighWallNumeric m n,
      ∀ (epsilon : ℝ) (hepsilon : epsilon ∈ Ioo (0 : ℝ) T)
        (heps0 : upperInitialEpsilon m n ≤ epsilon),
      AllOriginalAttainerDensity
        (actualConcreteHighWallData T m n hp epsilon 0 hepsilon heps0 (by norm_num)) →
      concreteSharpCostAtNumeric T m n hp epsilon hepsilon heps0 := by
  filter_upwards [ActualHighWallData.eventually_concrete_theta_zero_original_wall_sharp_of_density
    hm] with n hn
  intro hp epsilon hepsilon heps0 H
  let a := actualConcreteHighWallData T m n hp epsilon 0 hepsilon heps0 (by norm_num)
  have hcost := hn a rfl H
  rw [original_bare_pressure_eq_physical_shell] at hcost
  change wallMinimumValue a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM
    a.g a.hg.continuous a.T a.epsilon a.tau a.d n 0 0 ≤
    physicalShellPressure n a.T a.s a.epsilon + highWallComparisonError m n
  simpa only [highWallComparisonError,
    show a.E = wallHighError m n from rfl] using hcost

end OriginalQLocalSharpReductionDraft
end OAI.SKFluctuations.LaplaceWindowFormalization
