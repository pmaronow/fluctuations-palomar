module

public import ComparisonActualHighWallThetaZeroSelectedScale
public import ComparisonActualHighWallThetaZeroStrongScaleGeometry
public import ComparisonActualHighWallThetaZeroRegularScaleCarrier
public import ComparisonActualConcreteHighWallAmplitude

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Filter Set PositiveLaplaceAssembly
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 12000000

namespace OriginalQFixedTStoppingDraft

def RetainedBadQ (T : ℝ) {m cl cu Az C0 Ct D Bclock : ℝ} (k : ℕ)
    (Q : ActualThetaZeroOverlapMinimum (k+1)
      m (m/10000) cl cu Az C0 Ct D Bclock) : Prop :=
  Q.data.T = T ∧
  Q.data.E = wallHighError m (k+1) ∧
  Q.data.d = wallHighD m (k+1) ∧
  Q.data.s = wallHighMass m (k+1) ∧
  Q.data.theta = 0 ∧
  Q.data.tau = (((k+1 : ℕ) : ℝ)^(-(10 : ℝ))) ∧
  upperInitialEpsilon m (k+1) ≤ Q.data.epsilon ∧
  Q.lam ∈ Ioo (((k+1 : ℕ) : ℝ)^(-(10 : ℝ))) (Q.data.d^2) ∧
  comparisonConditionalScale Q.data.N (m/10000) Q.data.E Q.lam ≤ Q.xs ∧
  Q.xs ≤ 1 ∧
  (Q.alpha.val.val Q.xs < cl*Q.xs ∨
    cu*Q.xs < Q.alpha.val.val Q.xs)

structure PhysicalExclusions
    (T m cl cu Az C0 Ct D Bclock : ℝ) : Prop where
  hT : 1 < T
  hm : 0 < m
  hmmax : m < 1/300
  hcl : 0 < cl
  hcl1 : cl ≤ 1
  hcu1 : 1 ≤ cu
  macroGate : ∀ (dim : ℕ → ℕ) (_hdim : StrictMono dim)
      (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
        m (m/10000) cl cu Az C0 Ct D Bclock),
      (∀ n, RetainedBadQ T (dim n) (Q n)) →
      ∀ η : ℝ, 0 < η → ∀ phi : ℕ → ℕ, StrictMono phi →
        (∀ n, η ≤ (Q (phi n)).xs) → False
  strong : ∀ (dim : ℕ → ℕ) (_hdim : StrictMono dim)
      (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
        m (m/10000) cl cu Az C0 Ct D Bclock),
      (∀ n, RetainedBadQ T (dim n) (Q n)) →
      Tendsto (fun n => (Q n).xs) atTop (𝓝 0) →
      ∀ η : ℝ, 0 < η → ∀ phi : ℕ → ℕ, StrictMono phi →
        (∀ n, η ≤ laplaceComparisonStrength (Q (phi n)).data.d
          (Q (phi n)).lam (Q (phi n)).xs / (Q (phi n)).xs^2) → False
  weak : ∀ (dim : ℕ → ℕ) (_hdim : StrictMono dim)
      (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
        m (m/10000) cl cu Az C0 Ct D Bclock),
      (∀ n, RetainedBadQ T (dim n) (Q n)) →
      Tendsto (fun n => (Q n).xs) atTop (𝓝 0) →
      Tendsto (fun n => laplaceComparisonStrength (Q n).data.d
        (Q n).lam (Q n).xs / (Q n).xs^2) atTop (𝓝 0) → False

private theorem tendsto_zero_of_no_positive_cofinal_subsequence
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (hno : ∀ η : ℝ, 0 < η → ∀ phi : ℕ → ℕ, StrictMono phi →
      (∀ n, η ≤ f (phi n)) → False) :
    Tendsto f atTop (𝓝 0) := by
  classical
  by_contra hzero
  have hfreq : ∃ η : ℝ, 0 < η ∧ ∃ᶠ n : ℕ in atTop, η ≤ f n := by
    by_contra hnone
    apply hzero
    apply Metric.tendsto_nhds.mpr
    intro eps heps
    have hnot : ¬ (∃ᶠ n : ℕ in atTop, eps ≤ f n) :=
      fun h => hnone ⟨eps, heps, h⟩
    have hsmall : ∀ᶠ n : ℕ in atTop, f n < eps := by
      simpa only [Filter.Frequently, not_not, not_le] using hnot
    filter_upwards [hsmall] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (hf n)] using hn
  obtain ⟨η, hη, hηfreq⟩ := hfreq
  obtain ⟨phi, hphi, hbound⟩ := extraction_of_frequently_atTop hηfreq
  exact hno η hη phi hphi hbound

theorem eventually_no_fixed_T_retained_bad_q
    {T m cl cu Az C0 Ct D Bclock : ℝ}
    (H : PhysicalExclusions T m cl cu Az C0 Ct D Bclock) :
    ∀ᶠ k : ℕ in atTop,
      ∀ Q : ActualThetaZeroOverlapMinimum (k+1)
        m (m/10000) cl cu Az C0 Ct D Bclock,
        ¬ RetainedBadQ T k Q := by
  classical
  have hnone : ¬ (∃ᶠ k : ℕ in atTop,
      ∃ Q : ActualThetaZeroOverlapMinimum (k+1)
        m (m/10000) cl cu Az C0 Ct D Bclock,
        RetainedBadQ T k Q) := by
    intro hbad
    obtain ⟨dim, hdim, hdimBad⟩ := extraction_of_frequently_atTop hbad
    choose Q hQ using hdimBad
    have hxs : Tendsto (fun n => (Q n).xs) atTop (𝓝 0) := by
      apply tendsto_zero_of_no_positive_cofinal_subsequence
        (fun n => (Q n).xs) (fun n => (Q n).hxs.le)
      exact H.macroGate dim hdim Q hQ
    have hratio : Tendsto (fun n => laplaceComparisonStrength (Q n).data.d
        (Q n).lam (Q n).xs / (Q n).xs^2) atTop (𝓝 0) := by
      apply tendsto_zero_of_no_positive_cofinal_subsequence
      · intro n
        exact div_nonneg
          (laplaceComparisonStrength_pos (Q n).data.d
            (Q n).hlam (Q n).xs).le (sq_nonneg _)
      · exact H.strong dim hdim Q hQ hxs
    exact H.weak dim hdim Q hQ hxs hratio
  have hevent : ∀ᶠ k : ℕ in atTop,
      ¬ ∃ Q : ActualThetaZeroOverlapMinimum (k+1)
        m (m/10000) cl cu Az C0 Ct D Bclock,
        RetainedBadQ T k Q := by
    simpa only [Filter.Frequently, not_not] using hnone
  filter_upwards [hevent] with k hk Q hQ
  exact hk ⟨Q, hQ⟩

theorem original_sweep_attainer_is_global_minimum
    {n : ℕ} {delta : ℝ} (a : ActualHighWallData n delta)
    (lam : ℝ) (hlam : 0 < lam) (hld : lam ≤ a.d^2) (alpha : a.Profile)
    (hattained : omittedComparisonSweepObjective a.hr ⟨a.hs.1.le, a.hs1⟩
      a.hc a.hk a.hkc a.hm a.hM n a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h
      a.d lam alpha = omittedComparisonSweepMinimum a.hr ⟨a.hs.1.le, a.hs1⟩
      a.hc a.hk a.hkc a.hm a.hM n a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h
      a.d lam) :
    ∀ beta : a.Profile,
      (a.thetaZeroShiftedParentData lam hlam hld).objective alpha ≤
        (a.thetaZeroShiftedParentData lam hlam hld).objective beta := by
  obtain ⟨P⟩ := a.theta_zero_shifted_minimum_attained lam hlam hld
  have hsame : (a.thetaZeroShiftedParentData lam hlam hld).objective alpha =
      (a.thetaZeroShiftedParentData lam hlam hld).objective P.alpha := by
    rw [a.theta_zero_objective_eq_omitted, hattained,
      ← a.theta_zero_wall_value_eq_omitted lam hlam hld,
      a.theta_zero_wall_value_attained lam hlam hld P]
  intro beta
  rw [hsame]
  exact P.minimum beta

theorem selected_bad_preserves_fixed_T
    {k : ℕ} {T m cl cu Az C0 Ct D Bclock : ℝ}
    (a : ActualHighWallData (k+1) (m/10000))
    (hTfix : a.T = T)
    (hE : a.E = wallHighError m (k+1))
    (hd : a.d = wallHighD m (k+1))
    (hs : a.s = wallHighMass m (k+1))
    (htheta : a.theta = 0)
    (htau : a.tau = (((k+1 : ℕ) : ℝ)^(-(10 : ℝ))))
    (heps0 : upperInitialEpsilon m (k+1) ≤ a.epsilon)
    (lam : ℝ) (hlam : lam ∈ Ioo (((k+1 : ℕ) : ℝ)^(-(10 : ℝ))) (a.d^2))
    (alpha : a.Profile)
    (hminimum : ∀ beta : a.Profile,
      (a.thetaZeroShiftedParentData lam
        ((Real.rpow_pos_of_pos a.hN _).trans hlam.1) hlam.2.le).objective alpha ≤
      (a.thetaZeroShiftedParentData lam
        ((Real.rpow_pos_of_pos a.hN _).trans hlam.1) hlam.2.le).objective beta)
    (hm : 0 ≤ m) (hcl : cl ≤ 1) (hcu : 1 ≤ cu)
    (hsA : a.s ≤ comparisonConditionalScale a.N (m/10000) a.E lam)
    (hrA : a.rmin ≤ comparisonConditionalScale a.N (m/10000) a.E lam)
    (hdD : a.d ≤ D) (hupper : Real.sqrt a.N*a.E ≤ a.d^2)
    (hlower : a.N^(-(2 : ℝ)/3+m)*a.d ≤ C0*a.E)
    (hclock : a.T ≤ Bclock) (hAz : 2 ≤ Az) (hCt : 1 ≤ Ct)
    (hbad : ∃ r ∈ Icc (min (comparisonConditionalScale a.N (m/10000)
        a.E lam) 1) 1,
      alpha.val.val r < cl*r ∨ cu*r < alpha.val.val r) :
    ∃ Q : ActualThetaZeroOverlapMinimum (k+1)
        m (m/10000) cl cu Az C0 Ct D Bclock,
      RetainedBadQ T k Q ∧ Q.data = a ∧ Q.lam = lam ∧ HEq Q.alpha alpha := by
  obtain ⟨Q, hdata, hQlam, hQalpha, hxs, _hz, hbadQ⟩ :=
    a.exists_theta_zero_selected_bad_scale_minimum lam
      ((Real.rpow_pos_of_pos a.hN _).trans hlam.1) hlam.2.le alpha hminimum
      (by positivity : 0 ≤ m/10000) hcl hcu hsA hrA hdD hupper
      hlower hclock hAz hCt hbad
  refine ⟨Q, ?_, hdata, hQlam, hQalpha⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hxs.2, hbadQ⟩
  · simpa only [hdata] using hTfix
  · simpa only [hdata] using hE
  · simpa only [hdata] using hd
  · simpa only [hdata] using hs
  · simpa only [hdata] using htheta
  · simpa only [hdata] using htau
  · simpa only [hdata] using heps0
  · simpa only [hdata, hQlam, ActualHighWallData.N] using hlam
  · simpa only [hdata, hQlam] using hxs.1

theorem all_original_attainers_have_exact_base_carrier
    {k : ℕ} {T m cl cu Az C0 Ct D Bclock : ℝ}
    (a : ActualHighWallData (k+1) (m/10000))
    (hTfix : a.T = T)
    (hE : a.E = wallHighError m (k+1))
    (hd : a.d = wallHighD m (k+1))
    (hs : a.s = wallHighMass m (k+1))
    (htheta : a.theta = 0)
    (htau : a.tau = (((k+1 : ℕ) : ℝ)^(-(10 : ℝ))))
    (heps0 : upperInitialEpsilon m (k+1) ≤ a.epsilon)
    (hm : 0 ≤ m) (hcl : cl ≤ 1) (hcu : 1 ≤ cu)
    (hdD : a.d ≤ D) (hupper : Real.sqrt a.N*a.E ≤ a.d^2)
    (hlower : a.N^(-(2 : ℝ)/3+m)*a.d ≤ C0*a.E)
    (hclock : a.T ≤ Bclock) (hAz : 2 ≤ Az) (hCt : 1 ≤ Ct)
    (hstop : ∀ Q : ActualThetaZeroOverlapMinimum (k+1)
      m (m/10000) cl cu Az C0 Ct D Bclock, ¬ RetainedBadQ T k Q)
    (lam : ℝ) (hlam : lam ∈ Ioo (((k+1 : ℕ) : ℝ)^(-(10 : ℝ))) (a.d^2))
    (hsA : a.s ≤ comparisonConditionalScale a.N (m/10000) a.E lam)
    (hrA : a.rmin ≤ comparisonConditionalScale a.N (m/10000) a.E lam)
    (alpha : a.Profile)
    (hminimum : ∀ beta : a.Profile,
      (a.thetaZeroShiftedParentData lam
        ((Real.rpow_pos_of_pos a.hN _).trans hlam.1) hlam.2.le).objective alpha ≤
      (a.thetaZeroShiftedParentData lam
        ((Real.rpow_pos_of_pos a.hN _).trans hlam.1) hlam.2.le).objective beta) :
    ∃ Q : ActualThetaZeroOverlapMinimum (k+1)
        m (m/10000) cl cu Az C0 Ct D Bclock,
      Q.data = a ∧ Q.lam = lam ∧ HEq Q.alpha alpha ∧
      Q.xs = comparisonConditionalScale a.N (m/10000) a.E lam ∧
      Q.z = min (2*comparisonConditionalScale a.N (m/10000) a.E lam) 1 := by
  let A := comparisonConditionalScale a.N (m/10000) a.E lam
  have houter : ∀ r ∈ Icc (min A 1) 1,
      cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r := by
    by_cases hA : 1 ≤ A
    · intro r hr
      rw [min_eq_right hA] at hr
      have hr1 : r = 1 := le_antisymm hr.2 hr.1
      subst r
      simpa only [mul_one, alpha.property.2.1] using And.intro hcl hcu
    · intro r hr
      by_contra hbad
      have hbadRadius : ∃ r ∈ Icc (min A 1) 1,
          alpha.val.val r < cl*r ∨ cu*r < alpha.val.val r := by
        refine ⟨r, hr, ?_⟩
        rcases not_and_or.mp hbad with hlow | hhigh
        · exact Or.inl (lt_of_not_ge hlow)
        · exact Or.inr (lt_of_not_ge hhigh)
      obtain ⟨M, hbadM, _, _, _⟩ := selected_bad_preserves_fixed_T a
        hTfix hE hd hs htheta htau heps0 lam hlam alpha hminimum hm hcl hcu hsA hrA
        hdD hupper hlower hclock hAz hCt hbadRadius
      exact hstop M hbadM
  have hApos : 0 < A := comparison_conditional_scale_pos
    a.hN a.hE ((Real.rpow_pos_of_pos a.hN _).trans hlam.1)
  have hregular : ∀ r ∈ Icc (min (2*A) 1) 1,
      cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r := by
    intro r hr
    exact houter r ⟨(min_le_min (by linarith : A ≤ 2*A) le_rfl).trans hr.1,
      hr.2⟩
  simpa only [A] using a.theta_zero_regular_scale_carrier lam
    ((Real.rpow_pos_of_pos a.hN _).trans hlam.1) hlam.2.le alpha
    hminimum (by positivity : 0 ≤ m/10000) hsA hrA hdD hupper
    hlower hclock hAz hCt hregular

theorem eventually_all_original_attainers_have_exact_base_carrier
    {T m cl cu Az C0 Ct D Bclock : ℝ}
    (H : PhysicalExclusions T m cl cu Az C0 Ct D Bclock)
    (hAz : 2 ≤ Az) (hCt : 1 ≤ Ct) :
    ∀ᶠ k : ℕ in atTop,
      ∀ a : ActualHighWallData (k+1) (m/10000),
        a.T = T →
        a.E = wallHighError m (k+1) →
        a.d = wallHighD m (k+1) →
        a.s = wallHighMass m (k+1) →
        a.theta = 0 →
        a.tau = (((k+1 : ℕ) : ℝ)^(-(10 : ℝ))) →
        upperInitialEpsilon m (k+1) ≤ a.epsilon →
        a.d ≤ D →
        Real.sqrt a.N*a.E ≤ a.d^2 →
        a.N^(-(2 : ℝ)/3+m)*a.d ≤ C0*a.E →
        a.T ≤ Bclock →
        ∀ (lam : ℝ)
          (hlam : lam ∈ Ioo (((k+1 : ℕ) : ℝ)^(-(10 : ℝ))) (a.d^2)),
          a.s ≤ comparisonConditionalScale a.N (m/10000) a.E lam →
          a.rmin ≤ comparisonConditionalScale a.N (m/10000) a.E lam →
          ∀ (alpha : a.Profile),
            omittedComparisonSweepObjective a.hr ⟨a.hs.1.le, a.hs1⟩
              a.hc a.hk a.hkc a.hm a.hM (k+1) a.thetaZeroHighOnlyData.b
              a.thetaZeroHighOnlyData.h a.d lam alpha =
            omittedComparisonSweepMinimum a.hr ⟨a.hs.1.le, a.hs1⟩
              a.hc a.hk a.hkc a.hm a.hM (k+1) a.thetaZeroHighOnlyData.b
              a.thetaZeroHighOnlyData.h a.d lam →
            ∃ Q : ActualThetaZeroOverlapMinimum (k+1)
                m (m/10000) cl cu Az C0 Ct D Bclock,
              Q.data = a ∧ Q.lam = lam ∧ HEq Q.alpha alpha ∧
              Q.xs = comparisonConditionalScale a.N (m/10000) a.E lam ∧
              Q.z = min (2*comparisonConditionalScale a.N (m/10000) a.E lam) 1 := by
  filter_upwards [eventually_no_fixed_T_retained_bad_q H] with k hk
  intro a hTfix hE hd hs htheta htau heps0 hdD hupper hlower hclock
    lam hlam hsA hrA alpha hattained
  have hminimum := original_sweep_attainer_is_global_minimum a lam
    ((Real.rpow_pos_of_pos a.hN _).trans hlam.1) hlam.2.le alpha hattained
  exact all_original_attainers_have_exact_base_carrier a
    hTfix hE hd hs htheta htau heps0 H.hm.le H.hcl1 H.hcu1 hdD hupper hlower
    hclock hAz hCt hk lam hlam hsA hrA alpha hminimum

end OriginalQFixedTStoppingDraft
end OAI.SKFluctuations.LaplaceWindowFormalization
