module

public import ComparisonRegularWallMeanNumericChoiceDraft
public import ComparisonFinalWallQuantifierBridgeDraft
public import ComparisonConcretePositiveWallMeanWrapperDraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Cavity PositiveLaplaceAssembly
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 48000000

theorem eventually_regular_wall_mean_bound_for_any_concrete_sequence
    {T m cl cu : ℝ}
    (hT : 0 < T) (hm : 0 < m) (hmmax : m < 1 / 300)
    (hcl : 0 < cl) (hcu : 0 < cu)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (x : (j : ℕ) → RegularWallMeanSample T m cl cu (dim j)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ j : ℕ in atTop, regularWallMeanBound C (dim j) (x j) := by
  obtain ⟨q⟩ := exists_concrete_regular_wall_mean_numeric_choice hT hm hcu
  let M : (j : ℕ) → ActualHighWallOverlapMinimum (dim j + 1)
      m (m / 10000) cl cu 1 1 1 1 T := fun j => (x j).M
  have hfixed : ∀ j, (M j).xs = (M j).data.d := fun j => (x j).hfixed
  have hTbound : ∀ j, T ≤ (M j).data.T := by
    intro j
    rw [(x j).hT]
  have hconcrete : ∀ j, (M j).data.d = wallHighD m (dim j + 1) :=
    fun j => (x j).hd
  have hepsilon : ∀ j, upperInitialEpsilon m (dim j + 1) ≤
      (M j).data.epsilon := fun j => (x j).hepsilon
  have hN : Tendsto (fun j => ((dim j + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim)
  have hdlim : Tendsto (fun j => (M j).data.d) atTop (𝓝 0) := by
    have H := (tendsto_rpow_neg_atTop
      (show 0 < (1 : ℝ) / 6 - 15 * m by linarith only [hmmax])).comp hN
    apply H.congr'
    apply Eventually.of_forall
    intro j
    simp only [Function.comp_apply]
    rw [(x j).hd]
    unfold wallHighD
    congr 1
    ring
  have hsRatio : Tendsto
      (fun j => (M j).data.s / (M j).data.d) atTop (𝓝 0) := by
    have H := (tendsto_rpow_neg_atTop
      (show 0 < 10 * m by positivity)).comp hN
    apply H.congr'
    apply Eventually.of_forall
    intro j
    simp only [Function.comp_apply]
    rw [(x j).hs, (x j).hd]
    have hNj : 0 < (((dim j + 1 : ℕ) : ℝ)) := by positivity
    unfold wallHighMass wallHighD
    rw [← Real.rpow_sub hNj]
    congr 1
    ring
  have hdelta : 0 < m / 10000 := by positivity
  have hroom : m / 10000 < 3 * m := by linarith only [hm]
  obtain ⟨C, hC, HC⟩ :=
    Cavity.eventually_actual_high_wall_omitted_mean_cubic_from_regular_physical_minimum_along
      (m := m) (delta := m / 10000) (cl := cl) (cu := cu)
      (Az := 1) (C0 := 1) (Ct := 1) (D := 1) (Bclock := T)
      (L := q.L) (eta := q.eta) (c := q.c) (cK := q.cK) (T0 := T)
      q.dOrder q.hdOrder q.p q.hp q.hOrder q.htheta1 q.htheta2 q.hdeficit
      q.Cmass q.Rmacro q.F q.Cx q.hCm q.hCx q.heta
      hm hdelta hroom q.hgap hcl hcu (by norm_num) (by norm_num)
      (by norm_num) q.hmacro q.hRhalf q.hFmass q.hFradius q.hL
      q.hc q.hcout q.hcK hT q.hKroom q.hbandRoom
      dim hdim M hfixed hdlim hsRatio hTbound hmmax hconcrete hepsilon
  refine ⟨C, hC, ?_⟩
  filter_upwards [HC] with j hj
  exact hj (x j).u ⟨(x j).hu.1.le, (x j).hu.2⟩

theorem eventually_uniform_strict_regular_concrete_wall_mean
    {T m cl cu : ℝ}
    (hT : 0 < T) (hm : 0 < m) (hmmax : m < 1 / 300)
    (hcl : 0 < cl) (hcu : 0 < cu) :
    ∃ Cw : ℝ, 1 ≤ Cw ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ x : RegularWallMeanSample T m cl cu n,
          orderedPathS (n + 1) x.M.bf x.M.hf x.u <
            wallMeanScale Cw x.M.data.d x.M.data.epsilon := by
  exact eventually_uniform_strict_regular_wall_mean_of_sequence_bounds
    (fun dim hdim x =>
      eventually_regular_wall_mean_bound_for_any_concrete_sequence
        hT hm hmmax hcl hcu dim hdim x)

theorem eventually_concrete_positive_wall_mean_of_all_minima_regular
    {T m cl cu : ℝ}
    (hT : 0 < T) (hm : 0 < m) (hmmax : m < 1 / 300)
    (hcl : 0 < cl) (hcu : 0 < cu)
    (hregular : ∀ᶠ n : ℕ in atTop,
      ∀ x : OriginalPositiveWallMinimumSample T m n,
        ∀ r ∈ Icc (wallHighD m (n + 1)) 1,
          cl * r ≤ x.alpha.val.val r ∧
            x.alpha.val.val r ≤ cu * r) :
    ∃ Cw : ℝ, 1 ≤ Cw ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ hp : ActualConcreteHighWallNumeric m (n + 1),
        ∀ epsilon : ℝ, ∀ hepsilon : epsilon ∈ Ioo (0 : ℝ) T,
        ∀ heps0 : upperInitialEpsilon m (n + 1) ≤ epsilon,
          concretePositiveThetaMeanAtNumeric T Cw m (n + 1) hp epsilon
            hepsilon heps0 := by
  obtain ⟨Cw, hCw, hbound⟩ :=
    eventually_uniform_strict_regular_concrete_wall_mean
      hT hm hmmax hcl hcu
  refine ⟨Cw, hCw, ?_⟩
  filter_upwards [hregular, hbound] with n hnRegular hnBound
  intro hp epsilon hepsilon heps0
  dsimp only [concretePositiveThetaMeanAtNumeric]
  intro theta htheta alpha hmin u hu
  let raw : OriginalPositiveWallMinimumSample T m n := {
    hp := hp, epsilon := epsilon, hepsilon := hepsilon, heps0 := heps0,
    theta := theta, htheta := htheta, alpha := alpha, minimum := hmin }
  have hprofile := hnRegular raw
  let M := actualConcreteHighWallOverlapMinimum hp hepsilon heps0 htheta
    alpha hmin hprofile
  let sample : RegularWallMeanSample T m cl cu n := {
    M := M, hfixed := rfl, hT := rfl, hE := rfl, hd := rfl,
    hs := rfl, hepsilon := heps0, u := u, hu := hu }
  exact hnBound sample

theorem eventually_concrete_positive_wall_mean_of_physical_exclusions
    {T m cl cu : ℝ}
    (hT : 0 < T) (hm : 0 < m) (hmmax : m < 1 / 300)
    (hcl : 0 < cl) (hcu : 0 < cu)
    (hcl1 : cl ≤ 1) (hcu1 : 1 ≤ cu)
    (hsmall : ∀ dim : ℕ → ℕ, Tendsto dim atTop atTop →
      ∀ x : (j : ℕ) → OriginalPositiveWallSelectedBadSample T m cl cu (dim j),
        (∀ j, selectedBadSmallEpsilon (dim j) (x j)) → False)
    (hlarge : ∀ dim : ℕ → ℕ, Tendsto dim atTop atTop →
      ∀ x : (j : ℕ) → OriginalPositiveWallSelectedBadSample T m cl cu (dim j),
        (∀ j, selectedBadLargeEpsilon (dim j) (x j)) → False) :
    ∃ Cw : ℝ, 1 ≤ Cw ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ hp : ActualConcreteHighWallNumeric m (n + 1),
        ∀ epsilon : ℝ, ∀ hepsilon : epsilon ∈ Ioo (0 : ℝ) T,
        ∀ heps0 : upperInitialEpsilon m (n + 1) ≤ epsilon,
          concretePositiveThetaMeanAtNumeric T Cw m (n + 1) hp epsilon
            hepsilon heps0 := by
  exact eventually_concrete_positive_wall_mean_of_all_minima_regular
    hT hm hmmax hcl hcu
    (eventually_all_original_wall_minima_regular_of_physical_exclusions
      hcl1 hcu1 hsmall hlarge)

theorem eventually_concrete_positive_wall_mean_all_sizes_of_physical_exclusions
    {T m cl cu : ℝ}
    (hT : 0 < T) (hm : 0 < m) (hmmax : m < 1 / 300)
    (hcl : 0 < cl) (hcu : 0 < cu)
    (hcl1 : cl ≤ 1) (hcu1 : 1 ≤ cu)
    (hsmall : ∀ dim : ℕ → ℕ, Tendsto dim atTop atTop →
      ∀ x : (j : ℕ) → OriginalPositiveWallSelectedBadSample T m cl cu (dim j),
        (∀ j, selectedBadSmallEpsilon (dim j) (x j)) → False)
    (hlarge : ∀ dim : ℕ → ℕ, Tendsto dim atTop atTop →
      ∀ x : (j : ℕ) → OriginalPositiveWallSelectedBadSample T m cl cu (dim j),
        (∀ j, selectedBadLargeEpsilon (dim j) (x j)) → False) :
    ∃ Cw : ℝ, 1 ≤ Cw ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ hp : ActualConcreteHighWallNumeric m n,
        ∀ epsilon : ℝ, ∀ hepsilon : epsilon ∈ Ioo (0 : ℝ) T,
        ∀ heps0 : upperInitialEpsilon m n ≤ epsilon,
          concretePositiveThetaMeanAtNumeric T Cw m n hp epsilon
            hepsilon heps0 := by
  obtain ⟨Cw, hCw, H⟩ :=
    eventually_concrete_positive_wall_mean_of_physical_exclusions
      hT hm hmmax hcl hcu hcl1 hcu1 hsmall hlarge
  refine ⟨Cw, hCw, ?_⟩
  exact eventually_of_eventually_succ
    (fun n => ∀ hp : ActualConcreteHighWallNumeric m n,
      ∀ epsilon : ℝ, ∀ hepsilon : epsilon ∈ Ioo (0 : ℝ) T,
      ∀ heps0 : upperInitialEpsilon m n ≤ epsilon,
        concretePositiveThetaMeanAtNumeric T Cw m n hp epsilon
          hepsilon heps0) H

theorem eventually_concrete_high_wall_inputs_of_sharp_and_exclusions
    {T m cl cu : ℝ}
    (hT : 0 < T) (hm : 0 < m) (hmmax : m < 1 / 300)
    (hcl : 0 < cl) (hcu : 0 < cu)
    (hcl1 : cl ≤ 1) (hcu1 : 1 ≤ cu)
    (hsmall : ∀ dim : ℕ → ℕ, Tendsto dim atTop atTop →
      ∀ x : (j : ℕ) → OriginalPositiveWallSelectedBadSample T m cl cu (dim j),
        (∀ j, selectedBadSmallEpsilon (dim j) (x j)) → False)
    (hlarge : ∀ dim : ℕ → ℕ, Tendsto dim atTop atTop →
      ∀ x : (j : ℕ) → OriginalPositiveWallSelectedBadSample T m cl cu (dim j),
        (∀ j, selectedBadLargeEpsilon (dim j) (x j)) → False)
    (hsharp : ∀ᶠ n : ℕ in atTop,
      ∀ hp : ActualConcreteHighWallNumeric m n,
      ∀ epsilon : ℝ, ∀ hepsilon : epsilon ∈ Ioo (0 : ℝ) T,
      ∀ heps0 : upperInitialEpsilon m n ≤ epsilon,
        concreteSharpCostAtNumeric T m n hp epsilon hepsilon heps0) :
    ∃ Cw : ℝ, 1 ≤ Cw ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ hp : ConcreteHighWallGeometry m n,
        ∀ epsilon : ℝ, ∀ hepsilon : epsilon ∈ Ioo (0 : ℝ) T,
        ∀ heps0 : upperInitialEpsilon m n ≤ epsilon,
          concreteHighWallPhysicalInputs T Cw m n hp epsilon := by
  obtain ⟨Cw, hCw, Hmean⟩ :=
    eventually_concrete_positive_wall_mean_all_sizes_of_physical_exclusions
      hT hm hmmax hcl hcu hcl1 hcu1 hsmall hlarge
  exact ⟨Cw, hCw,
    eventually_concrete_high_wall_physical_inputs_of_numeric_fields
      hm hmmax hsharp Hmean⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
