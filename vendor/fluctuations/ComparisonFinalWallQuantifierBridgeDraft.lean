module

public import ComparisonSequentialUniformization
public import ComparisonActualHighWallOmittedMeanFromRegularMinimumAlong
public import ComparisonActualConcreteHighWallAmplitude
public import ComparisonActualHighWallSelectedBadScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Cavity PositiveLaplaceAssembly
open scoped Topology NNReal
set_option autoImplicit false

theorem eventually_of_eventually_succ (P : ℕ → Prop)
    (H : ∀ᶠ n : ℕ in atTop, P (n + 1)) :
    ∀ᶠ n : ℕ in atTop, P n := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp H
  apply eventually_atTop.mpr
  refine ⟨N + 1, ?_⟩
  intro n hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  apply hN j
  omega

theorem eventually_no_bad_of_cofinal_exclusion
    (X : ℕ → Type*) (Bad : (n : ℕ) → X n → Prop)
    (hexclude : ∀ dim : ℕ → ℕ, Tendsto dim atTop atTop →
      ∀ x : (j : ℕ) → X (dim j),
        (∀ j, Bad (dim j) (x j)) → False) :
    ∀ᶠ n : ℕ in atTop, ∀ x : X n, ¬ Bad n x := by
  classical
  by_contra hnone
  have hbad (j : ℕ) : ∃ n : ℕ, j ≤ n ∧ ∃ x : X n, Bad n x := by
    by_contra h
    have hgood : ∀ᶠ n : ℕ in atTop, ∀ x : X n, ¬ Bad n x :=
      eventually_atTop.mpr ⟨j, by
        intro n hn x hx
        exact h ⟨n, hn, x, hx⟩⟩
    exact hnone hgood
  choose dim hdim x hx using hbad
  have hdimTop : Tendsto dim atTop atTop :=
    tendsto_atTop_mono hdim tendsto_id
  exact hexclude dim hdimTop x hx

theorem eventually_regular_of_two_selected_bad_exclusions
    (Raw Selected : ℕ → Type*)
    (irregular : (n : ℕ) → Raw n → Prop)
    (selectedBad smallEpsilon largeEpsilon :
      (n : ℕ) → Selected n → Prop)
    (hselect : ∀ n (a : Raw n), irregular n a →
      ∃ b : Selected n, selectedBad n b)
    (hsplit : ∀ n (b : Selected n), selectedBad n b →
      smallEpsilon n b ∨ largeEpsilon n b)
    (hsmall : ∀ dim : ℕ → ℕ, Tendsto dim atTop atTop →
      ∀ b : (j : ℕ) → Selected (dim j),
        (∀ j, smallEpsilon (dim j) (b j)) → False)
    (hlarge : ∀ dim : ℕ → ℕ, Tendsto dim atTop atTop →
      ∀ b : (j : ℕ) → Selected (dim j),
        (∀ j, largeEpsilon (dim j) (b j)) → False) :
    ∀ᶠ n : ℕ in atTop, ∀ a : Raw n, ¬ irregular n a := by
  have hs := eventually_no_bad_of_cofinal_exclusion Selected smallEpsilon hsmall
  have hl := eventually_no_bad_of_cofinal_exclusion Selected largeEpsilon hlarge
  filter_upwards [hs, hl] with n hsn hln a ha
  obtain ⟨b, hb⟩ := hselect n a ha
  rcases hsplit n b hb with hsmallB | hlargeB
  · exact hsn b hsmallB
  · exact hln b hlargeB

structure OriginalPositiveWallMinimumSample (T m : ℝ) (n : ℕ) where
  hp : ActualConcreteHighWallNumeric m (n + 1)
  epsilon : ℝ
  hepsilon : epsilon ∈ Ioo (0 : ℝ) T
  heps0 : upperInitialEpsilon m (n + 1) ≤ epsilon
  theta : ℝ
  htheta : theta ∈ Icc (0 : ℝ) 1
  alpha :
    (actualConcreteHighWallData T m (n + 1) hp epsilon theta
      hepsilon heps0 htheta).Profile
  minimum :
    ∀ beta :
      (actualConcreteHighWallData T m (n + 1) hp epsilon theta
        hepsilon heps0 htheta).Profile,
      (actualConcreteHighWallData T m (n + 1) hp epsilon theta
        hepsilon heps0 htheta).objective alpha ≤
      (actualConcreteHighWallData T m (n + 1) hp epsilon theta
        hepsilon heps0 htheta).objective beta

def originalPositiveWallIrregular {T m cl cu : ℝ} (n : ℕ)
    (x : OriginalPositiveWallMinimumSample T m n) : Prop :=
  ∃ r ∈ Icc (wallHighD m (n + 1)) 1,
    x.alpha.val.val r < cl * r ∨ cu * r < x.alpha.val.val r

structure OriginalPositiveWallSelectedBadSample
    (T m cl cu : ℝ) (n : ℕ) where
  P : ActualHighWallOverlapMinimum (n + 1) m (m / 10000)
    cl cu 2 1 1 1 T
  hT : P.data.T = T
  hE : P.data.E = wallHighError m (n + 1)
  hd : P.data.d = wallHighD m (n + 1)
  hs : P.data.s = wallHighMass m (n + 1)
  hunit : P.xs ≤ 1
  hdxs : P.data.d ≤ P.xs
  hbad : P.alpha.val.val P.xs < cl * P.xs ∨
    cu * P.xs < P.alpha.val.val P.xs

def selectedBadSmallEpsilon {T m cl cu : ℝ} (n : ℕ)
    (x : OriginalPositiveWallSelectedBadSample T m cl cu n) : Prop :=
  x.P.data.epsilon < T / 4

def selectedBadLargeEpsilon {T m cl cu : ℝ} (n : ℕ)
    (x : OriginalPositiveWallSelectedBadSample T m cl cu n) : Prop :=
  T / 4 ≤ x.P.data.epsilon

theorem original_positive_wall_bad_minimum_selects_bad_scale
    {T m cl cu : ℝ} (hcl1 : cl ≤ 1) (hcu1 : 1 ≤ cu)
    (n : ℕ) (x : OriginalPositiveWallMinimumSample T m n)
    (hbad : originalPositiveWallIrregular (cl := cl) (cu := cu) n x) :
    Nonempty (OriginalPositiveWallSelectedBadSample T m cl cu n) := by
  let a := actualConcreteHighWallData T m (n + 1) x.hp x.epsilon x.theta
    x.hepsilon x.heps0 x.htheta
  obtain ⟨P, hdata, _halpha, hdxs, hunit, _hz, hbadP⟩ :=
    a.exists_selected_bad_scale_minimum
      (m := m) (cl := cl) (cu := cu) (C0 := 1) (D := 1) (Bclock := T)
      x.alpha x.minimum hcl1 hcu1 x.hp.hsD x.hp.hd1
      x.hp.hupper (by simpa only [one_mul,a,actualConcreteHighWallData,ActualHighWallData.N] using x.hp.hlower) (by dsimp [a]; exact le_rfl)
      (by simpa only [originalPositiveWallIrregular, a,
        actualConcreteHighWallData] using hbad)
  refine ⟨{
    P := P
    hT := ?_
    hE := ?_
    hd := ?_
    hs := ?_
    hunit := hunit
    hdxs := by rw [hdata];exact hdxs
    hbad := hbadP }⟩
  all_goals rw [hdata]
  all_goals rfl

theorem eventually_all_original_wall_minima_regular_of_selected_exclusions
    {T m cl cu : ℝ}
    (hselect : ∀ n (x : OriginalPositiveWallMinimumSample T m n),
      originalPositiveWallIrregular (cl := cl) (cu := cu) n x →
        Nonempty (OriginalPositiveWallSelectedBadSample T m cl cu n))
    (hsmall : ∀ dim : ℕ → ℕ, Tendsto dim atTop atTop →
      ∀ x : (j : ℕ) → OriginalPositiveWallSelectedBadSample T m cl cu (dim j),
        (∀ j, selectedBadSmallEpsilon (dim j) (x j)) → False)
    (hlarge : ∀ dim : ℕ → ℕ, Tendsto dim atTop atTop →
      ∀ x : (j : ℕ) → OriginalPositiveWallSelectedBadSample T m cl cu (dim j),
        (∀ j, selectedBadLargeEpsilon (dim j) (x j)) → False) :
    ∀ᶠ n : ℕ in atTop,
      ∀ x : OriginalPositiveWallMinimumSample T m n,
        ∀ r ∈ Icc (wallHighD m (n + 1)) 1,
          cl * r ≤ x.alpha.val.val r ∧
            x.alpha.val.val r ≤ cu * r := by
  have hs := eventually_no_bad_of_cofinal_exclusion
    (fun n => OriginalPositiveWallSelectedBadSample T m cl cu n)
    (selectedBadSmallEpsilon (T := T) (m := m) (cl := cl) (cu := cu))
    hsmall
  have hl := eventually_no_bad_of_cofinal_exclusion
    (fun n => OriginalPositiveWallSelectedBadSample T m cl cu n)
    (selectedBadLargeEpsilon (T := T) (m := m) (cl := cl) (cu := cu))
    hlarge
  filter_upwards [hs, hl] with n hsn hln
  intro x r hr
  have hgood : ¬ originalPositiveWallIrregular (cl := cl) (cu := cu) n x := by
    intro hbad
    obtain ⟨y⟩ := hselect n x hbad
    rcases lt_or_ge y.P.data.epsilon (T / 4) with hsmallY | hlargeY
    · exact hsn y hsmallY
    · exact hln y hlargeY
  constructor
  · by_contra hleft
    exact hgood ⟨r, hr, Or.inl (lt_of_not_ge hleft)⟩
  · by_contra hright
    exact hgood ⟨r, hr, Or.inr (lt_of_not_ge hright)⟩

theorem eventually_all_original_wall_minima_regular_of_physical_exclusions
    {T m cl cu : ℝ} (hcl1 : cl ≤ 1) (hcu1 : 1 ≤ cu)
    (hsmall : ∀ dim : ℕ → ℕ, Tendsto dim atTop atTop →
      ∀ x : (j : ℕ) → OriginalPositiveWallSelectedBadSample T m cl cu (dim j),
        (∀ j, selectedBadSmallEpsilon (dim j) (x j)) → False)
    (hlarge : ∀ dim : ℕ → ℕ, Tendsto dim atTop atTop →
      ∀ x : (j : ℕ) → OriginalPositiveWallSelectedBadSample T m cl cu (dim j),
        (∀ j, selectedBadLargeEpsilon (dim j) (x j)) → False) :
    ∀ᶠ n : ℕ in atTop,
      ∀ x : OriginalPositiveWallMinimumSample T m n,
        ∀ r ∈ Icc (wallHighD m (n + 1)) 1,
          cl * r ≤ x.alpha.val.val r ∧
            x.alpha.val.val r ≤ cu * r := by
  exact eventually_all_original_wall_minima_regular_of_selected_exclusions
    (original_positive_wall_bad_minimum_selects_bad_scale hcl1 hcu1)
    hsmall hlarge

structure RegularWallMeanSample (T m cl cu : ℝ) (n : ℕ) where
  M : ActualHighWallOverlapMinimum (n + 1) m (m / 10000) cl cu 1 1 1 1 T
  hfixed : M.xs = M.data.d
  hT : M.data.T = T
  hE : M.data.E = wallHighError m (n + 1)
  hd : M.data.d = wallHighD m (n + 1)
  hs : M.data.s = wallHighMass m (n + 1)
  hepsilon : upperInitialEpsilon m (n + 1) ≤ M.data.epsilon
  u : ℝ
  hu : u ∈ Ioo (0 : ℝ) M.data.s

def regularWallMeanBound {T m cl cu : ℝ}
    (C : ℝ) (n : ℕ) (x : RegularWallMeanSample T m cl cu n) : Prop :=
  orderedPathS (n + 1) x.M.bf x.M.hf x.u ≤
    wallMeanScale C x.M.data.d x.M.data.epsilon

theorem eventually_uniform_strict_regular_wall_mean_of_sequence_bounds
    {T m cl cu : ℝ}
    (hsequence : ∀ dim : ℕ → ℕ, Tendsto dim atTop atTop →
      ∀ x : (j : ℕ) → RegularWallMeanSample T m cl cu (dim j),
        ∃ C : ℝ, 0 < C ∧
          ∀ᶠ j : ℕ in atTop,
            regularWallMeanBound C (dim j) (x j)) :
    ∃ Cw : ℝ, 1 ≤ Cw ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ x : RegularWallMeanSample T m cl cu n,
          orderedPathS (n + 1) x.M.bf x.M.hf x.u <
            wallMeanScale Cw x.M.data.d x.M.data.epsilon := by
  have hmono : ∀ C C' n (x : RegularWallMeanSample T m cl cu n),
      C ≤ C' → regularWallMeanBound C n x →
        regularWallMeanBound C' n x := by
    intro C C' n x hCC' hx
    have hscale : 0 ≤ x.M.data.d ^ 3 / x.M.data.epsilon :=
      div_nonneg (pow_nonneg x.M.data.hd.le 3) x.M.data.hepsilon.1.le
    calc
      orderedPathS (n + 1) x.M.bf x.M.hf x.u ≤
          C * (x.M.data.d ^ 3 / x.M.data.epsilon) := by
            simpa only [regularWallMeanBound, wallMeanScale, mul_div_assoc] using hx
      _ ≤ C' * (x.M.data.d ^ 3 / x.M.data.epsilon) :=
        mul_le_mul_of_nonneg_right hCC' hscale
      _ = wallMeanScale C' x.M.data.d x.M.data.epsilon := by
        simp only [wallMeanScale, mul_div_assoc]
  obtain ⟨C, hC, HC⟩ :=
    eventual_uniform_bound_of_every_cofinal_sequence
      (fun n => RegularWallMeanSample T m cl cu n)
      (regularWallMeanBound (T := T) (m := m) (cl := cl) (cu := cu))
      hmono hsequence
  let Cw : ℝ := max 1 (C + 1)
  have hCw : 1 ≤ Cw := le_max_left _ _
  have hstrict : C < Cw := by
    dsimp only [Cw]
    linarith only [le_max_right (1 : ℝ) (C + 1)]
  refine ⟨Cw, hCw, ?_⟩
  filter_upwards [HC] with n hn x
  have hscale : 0 < x.M.data.d ^ 3 / x.M.data.epsilon :=
    div_pos (pow_pos x.M.data.hd 3) x.M.data.hepsilon.1
  calc
    orderedPathS (n + 1) x.M.bf x.M.hf x.u ≤
        C * (x.M.data.d ^ 3 / x.M.data.epsilon) := by
          simpa only [regularWallMeanBound, wallMeanScale, mul_div_assoc] using hn x
    _ < Cw * (x.M.data.d ^ 3 / x.M.data.epsilon) :=
      mul_lt_mul_of_pos_right hstrict hscale
    _ = wallMeanScale Cw x.M.data.d x.M.data.epsilon := by
      simp only [wallMeanScale, mul_div_assoc]

end OAI.SKFluctuations.LaplaceWindowFormalization
