module

public import ComparisonActualHighWallOmittedMeanFromRegularMinimumAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Cavity Hierarchy NativeOverlapMinimum
open scoped Topology
set_option autoImplicit false

structure ConcreteRegularWallMeanNumericChoice (T m cu : ℝ) where
  dOrder : ℕ
  p : ℝ
  Cmass : ℝ
  Rmacro : ℝ
  F : ℝ
  Cx : ℝ
  eta : ℝ
  L : ℝ
  c : ℝ
  cK : ℝ
  hdOrder : 0 < dOrder
  hp : 2 < p
  hOrder : p / (p - 2) ≤ (dOrder : ℝ)
  htheta1 : 1 ≤ 4 / p
  htheta2 : 4 / p ≤ 2
  hdeficit : 2 - 4 / p ≤ actualMassSavingExponent m (m / 10000) / 128
  hCm : 1 ≤ Cmass
  hCx : 0 < Cx
  heta : 0 < eta
  hgap : 2 * eta < 6 * m
  hmacro : 0 < Rmacro
  hRhalf : Rmacro ≤ 1 / 2
  hFmass : 1 + 2 * cu ≤ F
  hFradius : 1 + 1 / Rmacro ≤ F
  hL : 0 < L
  hc : 0 < c
  hcout : cu * (1 : ℝ) < c
  hcK : 0 < cK
  hKroom : cK ≤ 3 * T * (starMassBandConstant cu (1 : ℝ) / cu) / 8
  hbandRoom : calibratedBandStart cu 1 + 4 * L ≤ Cmass

theorem exists_concrete_regular_wall_mean_numeric_choice
    {T m cu : ℝ} (hT : 0 < T) (hm : 0 < m) (hcu : 0 < cu) :
    Nonempty (ConcreteRegularWallMeanNumericChoice T m cu) := by
  classical
  let delta : ℝ := m / 10000
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  let saving : ℝ := actualMassSavingExponent m delta
  have hsaving : 0 < saving := by
    dsimp [saving, actualMassSavingExponent]
    have hm1 : 0 < min m delta := lt_min hm hdelta
    exact div_pos (lt_min (by norm_num) hm1) (by norm_num)
  have hsavingUpper : saving ≤ 1 / 64 := by
    dsimp [saving, actualMassSavingExponent]
    exact div_le_div_of_nonneg_right (min_le_left (1 : ℝ) (min m delta))
      (by norm_num)
  let sigma : ℝ := saving / 256
  have hsigma : 0 < sigma := by dsimp [sigma]; positivity
  have hsigmaSmall : sigma < 1 := by
    dsimp [sigma]
    linarith only [hsavingUpper]
  let p : ℝ := 2 + sigma
  have hp : 2 < p := by dsimp [p]; linarith only [hsigma]
  have hp0 : 0 < p := by linarith only [hp]
  have hp4 : p ≤ 4 := by dsimp [p]; linarith only [hsigmaSmall]
  have htheta1 : 1 ≤ 4 / p := by
    apply (le_div_iff₀ hp0).mpr
    linarith only [hp4]
  have htheta2 : 4 / p ≤ 2 := by
    apply (div_le_iff₀ hp0).mpr
    linarith only [hp]
  have hdeficit : 2 - 4 / p ≤ saving / 128 := by
    have hfirst : 2 - 4 / p ≤ sigma := by
      have hnum : (2 - sigma) * p ≤ 4 := by
        dsimp [p]
        nlinarith only [sq_nonneg sigma]
      have hdiv : 2 - sigma ≤ 4 / p :=
        (le_div_iff₀ hp0).mpr hnum
      linarith only [hdiv]
    have hsecond : sigma ≤ saving / 128 := by
      dsimp [sigma]
      linarith only [hsaving]
    exact hfirst.trans hsecond
  obtain ⟨dOrder, horderCast⟩ := exists_nat_gt (p / (p - 2))
  have horderPositive : 0 < p / (p - 2) := by
    apply div_pos hp0
    dsimp [p]
    linarith only [hsigma]
  have hdOrder : 0 < dOrder := by
    by_contra hnot
    have hz : dOrder = 0 := Nat.eq_zero_of_not_pos hnot
    simp only [hz, Nat.cast_zero] at horderCast
    exact (not_lt_of_ge horderPositive.le) horderCast
  let Rmacro : ℝ := 1 / 4
  let L : ℝ := 1
  let Cx : ℝ := 1
  let eta : ℝ := m
  let c : ℝ := cu + 1
  let cK : ℝ := T / 8
  let Cmass : ℝ := calibratedBandStart cu 1 + 5
  let F : ℝ := max (1 + 2 * cu) 5 + 1
  have hstart : 2 ≤ calibratedBandStart cu 1 := by
    unfold calibratedBandStart starMassBandConstant
    nlinarith only [hcu.le]
  have hCm : 1 ≤ Cmass := by dsimp [Cmass]; linarith only [hstart]
  have hFradius : 1 + 1 / Rmacro ≤ F := by
    have hEq : 1 + 1 / Rmacro = (5 : ℝ) := by
      dsimp [Rmacro]
      norm_num
    rw [hEq]
    dsimp [F]
    have hmax : (5 : ℝ) ≤ max (1 + 2 * cu) 5 := le_max_right _ _
    linarith only [hmax]
  have hFmass : 1 + 2 * cu ≤ F := by
    dsimp [F]
    linarith only [le_max_left (1 + 2 * cu) (5 : ℝ)]
  have hKroom : cK ≤ 3 * T * (starMassBandConstant cu 1 / cu) / 8 := by
    have hstar : cu ≤ starMassBandConstant cu 1 := by
      unfold starMassBandConstant
      nlinarith only [hcu]
    have hratio : 1 ≤ starMassBandConstant cu 1 / cu :=
      (le_div_iff₀ hcu).mpr (by simpa only [one_mul] using hstar)
    have hproduct :
        0 ≤ T * (starMassBandConstant cu 1 / cu - 1) :=
      mul_nonneg hT.le (sub_nonneg.mpr hratio)
    dsimp [cK]
    nlinarith only [hproduct, hT]
  have hbandRoom : calibratedBandStart cu 1 + 4 * L ≤ Cmass := by
    dsimp [L, Cmass]
    linarith
  let choice : ConcreteRegularWallMeanNumericChoice T m cu := {
    dOrder := dOrder, p := p, Cmass := Cmass, Rmacro := Rmacro,
    F := F, Cx := Cx, eta := eta, L := L, c := c, cK := cK,
    hdOrder := hdOrder, hp := hp, hOrder := horderCast.le,
    htheta1 := htheta1, htheta2 := htheta2,
    hdeficit := by simpa only [saving, delta] using hdeficit,
    hCm := hCm, hCx := by dsimp [Cx]; norm_num,
    heta := by dsimp [eta]; exact hm,
    hgap := by dsimp [eta]; linarith only [hm],
    hmacro := by dsimp [Rmacro]; norm_num,
    hRhalf := by dsimp [Rmacro]; norm_num,
    hFmass := hFmass, hFradius := hFradius,
    hL := by dsimp [L]; norm_num,
    hc := by dsimp [c]; linarith only [hcu],
    hcout := by dsimp [c]; nlinarith,
    hcK := by dsimp [cK]; positivity,
    hKroom := hKroom, hbandRoom := hbandRoom }
  exact ⟨choice⟩

theorem exists_common_original_wall_profile_margins
    {T lowerSmall upperSmall lowerLarge upperLarge : ℝ}
    (hT : 0 < T) (hLowerSmall : 0 < lowerSmall)
    (hUpperSmall : 0 < upperSmall) (hLowerLarge : 0 < lowerLarge)
    (hUpperLarge : 0 < upperLarge) :
    ∃ cl cu : ℝ,
      0 < cl ∧ cl ≤ 1 ∧ cl ≤ lowerSmall ∧ cl ≤ lowerLarge ∧
      cl < T * Real.exp (-12 * T) ∧
      0 < cu ∧ 1 ≤ cu ∧ upperSmall ≤ cu ∧ upperLarge ≤ cu ∧
      T * (ReplicaTree.attachmentCount 1 3 : ℝ)^2 /
        (2 * Real.exp (-12 * T)) < cu := by
  let temp : ℝ := T * Real.exp (-12 * T)
  have htemp : 0 < temp := by dsimp [temp]; positivity
  let lo : ℝ := min lowerSmall (min lowerLarge (min 1 temp))
  have hlo : 0 < lo := by
    dsimp [lo]
    exact lt_min hLowerSmall (lt_min hLowerLarge (lt_min (by norm_num) htemp))
  have hloSmall : lo ≤ lowerSmall := by dsimp [lo]; exact min_le_left _ _
  have hloLarge : lo ≤ lowerLarge := by
    dsimp [lo]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hloOne : lo ≤ 1 := by
    dsimp [lo]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hloTemp : lo ≤ temp := by
    dsimp [lo]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let cl : ℝ := lo / 2
  let scalar : ℝ := T * (ReplicaTree.attachmentCount 1 3 : ℝ)^2 /
    (2 * Real.exp (-12 * T))
  let hi : ℝ := max upperSmall (max upperLarge (max 1 (scalar + 1)))
  have hhiSmall : upperSmall ≤ hi := by dsimp [hi]; exact le_max_left _ _
  have hhiLarge : upperLarge ≤ hi := by
    dsimp [hi]
    exact (le_max_left upperLarge (max 1 (scalar+1))).trans
      (le_max_right upperSmall (max upperLarge (max 1 (scalar+1))))
  have hhiOne : 1 ≤ hi := by
    dsimp [hi]
    exact (le_max_left (1:ℝ) (scalar+1)).trans
      ((le_max_right upperLarge (max 1 (scalar+1))).trans
        (le_max_right upperSmall (max upperLarge (max 1 (scalar+1)))))
  have hhiScalar : scalar + 1 ≤ hi := by
    dsimp [hi]
    exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  let cu : ℝ := hi + 1
  refine ⟨cl, cu, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [cl]; positivity
  · dsimp [cl]; linarith only [hlo, hloOne]
  · dsimp [cl]; linarith only [hlo, hloSmall]
  · dsimp [cl]; linarith only [hlo, hloLarge]
  · change cl < temp
    dsimp [cl]
    linarith only [hlo, hloTemp]
  · dsimp [cu]; linarith only [hhiOne]
  · dsimp [cu]; linarith only [hhiOne]
  · dsimp [cu]; linarith only [hhiSmall]
  · dsimp [cu]; linarith only [hhiLarge]
  · change scalar < cu
    dsimp [cu]
    linarith only [hhiScalar]

end OAI.SKFluctuations.LaplaceWindowFormalization
