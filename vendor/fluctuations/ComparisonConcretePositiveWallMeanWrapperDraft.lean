module

public import ComparisonFinalWallQuantifierBridgeDraft
public import ConcreteHighWallInputs

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy PositiveLaplaceAssembly
open scoped Topology NNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def concreteSharpCostAtNumeric
    (T m : ℝ) (n : ℕ) (hp : ActualConcreteHighWallNumeric m n)
    (epsilon : ℝ) (hepsilon : epsilon ∈ Ioo (0 : ℝ) T)
    (heps0 : upperInitialEpsilon m n ≤ epsilon) : Prop :=
  let a := actualConcreteHighWallData T m n hp epsilon 0 hepsilon heps0 (by norm_num)
  wallMinimumValue a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
    T epsilon a.tau a.d n 0 0 ≤
    physicalShellPressure n T a.s epsilon + highWallComparisonError m n

def concretePositiveThetaMeanAtNumeric
    (T C m : ℝ) (n : ℕ) (hp : ActualConcreteHighWallNumeric m n)
    (epsilon : ℝ) (hepsilon : epsilon ∈ Ioo (0 : ℝ) T)
    (heps0 : upperInitialEpsilon m n ≤ epsilon) : Prop :=
  ∀ theta : ℝ, ∀ htheta : theta ∈ Icc (0 : ℝ) 1,
    let a := actualConcreteHighWallData T m n hp epsilon theta hepsilon heps0 htheta
    ∀ alpha : a.Profile,
      (∀ beta : a.Profile, a.objective alpha ≤ a.objective beta) →
      ∀ u ∈ Ioo (0 : ℝ) a.s,
        orderedPathS n (a.bf alpha) (a.hf alpha) u <
          wallMeanScale C a.d epsilon

theorem actual_wall_minimum_of_value_equality
    {n : ℕ} {delta : ℝ} (a : ActualHighWallData n delta)
    (alpha : a.Profile)
    (hvalue : a.objective alpha =
      wallMinimumValue a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM
        a.g a.hg.continuous a.T a.epsilon a.tau a.d n 0 a.theta) :
    ∀ beta : a.Profile, a.objective alpha ≤ a.objective beta := by
  obtain ⟨gamma, hgamma⟩ := a.exists_minimum
  have hvalueGamma :
      wallMinimumValue a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM
        a.g a.hg.continuous a.T a.epsilon a.tau a.d n 0 a.theta =
        a.objective gamma := by
    unfold wallMinimumValue
    change sInf (Set.range a.objective) = a.objective gamma
    apply IsLeast.csInf_eq
    refine ⟨Set.mem_range_self gamma, ?_⟩
    rintro y ⟨beta, rfl⟩
    exact hgamma beta
  intro beta
  rw [hvalue, hvalueGamma]
  exact hgamma beta

theorem concrete_high_wall_physical_inputs_of_sharp_and_uniform_mean
    {T C m : ℝ} {n : ℕ}
    (hpGeometry : ConcreteHighWallGeometry m n)
    (hpNumeric : ActualConcreteHighWallNumeric m n)
    {epsilon : ℝ} (hepsilon : epsilon ∈ Ioo (0 : ℝ) T)
    (heps0 : upperInitialEpsilon m n ≤ epsilon)
    (hcost : concreteSharpCostAtNumeric T m n hpNumeric epsilon hepsilon heps0)
    (hmean : concretePositiveThetaMeanAtNumeric T C m n hpNumeric
      epsilon hepsilon heps0) :
    concreteHighWallPhysicalInputs T C m n hpGeometry epsilon := by
  dsimp only [concreteHighWallPhysicalInputs]
  constructor
  · simpa only [concreteSharpCostAtNumeric,
      ActualHighWallData.g, ActualHighWallData.rmin, ActualHighWallData.k,
      ActualHighWallData.M, concreteWallFloor, concreteWallCap,
      actualConcreteHighWallData, ActualHighWallData.N] using hcost
  · intro theta htheta alpha hvalue u hu
    have hcut : 0 < (n : ℝ)^(-(10 : ℝ)) :=
      Real.rpow_pos_of_pos (Nat.cast_pos.mpr hpGeometry.positive_size) _
    have hthetaClosed : theta ∈ Icc (0 : ℝ) 1 :=
      ⟨hcut.le.trans htheta.1.le, htheta.2.le⟩
    let a := actualConcreteHighWallData T m n hpNumeric epsilon theta
      hepsilon heps0 hthetaClosed
    let alpha' : a.Profile := alpha
    have hvalue' : a.objective alpha' =
        wallMinimumValue a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM
          a.g a.hg.continuous a.T a.epsilon a.tau a.d n 0 a.theta := by
      simpa only [a, alpha', ActualHighWallData.objective,
        ActualHighWallData.g, ActualHighWallData.rmin, ActualHighWallData.k,
        ActualHighWallData.M, concreteWallFloor, concreteWallCap,
        actualConcreteHighWallData, ActualHighWallData.N] using hvalue
    have hminimum := actual_wall_minimum_of_value_equality a alpha' hvalue'
    have hphysical := hmean theta hthetaClosed alpha' hminimum u hu
    simpa only [a, alpha', actualConcreteHighWallData,
      ActualHighWallData.bf, ActualHighWallData.hf,
      ActualHighWallData.b, ActualHighWallData.h, ActualHighWallData.g,
      ActualHighWallData.rmin, ActualHighWallData.k, ActualHighWallData.M,
      concreteWallFloor, concreteWallCap, ActualHighWallData.N] using hphysical

theorem eventually_concrete_high_wall_physical_inputs_of_numeric_fields
    {T C m : ℝ} (hm : 0 < m) (hmmax : m < 1 / 300)
    (hsharp : ∀ᶠ n : ℕ in atTop,
      ∀ hp : ActualConcreteHighWallNumeric m n,
      ∀ epsilon : ℝ, ∀ hepsilon : epsilon ∈ Ioo (0 : ℝ) T,
      ∀ heps0 : upperInitialEpsilon m n ≤ epsilon,
        concreteSharpCostAtNumeric T m n hp epsilon hepsilon heps0)
    (hmean : ∀ᶠ n : ℕ in atTop,
      ∀ hp : ActualConcreteHighWallNumeric m n,
      ∀ epsilon : ℝ, ∀ hepsilon : epsilon ∈ Ioo (0 : ℝ) T,
      ∀ heps0 : upperInitialEpsilon m n ≤ epsilon,
        concretePositiveThetaMeanAtNumeric T C m n hp epsilon
          hepsilon heps0) :
    ∀ᶠ n : ℕ in atTop,
      ∀ hp : ConcreteHighWallGeometry m n,
      ∀ epsilon : ℝ, ∀ hepsilon : epsilon ∈ Ioo (0 : ℝ) T,
      ∀ heps0 : upperInitialEpsilon m n ≤ epsilon,
        concreteHighWallPhysicalInputs T C m n hp epsilon := by
  filter_upwards [actualConcreteHighWallNumeric_eventually hm hmmax,
    hsharp, hmean] with n hpNumeric hnSharp hnMean
  intro hpGeometry epsilon hepsilon heps0
  exact concrete_high_wall_physical_inputs_of_sharp_and_uniform_mean
    hpGeometry hpNumeric hepsilon heps0
    (hnSharp hpNumeric epsilon hepsilon heps0)
    (hnMean hpNumeric epsilon hepsilon heps0)

end OAI.SKFluctuations.LaplaceWindowFormalization
