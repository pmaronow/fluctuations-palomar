module

public import ConcreteComparisonStrength
public import WallPhysicalIntegratedCost

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

def concreteWallFloor (N δ E : ℝ) : ℝ → ℝ :=
  comparisonFloor N δ (comparisonSmallMass N E)

def concreteWallCap (N δ E d : ℝ) : ℝ → ℝ :=
  comparisonCap N δ (comparisonSmallMass N E) (comparisonConstraintLength N E d) E d

def concreteWallRadius (N δ E d s : ℝ) : ℝ :=
  comparisonSmallMass N E/(2*concreteWallCap N δ E d s)

theorem concreteWallSmallMass_pos {N E : ℝ} (hN:0<N) (hE:0<E) :
    0<comparisonSmallMass N E := by unfold comparisonSmallMass; positivity

theorem concreteWallConstraintLength_pos {N E d : ℝ} (hN:0<N) (hE:0<E) (hd:0<d) :
    0<comparisonConstraintLength N E d := by
  have hu := concreteWallSmallMass_pos hN hE
  have hsqrt : 0<Real.sqrt N := Real.sqrt_pos.2 hN
  unfold comparisonConstraintLength comparisonLowerScale
  exact lt_min hu (by positivity)

theorem concreteWallConstraintLength_le_smallMass (N E d : ℝ) :
    comparisonConstraintLength N E d ≤ comparisonSmallMass N E := min_le_left _ _

theorem concreteWallCap_ge {N δ E d s : ℝ}
    (hN:0<N) (hE:0<E) (hd:0<d) (hs:0 ≤ s) :
    N^δ ≤ concreteWallCap N δ E d s :=
  comparisonCap_ge hN (concreteWallSmallMass_pos hN hE)
    (concreteWallConstraintLength_pos hN hE hd) (min_le_left _ _) hE hd.le hs

theorem concreteWallCap_continuous (N δ E d:ℝ) : Continuous (concreteWallCap N δ E d) :=
  comparisonCap_continuous _ _ _ _ _ _

theorem concreteWallRadius_bounds {N δ E d s : ℝ}
    (hN:0<N) (hE:0<E) (hd:0<d) (hd1:d ≤ 1) (hs:0 ≤ s)
    (hq:2 ≤ N^δ) (hu:comparisonSmallMass N E ≤ d) :
    0<concreteWallRadius N δ E d s ∧
      concreteWallRadius N δ E d s ≤ d/4 ∧
      concreteWallRadius N δ E d s ≤ 1/2 := by
  have hU := concreteWallSmallMass_pos hN hE
  have hcap : 2 ≤ concreteWallCap N δ E d s := hq.trans (concreteWallCap_ge hN hE hd hs)
  have hr : 0<concreteWallRadius N δ E d s := by unfold concreteWallRadius; positivity
  have hsmall : concreteWallRadius N δ E d s ≤ comparisonSmallMass N E/4 := by
    unfold concreteWallRadius
    apply div_le_div_of_nonneg_left hU.le (by norm_num)
    linarith
  have hrd : concreteWallRadius N δ E d s ≤ d/4 := hsmall.trans (div_le_div_of_nonneg_right hu (by norm_num))
  exact ⟨hr,hrd,by linarith⟩

theorem concreteWallConstraints_nonempty {N δ E d s : ℝ}
    (hN:0<N) (hE:0<E) (hd:0<d) (hd1:d ≤ 1) (hs:s∈Icc (0:ℝ) (1/2))
    (hq:2 ≤ N^δ) (hu:comparisonSmallMass N E ≤ d) :
    (inverseIntegralConstraints (concreteWallRadius N δ E d s) s
      (concreteWallFloor N δ E) (concreteWallCap N δ E d)).Nonempty := by
  have hr := concreteWallRadius_bounds hN hE hd hd1 hs.1 hq hu
  have hk := comparisonFloor_continuousOn (δ:=δ) hN (concreteWallSmallMass_pos hN hE) hr.1.le
  have hMc := concreteWallCap_continuous N δ E d
  have hm := comparisonCap_monotoneOn (δ:=δ) hN (concreteWallSmallMass_pos hN hE).le
    (concreteWallConstraintLength_pos hN hE hd) hE hd.le
  have hM := comparisonCap_nonneg (δ:=δ) hN (concreteWallSmallMass_pos hN hE).le
    (concreteWallConstraintLength_pos hN hE hd) hE hd.le zero_le_one
  have hne := comparisonConstraints_nonempty hN (concreteWallSmallMass_pos hN hE)
    (concreteWallConstraintLength_pos hN hE hd) (min_le_left _ _) hE hd.le hq
    ⟨hr.1.le,hr.2.2⟩ hs
  change (inverseDifferentialConstraints (concreteWallRadius N δ E d s) s
    (concreteWallFloor N δ E) (concreteWallCap N δ E d)).Nonempty at hne
  rw [inverseDifferentialConstraints_eq (concreteWallRadius N δ E d s) s
    (by linarith [hr.2.2]) (concreteWallFloor N δ E) (concreteWallCap N δ E d)
    hk hMc hm hM] at hne
  exact hne

theorem concreteWallStrength_initial {N δ E d s : ℝ}
    (hN:0<N) (hE:0<E) (hd:0<d) (hd1:d ≤ 1) (hs:0 ≤ s)
    (hq:2 ≤ N^δ) (hu:comparisonSmallMass N E ≤ d) :
    laplaceComparisonStrength d (d^2) (concreteWallRadius N δ E d s)=d^2 := by
  have hr := concreteWallRadius_bounds hN hE hd hd1 hs hq hu
  have hrd : concreteWallRadius N δ E d s/d ≤ 1 := (div_le_one hd).mpr (by linarith [hr.2.1])
  rw [laplaceFinalStrength_eq hd.ne']
  simp [laplaceComparisonShape,hrd]

end OAI.SKFluctuations.LaplaceWindowFormalization
