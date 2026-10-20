module

public import ConcreteWallCostPowers

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy PositiveLaplaceAssembly
open scoped Topology NNReal

structure ConcreteHighWallGeometry (m : ℝ) (n : ℕ) : Prop where
  positive_size : 0 < n
  size_gt_one : 1 < (n:ℝ)
  logarithm : 1 ≤ Real.log (n:ℝ)
  radius_le_one : wallHighD m n ≤ 1
  mass_mem : wallHighMass m n ∈ Ioc (0:ℝ) (1/2)
  slack : 2 ≤ (n:ℝ)^(m/10000)
  small_mass : comparisonSmallMass (n:ℝ) (wallHighError m n) ≤ wallHighD m n
  strength_margin : (wallHighD m n)^2 ≤ upperInitialEpsilon m n

theorem concreteHighWallGeometry_eventually {m : ℝ}
    (hm : 0 < m) (hmmax : m < 1/300) :
    ∀ᶠ n : ℕ in atTop, ConcreteHighWallGeometry m n := by
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  filter_upwards [wallHighParameters_eventually hm hmmax,hlog,eventually_gt_atTop (1:ℕ)]
    with n hp hlogn hn
  exact ⟨by omega,by exact_mod_cast hn,hlogn,hp.2.1,hp.2.2.1,hp.2.2.2.1,
    hp.2.2.2.2.1,hp.2.2.2.2.2⟩

def highWallComparisonError (m : ℝ) (n : ℕ) : ℝ :=
  (n:ℝ)^(20*(m/10000))*wallHighError m n

def concreteHighWallPhysicalInputs (T C m : ℝ) (n : ℕ)
    (hp : ConcreteHighWallGeometry m n) (epsilon : ℝ) : Prop :=
  let N : ℝ := n
  let s := wallHighMass m n
  let d := wallHighD m n
  let E := wallHighError m n
  let rmin := concreteWallRadius N (m/10000) E d s
  let k := concreteWallFloor N (m/10000) E
  let M := concreteWallCap N (m/10000) E d
  let hN : 0 < N := Nat.cast_pos.mpr hp.positive_size
  let hE := wallHighError_pos m hp.positive_size
  let hd := wallHighD_pos m hp.positive_size
  let hrBounds := concreteWallRadius_bounds hN hE hd hp.radius_le_one hp.mass_mem.1.le
    hp.slack hp.small_mass
  let hr : rmin ≤ 1 := hrBounds.2.2.trans (by norm_num : (1/2:ℝ) ≤ 1)
  let hs1 : s ≤ 1 := hp.mass_mem.2.trans (by norm_num : (1/2:ℝ) ≤ 1)
  let hc := comparisonFloor_pos (δ := m/10000) hN (concreteWallSmallMass_pos hN hE)
    (by norm_num : (0:ℝ) ≤ 1)
  let hk := comparisonFloor_continuousOn (δ := m/10000) hN
    (concreteWallSmallMass_pos hN hE) hrBounds.1.le
  let hkc := fun r (hr : r ∈ Icc rmin 1) => comparisonFloor_lower_on (δ := m/10000)
    hN (concreteWallSmallMass_pos hN hE) hrBounds.1.le hr
  let hm := comparisonCap_monotoneOn (δ := m/10000) hN
    (concreteWallSmallMass_pos hN hE).le (concreteWallConstraintLength_pos hN hE hd) hE hd.le
  let hM := comparisonCap_nonneg (δ := m/10000) hN
    (concreteWallSmallMass_pos hN hE).le (concreteWallConstraintLength_pos hN hE hd)
    hE hd.le zero_le_one
  let g := laplaceComparisonStrength d (d^2)
  let hg := (laplaceComparisonStrength_contDiff d (d^2)).continuous
  wallMinimumValue hr hs1 hc hk hkc hm hM g hg T epsilon (N^(-(10:ℝ))) d n 0 0 ≤
      physicalShellPressure n T s epsilon+highWallComparisonError m n ∧
    ∀ θ ∈ Ioo (N^(-(10:ℝ))) 1, ∀ α : inverseIntegralConstraints rmin s k M,
      wallObjective hr hs1 hc hk hkc hm hM g hg T epsilon θ (N^(-(10:ℝ))) d n 0 α=
        wallMinimumValue hr hs1 hc hk hkc hm hM g hg T epsilon (N^(-(10:ℝ))) d n 0 θ →
      ∀ u ∈ Ioo (0:ℝ) s, orderedPathS n
        (fun v => (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T epsilon θ α v).toNNReal)
        (fun v => (wallChangedField hr hs1 hc hk hkc hm hM g hg T epsilon θ
          (N^(-(10:ℝ))) d α v).toNNReal) u < wallMeanScale C d epsilon

theorem concreteHighWall_step_of_physical_inputs {T C m : ℝ} (hC : 0 ≤ C)
    (n : ℕ) (hp : ConcreteHighWallGeometry m n) {epsilon : ℝ}
    (hepsilon : epsilon ∈ Ioo (0:ℝ) T) (heps0 : upperInitialEpsilon m n ≤ epsilon)
    (hinput : concreteHighWallPhysicalInputs T C m n hp epsilon) :
    physicalShellPressure n T (wallHighMass m n) (wallStep T epsilon)-
      physicalShellPressure n T (wallHighMass m n) epsilon ≤
        highWallComparisonError m n+concreteHighWallPhysicalCost T C m n epsilon := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.positive_size.ne'
  let : Nonempty (FeatureIndex (n+1)) := ⟨Sum.inl ⟨0,by omega⟩⟩
  let dim := Fintype.card (FeatureIndex (n+1))-1
  have hcard : dim+1=Fintype.card (FeatureIndex (n+1)) :=
    Nat.sub_add_cancel Fintype.card_pos
  let e : Fin (dim+1) ≃ FeatureIndex (n+1) :=
    (finCongr hcard).trans (Fintype.equivFin _).symm
  have hN : 0 < ((n+1:ℕ):ℝ) := by positivity
  have hcut : 0 < ((n+1:ℕ):ℝ)^(-(10:ℝ)) := Real.rpow_pos_of_pos hN _
  have hcut1 : ((n+1:ℕ):ℝ)^(-(10:ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hp.size_gt_one.le (by norm_num)
  have hA : 0 ≤ wallMeanScale C (wallHighD m (n+1)) epsilon := by
    unfold wallMeanScale
    exact div_nonneg (mul_nonneg hC (pow_nonneg (wallHighD_pos m hp.positive_size).le 3))
      hepsilon.1.le
  have hs := concreteWallPressure_step_of_actual_mean
    (highError := highWallComparisonError m (n+1)) n dim e hp.size_gt_one hp.logarithm
    (wallHighError_pos m hp.positive_size) (wallHighD_pos m hp.positive_size)
    hp.radius_le_one hp.mass_mem hp.slack hp.small_mass hepsilon
    (hp.strength_margin.trans heps0) hcut hcut1 hA
  dsimp only [concreteHighWallPhysicalInputs] at hinput
  have hh := hs hinput.1 hinput.2
  simpa only [concreteHighWallPhysicalCost,add_assoc] using hh

theorem highWallComparisonError_le_ledger {m : ℝ} (hm : 0 ≤ m)
    {n : ℕ} (hn : 1 ≤ n) : highWallComparisonError m n ≤ upperWallStepLedger m n := by
  have hnpos : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have heq : highWallComparisonError m n=
      (n:ℝ)^(-(5:ℝ)/6+25*m+20*(m/10000)) := by
    unfold highWallComparisonError
    rw [wallHighError_eq m (by omega),← Real.rpow_add hnpos]
    congr 1
    ring
  rw [heq]
  have hp := Real.rpow_le_rpow_of_exponent_le hnR
    (show -(5:ℝ)/6+25*m+20*(m/10000) ≤ -(5:ℝ)/6+27*m+20*(m/10000) by linarith)
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hnR
  have hother : 0 ≤ (n:ℝ)^(-(5:ℝ)/6+65*m+m/10000)*(Real.log (n:ℝ))^3+
      (n:ℝ)^(-(10:ℝ)) := by positivity
  unfold upperWallStepLedger
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
