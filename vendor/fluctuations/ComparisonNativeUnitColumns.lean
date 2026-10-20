module

public import ComparisonFilledMassRadiusBridge
public import ComparisonContactSideTrace
public import ComparisonSelectedUnitSampling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 1800000

theorem sampled_mass_weight_sum {ι : Type} (q : ℝ → ι → ℝ≥0)
    (as : List PositiveMass) (u : ℝ) (C : ℕ → ℝ) :
    (∑i : Fin ((sampleClockSteps q u as).length+1),
      pathMassDifferences (sampleClockSteps q u as) u i*C i.val)=
      massCellSum as u C+(1-partitionEnd u as)*C as.length := by
  induction as generalizing u C with
  | nil =>
    simp only [massCellSum,partitionEnd,List.length_nil,zero_add]
    change (∑i : Fin 1,(1-u)*C i.val)=(1-u)*C 0
    rw [Fin.sum_univ_one]
    rfl
  | cons a as ih =>
    change (∑i : Fin ((sampleClockSteps q a.val as).length+1+1),
      Fin.cons (α:=fun _ : Fin ((sampleClockSteps q a.val as).length+1+1)=>ℝ)
        (a.val-u) (pathMassDifferences (sampleClockSteps q a.val as) a.val) i*C i.val)=_
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,Fin.val_zero,Fin.val_succ]
    rw [ih a.val (fun j=>C (j+1))]
    simp only [massCellSum,partitionEnd,List.length_cons]
    ring

def nativeSelectedColumn {N K : ℕ} (J : Finset (Fin N))
    (unit : Fin N → Fin K) (col : Fin K → ℝ) (i : ℕ) : ℝ :=
  if hi : i<N then if ⟨i,hi⟩∈J then col (unit ⟨i,hi⟩) else 0 else 0

theorem nativeSelectedColumn_atIndex {N K : ℕ} (J : Finset (Fin N))
    (unit : Fin N → Fin K) (col : Fin K → ℝ) (i : Fin N) :
    nativeSelectedColumn J unit col i.val=(if i∈J then col (unit i) else 0) := by
  simp only [nativeSelectedColumn,dite_eq_left i.isLt]

theorem nativeSelectedColumn_nonneg {N K : ℕ} (J : Finset (Fin N))
    (unit : Fin N → Fin K) (col : Fin K → ℝ) (hcol : ∀u,0≤col u) (i : ℕ) :
    0≤nativeSelectedColumn J unit col i := by
  unfold nativeSelectedColumn
  split_ifs <;> first | exact hcol _ | exact le_rfl

theorem radiusCellEnergyDensity_mem_Icc_bound (R : ℝ → ℝ) (hR : Monotone R)
    {u B : ℝ} (as : List PositiveMass) (ho : MassOrdered u as) (C : ℕ → ℝ)
    (hB : 0≤B) (hC : ∀i,C i∈Icc (0:ℝ) B) (r : ℝ) :
    radiusCellEnergyDensity R u as C r∈Icc (0:ℝ) B := by
  induction as generalizing u C with
  | nil => exact ⟨le_rfl,hB⟩
  | cons a as ih =>
    by_cases hr : r∈Ioc (R u) (R a.val)
    · rw [radiusCellEnergyDensity,indicator_of_mem hr,
        radiusCellEnergyDensity_eq_zero_of_le R hR as ho.2.2 _ hr.2,add_zero]
      exact hC 0
    · rw [radiusCellEnergyDensity,indicator_of_notMem hr,zero_add]
      exact ih ho.2.2 _ (fun j=>hC (j+1))

theorem sideSquareColumn_le_two_inv (x : ℕ → ℝ) (K : ℕ) {δ width : ℝ}
    (hstart : x 0=0) (hend : x K=width) (hδ : 0<δ) (hwidth : 2*δ≤width)
    (hx : ∀u : Fin K,x u.val<x (u.val+1)) (u : Fin K) :
    sideSquareColumn x δ width u.val≤2/δ := by
  have hpq : δ≤width-δ := by linarith
  have hmono := WholeUnitSideKernel.unitPoints_monotoneOn x (fun u hu=>(hx ⟨u,hu⟩).le)
  have hleftB : x u.val≤width := by
    rw [←hend]
    exact hmono ⟨by omega,by omega⟩ ⟨by omega,le_rfl⟩ (by omega)
  have hrightA : 0≤x (u.val+1) := by
    rw [←hstart]
    exact hmono ⟨le_rfl,by omega⟩ ⟨by omega,by omega⟩ (by omega)
  have hIL : IntervalIntegrable (fun t=>(WholeUnitSideKernel.left 0 (x u.val) (x (u.val+1)) t)^2)
      volume δ width := by
    apply ContinuousOn.intervalIntegrable (μ:=volume)
    simpa [uIcc_of_le (by linarith : δ≤width),Pi.pow_def] using
      (WholeUnitSideKernel.left_continuousOn (a:=0) (b:=width) hδ (hx u)).pow 2
  have hIR : IntervalIntegrable (fun t=>(WholeUnitSideKernel.right width (x u.val) (x (u.val+1)) t)^2)
      volume 0 (width-δ) := by
    apply ContinuousOn.intervalIntegrable (μ:=volume)
    simpa [uIcc_of_le (by linarith : 0≤width-δ),Pi.pow_def] using
      (WholeUnitSideKernel.right_continuousOn (a:=0) hδ (hx u)).pow 2
  have hL := (intervalIntegral.integral_mono_interval le_rfl hpq
    (by linarith : width-δ≤width) (Eventually.of_forall (fun _=>sq_nonneg _)) hIL).trans
      (by simpa only [zero_add,sub_zero] using
        (WholeUnitSideKernel.left_square_column_le_reciprocal (a:=0) hδ
          (by linarith) (hx u) hleftB))
  have hR := (intervalIntegral.integral_mono_interval hδ.le hpq le_rfl
    (Eventually.of_forall (fun _=>sq_nonneg _)) hIR).trans
      (WholeUnitSideKernel.right_square_column_le_reciprocal (a:=0) hδ
        (by linarith) (hx u) hrightA)
  have hLi : (max δ (x u.val))⁻¹≤δ⁻¹ :=
    inv_anti₀ hδ (le_max_left _ _)
  have hRi : (max δ (width-x (u.val+1)))⁻¹≤δ⁻¹ :=
    inv_anti₀ hδ (le_max_left _ _)
  dsimp only [sideSquareColumn]
  exact (add_le_add (hL.trans hLi) (hR.trans hRi)).trans_eq (by ring)

section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

def comparisonNativeUnitColumnWeight {ι : Type} (q : ℝ → ι → ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    {K : ℕ} (J : Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps q 0 as).length+1) → Fin K) (col : Fin K → ℝ) : ℝ → ℝ :=
  radiusCellEnergyDensity (comparisonSweepQuantile hc hk hkc hm hM α) 0 as
    (nativeSelectedColumn J unit col)

theorem comparisonNativeUnitColumnWeight_measurable {ι : Type}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps q 0 as).length+1) → Fin K) (col : Fin K → ℝ) :
    Measurable (comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as J unit col) :=
  radiusCellEnergyDensity_measurable _ _ _ _

theorem comparisonNativeUnitColumnWeight_side_bound {ι : Type}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps q 0 as).length+1) → Fin K)
    (x : ℕ → ℝ) {δ width : ℝ} (hstart : x 0=0) (hend : x K=width)
    (hδ : 0<δ) (hwidth : 2*δ≤width)
    (hx : ∀u : Fin K,x u.val<x (u.val+1)) (r : ℝ) :
    comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as J unit
      (fun u=>sideSquareColumn x δ width u.val) r∈Icc (0:ℝ) (2/δ) := by
  apply radiusCellEnergyDensity_mem_Icc_bound _
    (comparisonSweepQuantile_monotone hc hk hkc hm hM α) as ho _ (by positivity)
  intro i
  unfold nativeSelectedColumn
  split_ifs
  · exact ⟨sideSquareColumn_nonneg x hwidth _,
      sideSquareColumn_le_two_inv x K hstart hend hδ hwidth hx _⟩
  all_goals exact ⟨le_rfl,by positivity⟩

theorem comparisonNativeUnitColumnWeight_mass {ι : Type}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {K : ℕ} (J : Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps q 0 as).length+1) → Fin K) (col : Fin K → ℝ) :
    (∫r,deriv α.val.val r*comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as J unit col r)=
      ∑u : Fin K,physicalSelectedUnitMass (sampleClockSteps q 0 as) J unit u*col u := by
  rw [comparisonNativeUnitColumnWeight,
    comparison_filled_coefficients_mass_radius_eq hc hk hkc hm hM α
      (show (0:ℝ)∈Icc (0:ℝ) 1 by simp) as ho]
  have hs := sampled_mass_weight_sum q as 0 (nativeSelectedColumn J unit col)
  simp only [he,sub_self,zero_mul,add_zero] at hs
  rw [←hs]
  simp_rw [nativeSelectedColumn_atIndex]
  exact selected_mass_grouping _ _ _ _

theorem comparisonNativeUnitColumnWeight_side_mass_le_log {ι : Type}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {K : ℕ} (J : Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps q 0 as).length+1) → Fin K)
    (x : ℕ → ℝ) {δ width : ℝ} (hstart : x 0=0) (hend : x K=width)
    (hδ : 0<δ) (hwidth : 2*δ≤width)
    (hx : ∀u : Fin K,x u.val<x (u.val+1))
    (hmass : ∀u : Fin K,physicalSelectedUnitMass (sampleClockSteps q 0 as) J unit u=
      x (u.val+1)-x u.val) :
    (∫r,deriv α.val.val r*comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as J unit
      (fun u=>sideSquareColumn x δ width u.val) r)≤2*Real.log (width/δ) := by
  rw [comparisonNativeUnitColumnWeight_mass hc hk hkc hm hM q α as ho he]
  simp_rw [hmass]
  exact sideSquareColumn_mass_sum_le x K hstart hend hδ hwidth hx

end
end OAI.SKFluctuations.LaplaceWindowFormalization
