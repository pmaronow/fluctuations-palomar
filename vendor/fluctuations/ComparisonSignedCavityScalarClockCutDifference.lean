module

public import ComparisonSignedCavityActualTerminalGAtom
public import ComparisonSignedCavityTransientForkCost
public import ComparisonSignedCavityActualGammaHighBound
public import SKFluctuationsOAI.Probability.SKFluctuations.ClockZeroRefinement

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

theorem native_scalar_constant_edge_budget (a : ℝ) (as : List PositiveMass) (C : ℝ) :
    ClockTree.edgeBudget a as (fun _=>C)=(1-a)*C := by
  induction as generalizing a with
  | nil=>rfl
  | cons b bs ih=>simp only [ClockTree.edgeBudget,ih];ring

theorem native_scalar_disorder_clock_difference
    {as : List PositiveMass} (T : ClockTree Bool as) (ho : MassOrdered 0 as)
    (r : ℕ) (hT : T.leaves ≤ r) (q₀ q₁ : ℕ→ℝ)
    (hq₀ : Monotone q₀) (hq₁ : Monotone q₁) (hz₀ : q₀ 0=0) (hz₁ : q₁ 0=0)
    (P : T.Assignment→ℝ) (hP : ∀σ,|P σ| ≤ 1)
    (D : ℝ) (hD : 0 ≤ D) (hdir : ∀j,|q₁ j-q₀ j| ≤ D) :
    |T.disorderExpect (fun _=>(1/2:ℝ)) scalarFeature 0 (fun j _=>q₁ j) P 0-
      T.disorderExpect (fun _=>(1/2:ℝ)) scalarFeature 0 (fun j _=>q₀ j) P 0| ≤
      ClockTree.errorJetVariation r 0 0*((r:ℝ)+1)*D := by
  have hp (u : ℝ) (hu : u∈Ioo (0:ℝ) 1) (_i : Fin 1) :
      Monotone (fun j=>q₀ j+u*(q₁ j-q₀ j)) := by
    intro j k hjk
    have H₀:=mul_le_mul_of_nonneg_left (hq₀ hjk) (sub_nonneg.mpr hu.2.le)
    have H₁:=mul_le_mul_of_nonneg_left (hq₁ hjk) hu.1.le
    nlinarith only [H₀,H₁]
  have hr (_u : ℝ) (_hu : _u∈Ioo (0:ℝ) 1) (_i : Fin 1) :
      (0:Fin 1→ℝ) _i ≤ q₀ 0+_u*(q₁ 0-q₀ 0) := by simp only [hz₀,hz₁,sub_self,mul_zero,add_zero,Pi.zero_apply,le_refl]
  have hE (j : ℕ) (σ τ : Bool) :
      |ReplicaTree.coordinateProfile scalarFeature (fun j (_:Fin 1)=>q₁ j-q₀ j) j σ τ| ≤ D := by
    simpa only [ReplicaTree.coordinateProfile,Fin.sum_univ_one,scalarFeature_apply_spin,
      abs_mul,abs_spinValue,Pi.single_eq_same,abs_one,one_mul,mul_one] using hdir j
  have H:=ClockTree.disorderProfileJets_l1_comparison
    (by intro σ;norm_num : ∀σ : Bool,(0:ℝ)<1/2) scalarFeature ho [] T hT P
    (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 1) hP (by simp)
    (0:Fin 1→ℝ) (fun j _=>q₀ j) (fun j _=>q₁ j-q₀ j) hp hr
    (fun _=>hD) hE (0:Fin 1→ℝ) (s:=1) (t:=0) (by norm_num) (by norm_num)
  have HF:=T.native_forkCost_le_pair_bound (fun _=>D) D (by intro s t _;rfl)
  have HT : (T.leaves:ℝ) ≤ r:=by exact_mod_cast hT
  have HA : T.forkCost (fun _=>D)+ClockTree.edgeBudget 0 as (fun _=>D)+D ≤ ((r:ℝ)+1)*D := by
    rw [native_scalar_constant_edge_budget]
    nlinarith only [HF,mul_le_mul_of_nonneg_right HT hD]
  have HV:=ClockTree.errorJetVariation_nonneg r 0 0
  have HH:=mul_le_mul_of_nonneg_left HA HV
  simp only [ClockTree.disorderProfileJets,List.length_nil,pow_zero,mul_one,
    one_mul,zero_mul,add_zero,sub_zero,abs_one] at H
  have HE (j : ℕ) : q₀ j+(q₁ j-q₀ j)=q₁ j:=by ring
  simp only [HE] at H
  exact H.trans (by convert HH using 1;ring)

end OAI.SKFluctuations.Cavity
