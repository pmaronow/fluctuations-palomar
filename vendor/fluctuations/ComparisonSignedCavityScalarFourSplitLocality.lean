module

public import ComparisonSignedCavityScalarClockCutDifference
public import ComparisonSignedCavityActualSixConnectedClassification

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

theorem native_scalar_cavity_right_leaves {S B : Type*} {as : List PositiveMass}
    (T : ClockTree (S×B) as) : T.cavityRight.leaves=T.leaves := by
  induction T with
  | leaf=>rfl
  | step b T ih=>exact ih
  | fork T V ihT ihV=>simp only [ClockTree.cavityRight,ClockTree.leaves,ihT,ihV]

theorem native_relocated_clock_cut_difference (U V : ℕ) (hUV : U ≤ V)
    (K : ℕ→ℝ) (hKm : Monotone K) (hK0 : ∀j,0 ≤ K j) :
    ∀j,|relocatedClock U 0 K j-relocatedClock V 0 K j| ≤ K (V-1) := by
  intro j
  by_cases hju : j < U
  · have hjv : j < V:=lt_of_lt_of_le hju hUV
    simp only [relocatedClock,hju,hjv,ite_true,zero_mul,sub_self,abs_zero]
    exact hK0 _
  · by_cases hjv : j < V
    · simp only [relocatedClock,hju,hjv,ite_false,ite_true,zero_mul,sub_zero,abs_of_nonneg (hK0 j)]
      exact hKm (by omega)
    · simp only [relocatedClock,hju,hjv,ite_false,sub_self,abs_zero]
      exact hK0 _

theorem native_full_scalar_four_deeper_split_abs_le_clock
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (r : ℕ) (hT : T.leaves ≤ r)
    (U : ℕ) (hU0 : 0 < U) (K : ℕ→ℝ)
    (hKm : Monotone K) (hK0 : ∀j,0 ≤ K j)
    (a c e f : T.Slot) (hac : a ≠ c) (hUac : U ≤ T.splitIndex a c)
    (hdeep : T.splitIndex a c < T.splitIndex e f) :
    |fullScalarCutConnected4 T U K a c e f| ≤
      (ClockTree.errorJetVariation r 0 0*((r:ℝ)+1)+1)*K (T.splitIndex a c) := by
  let v:=T.splitIndex a c
  let V:=v+1
  have hV : V ≤ as.length:=(by omega : V ≤ T.splitIndex e f).trans (T.splitIndex_le_clockLength e f)
  have hUV : U ≤ V:=by dsimp only [V,v];omega
  have hV0 : 0 < V:=by dsimp only [V];omega
  have Hclock:=native_relocated_clock_cut_difference U V hUV K hKm hK0
  have HVminus : V-1=v:=by dsimp only [V];omega
  rw [HVminus] at Hclock
  have H:=native_scalar_disorder_clock_difference T.cavityRight ho r
    (by rw [native_scalar_cavity_right_leaves];exact hT)
    (relocatedClock V 0 K) (relocatedClock U 0 K)
    (relocatedClock_monotone V (by norm_num) hKm hK0)
    (relocatedClock_monotone U (by norm_num) hKm hK0)
    (by simp only [relocatedClock,hV0,ite_true,zero_mul])
    (by simp only [relocatedClock,hU0,ite_true,zero_mul])
    (fun σ=>T.cavityRight.slotProduct spinValue σ ([a,c,e,f].map T.cavityRightSlot))
    (fun σ=>(native_scalar_slot_product_abs_one _ σ _).le)
    (K v) (hK0 v) Hclock
  change |fullScalarCutMoment T U K [a,c,e,f]-fullScalarCutMoment T V K [a,c,e,f]| ≤ _ at H
  have Hzero:=fullScalarCutConnected4_cross_target_zero T ho V K a c e f hV
    (by dsimp only [V,v];omega) (by dsimp only [V,v];omega)
  have HGzero:=fullScalarCutGamma_cross_zero T ho V K a c hV (by dsimp only [V,v];omega)
  unfold fullScalarCutConnected4 at Hzero
  rw [HGzero,zero_mul,sub_zero] at Hzero
  rw [Hzero,sub_zero] at H
  have Hac:=native_full_scalar_gamma_abs_le_clock n T ho U hU0 K hKm hK0 a c hac
    (C:=1) (v:=K v) (by dsimp only [v];simp only [one_mul,le_refl])
  simp only [one_mul] at Hac
  have Hef:=native_full_scalar_cut_moment_abs_le_one T ho U K [e,f]
  change |fullScalarCutGamma T U K e f| ≤ 1 at Hef
  have Hprod:=mul_le_mul Hac Hef (abs_nonneg _) (hK0 v)
  rw [←abs_mul,mul_one] at Hprod
  unfold fullScalarCutConnected4
  apply (abs_sub _ _).trans
  apply (add_le_add H Hprod).trans_eq
  dsimp only [v]
  ring

end OAI.SKFluctuations.Cavity
