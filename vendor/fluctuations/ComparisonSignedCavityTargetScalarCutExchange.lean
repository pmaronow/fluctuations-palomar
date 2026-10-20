module

public import ComparisonSignedCavityScalarFourSplitLocality
public import ComparisonSignedCavityActualOriginalGPairingTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 14000000

theorem native_full_scalar_moment_cut_difference
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (r : ℕ) (hT : T.leaves ≤ r)
    (U V : ℕ) (hU : 0 < U) (hUV : U ≤ V)
    (K : ℕ→ℝ) (hKm : Monotone K) (hK0 : ∀j,0 ≤ K j) (es : List T.Slot) :
    |fullScalarCutMoment T U K es-fullScalarCutMoment T V K es| ≤
      ClockTree.errorJetVariation r 0 0*((r:ℝ)+1)*K (V-1) := by
  have hV : 0 < V:=hU.trans_le hUV
  exact native_scalar_disorder_clock_difference T.cavityRight ho r
    (by rw [native_scalar_cavity_right_leaves];exact hT)
    (relocatedClock V 0 K) (relocatedClock U 0 K)
    (relocatedClock_monotone V (by norm_num) hKm hK0)
    (relocatedClock_monotone U (by norm_num) hKm hK0)
    (by simp only [relocatedClock,hV,ite_true,zero_mul])
    (by simp only [relocatedClock,hU,ite_true,zero_mul])
    (fun σ=>T.cavityRight.slotProduct spinValue σ (es.map T.cavityRightSlot))
    (fun σ=>(native_scalar_slot_product_abs_one _ σ _).le)
    (K (V-1)) (hK0 _) (native_relocated_clock_cut_difference U V hUV K hKm hK0)

theorem native_full_scalar_connected_four_cut_difference
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (r : ℕ) (hT : T.leaves ≤ r)
    (U V : ℕ) (hU : 0 < U) (hUV : U ≤ V)
    (K : ℕ→ℝ) (hKm : Monotone K) (hK0 : ∀j,0 ≤ K j) (a c e f : T.Slot) :
    |fullScalarCutConnected4 T U K a c e f-fullScalarCutConnected4 T V K a c e f| ≤
      3*(ClockTree.errorJetVariation r 0 0*((r:ℝ)+1))*K (V-1) := by
  let D:=ClockTree.errorJetVariation r 0 0*((r:ℝ)+1)*K (V-1)
  have H4:=native_full_scalar_moment_cut_difference T ho r hT U V hU hUV K hKm hK0 [a,c,e,f]
  have Hac:=native_full_scalar_moment_cut_difference T ho r hT U V hU hUV K hKm hK0 [a,c]
  have Hef:=native_full_scalar_moment_cut_difference T ho r hT U V hU hUV K hKm hK0 [e,f]
  change |fullScalarCutGamma T U K a c-fullScalarCutGamma T V K a c| ≤ D at Hac
  change |fullScalarCutGamma T U K e f-fullScalarCutGamma T V K e f| ≤ D at Hef
  have Hefu:=native_full_scalar_cut_moment_abs_le_one T ho U K [e,f]
  have Hacv:=native_full_scalar_cut_moment_abs_le_one T ho V K [a,c]
  change |fullScalarCutGamma T U K e f| ≤ 1 at Hefu
  change |fullScalarCutGamma T V K a c| ≤ 1 at Hacv
  have hD : 0 ≤ D:=by
    dsimp only [D]
    exact mul_nonneg (mul_nonneg (ClockTree.errorJetVariation_nonneg r 0 0) (by positivity)) (hK0 _)
  have H1:=(mul_le_mul Hac Hefu (abs_nonneg _) hD)
  have H2:=(mul_le_mul Hacv Hef (abs_nonneg _) zero_le_one)
  rw [←abs_mul,mul_one] at H1
  rw [←abs_mul,one_mul] at H2
  have Hprod : |fullScalarCutGamma T U K a c*fullScalarCutGamma T U K e f-
      fullScalarCutGamma T V K a c*fullScalarCutGamma T V K e f| ≤ 2*D := by
    have Hidentity : fullScalarCutGamma T U K a c*fullScalarCutGamma T U K e f-
        fullScalarCutGamma T V K a c*fullScalarCutGamma T V K e f=
        (fullScalarCutGamma T U K a c-fullScalarCutGamma T V K a c)*fullScalarCutGamma T U K e f+
        fullScalarCutGamma T V K a c*(fullScalarCutGamma T U K e f-fullScalarCutGamma T V K e f) := by ring
    rw [Hidentity]
    exact (abs_add_le _ _).trans (by linarith)
  have Hidentity : fullScalarCutConnected4 T U K a c e f-fullScalarCutConnected4 T V K a c e f=
      (fullScalarCutMoment T U K [a,c,e,f]-fullScalarCutMoment T V K [a,c,e,f])-
      (fullScalarCutGamma T U K a c*fullScalarCutGamma T U K e f-
        fullScalarCutGamma T V K a c*fullScalarCutGamma T V K e f) := by
    unfold fullScalarCutConnected4
    ring
  rw [Hidentity]
  exact (abs_sub _ _).trans (by change _ ≤ 3*(ClockTree.errorJetVariation r 0 0*((r:ℝ)+1))*K (V-1);dsimp only [D] at Hprod;linarith)

theorem native_original_high_G_atom_cut_difference
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (r : ℕ) (hT : T.leaves ≤ r)
    (U V : ℕ) (hU : 0 < U) (hUV : U ≤ V) (hV : V ≤ as.length)
    (b h K C : ℕ→ℝ) (hKC : ∀j,K j=h j+b j*C j)
    (hKm : Monotone K) (hK0 : ∀j,0 ≤ K j)
    (a c e f : T.Slot) (hef : V ≤ T.splitIndex e f) (σ : T.Assignment) :
    |nativeOriginalHighGAtom T U K b C a c e f σ-
      nativeOriginalHighGAtom T V K b C a c e f σ| ≤
      (3/2:ℝ)*(ClockTree.errorJetVariation r 0 0*((r:ℝ)+1))*K (V-1)*
        |restHighKernel n V b h K (T.splitIndex e f) (T.atSlot σ e).1 (T.atSlot σ f).1| := by
  rw [native_original_high_G_atom_eq_unmasked_rest_kernel T ho U b h K C hKC a c e f (hUV.trans hV) σ,
    native_original_high_G_atom_eq_unmasked_rest_kernel T ho V b h K C hKC a c e f hV σ]
  have Hkernel : restHighKernel n U b h K (T.splitIndex e f) (T.atSlot σ e).1 (T.atSlot σ f).1=
      restHighKernel n V b h K (T.splitIndex e f) (T.atSlot σ e).1 (T.atSlot σ f).1 := by
    simp only [restHighKernel,not_lt.mpr (hUV.trans hef),not_lt.mpr hef,ite_false]
  rw [Hkernel]
  have Hidentity : (1/2:ℝ)*fullScalarCutConnected4 T U K a c e f*
      restHighKernel n V b h K (T.splitIndex e f) (T.atSlot σ e).1 (T.atSlot σ f).1-
      (1/2:ℝ)*fullScalarCutConnected4 T V K a c e f*
      restHighKernel n V b h K (T.splitIndex e f) (T.atSlot σ e).1 (T.atSlot σ f).1=
      (1/2:ℝ)*(fullScalarCutConnected4 T U K a c e f-fullScalarCutConnected4 T V K a c e f)*
      restHighKernel n V b h K (T.splitIndex e f) (T.atSlot σ e).1 (T.atSlot σ f).1 := by ring
  rw [Hidentity,abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  have H:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (native_full_scalar_connected_four_cut_difference T ho r hT U V hU hUV K hKm hK0 a c e f)
      (by norm_num : (0:ℝ) ≤ 1/2))
    (abs_nonneg (restHighKernel n V b h K (T.splitIndex e f) (T.atSlot σ e).1 (T.atSlot σ f).1))
  convert H using 1
  ring

end OAI.SKFluctuations.Cavity
