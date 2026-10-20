module

public import ComparisonSignedCavityOriginalGErrorPairProfile
public import ComparisonSignedCavityTargetScalarCutExchange

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set Classical
open scoped NNReal
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem native_original_G_atom_zero_of_low_error_pair
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (U : ℕ) (K b C : ℕ→ℝ) (a c e f : T.Slot)
    (hef : T.splitIndex e f<U) (σ : T.Assignment) :
    nativeOriginalHighGAtom T U K b C a c e f σ=0 := by
  unfold nativeOriginalHighGAtom
  split_ifs with H
  · have HH:=T.splitIndex_cut_trans U e a f
      (by simpa only [T.splitIndex_symm] using H.2.1) H.2.2.1
    omega
  · rfl

theorem native_original_G_atom_zero_of_diagonal_error_pair
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (U : ℕ) (K b C : ℕ→ℝ) (a c e : T.Slot) (σ : T.Assignment) :
    nativeOriginalHighGAtom T U K b C a c e e σ=0 := by
  simp only [nativeOriginalHighGAtom,ne_eq,not_true_eq_false,and_false,ite_false]

theorem native_original_G_pair_cut_difference_abs_le_profile
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (r : ℕ) (hT : T.leaves≤r)
    (U V : ℕ) (hU0 : 0<U) (hUV : U≤V) (hV : V≤as.length)
    (b h K C : ℕ→ℝ) (hKC : ∀j,K j=h j+b j*C j)
    (hKm : Monotone K) (hK0 : ∀j,0≤K j)
    (q : ℕ→FullCoordinate n→ℝ) (P : T.Assignment→ℝ) (a c e f : T.Slot)
    (A : ℝ) (hA : 0≤A)
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ=>(P σ)^2) 0≤A^2) :
    let coef:=(3/2:ℝ)*(errorJetVariation r 0 0*((r:ℝ)+1))*K (V-1)
    abs (T.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ=>P σ*(nativeOriginalHighGAtom T U K b C a c e f σ-
        nativeOriginalHighGAtom T V K b C a c e f σ)) 0) ≤
      A*(if T.splitIndex e f<U then 0 else
        if T.splitIndex e f<V then nativeWholeLawErrorRadius n as q (cutTSlope n U 0 b h K) (T.splitIndex e f)
        else coef*nativeWholeLawErrorRadius n as q (cutTSlope n V 0 b h K) (T.splitIndex e f)) := by
  dsimp only
  let coef:=(3/2:ℝ)*(errorJetVariation r 0 0*((r:ℝ)+1))*K (V-1)
  have hc : 0≤coef:=mul_nonneg (mul_nonneg (by norm_num)
    (mul_nonneg (errorJetVariation_nonneg r 0 0) (by positivity))) (hK0 _)
  by_cases hlow : T.splitIndex e f<U
  · simp only [native_original_G_atom_zero_of_low_error_pair T U K b C a c e f hlow,
      native_original_G_atom_zero_of_low_error_pair T V K b C a c e f (hlow.trans_le hUV),
      sub_self,mul_zero,ClockTree.disorderExpect,Finset.sum_const_zero,abs_zero,hlow,ite_true,le_refl]
  rw [ite_eq_right hlow]
  by_cases hef : e=f
  · subst f
    simp only [native_original_G_atom_zero_of_diagonal_error_pair,sub_self,mul_zero,
      ClockTree.disorderExpect,Finset.sum_const_zero,abs_zero]
    apply mul_nonneg hA
    split_ifs
    · exact Real.sqrt_nonneg _
    · exact mul_nonneg hc (Real.sqrt_nonneg _)
  by_cases hmid : T.splitIndex e f<V
  · rw [ite_eq_left hmid]
    simp only [native_original_G_atom_zero_of_low_error_pair T V K b C a c e f hmid,sub_zero]
    have H:=native_original_G_pair_expect_abs_le_radius T ho U (hUV.trans hV) b h K C hKC q
      P a c e f A hA hP
    rw [ite_eq_left (show U≤T.splitIndex e f ∧ e≠f from ⟨not_lt.mp hlow,hef⟩)] at H
    exact H
  rw [ite_eq_right hmid]
  let Q:=fun σ=>restHighKernel n V b h K (T.splitIndex e f) (T.atSlot σ e).1 (T.atSlot σ f).1
  let R:=nativeWholeLawErrorRadius n as q (cutTSlope n V 0 b h K) (T.splitIndex e f)
  let κ:=(1/2:ℝ)*(fullScalarCutConnected4 T U K a c e f-fullScalarCutConnected4 T V K a c e f)
  have hR : 0≤R:=Real.sqrt_nonneg _
  have Hκ : abs κ≤coef:=by
    have H:=mul_le_mul_of_nonneg_left
      (native_full_scalar_connected_four_cut_difference T ho r hT U V hU0 hUV K hKm hK0 a c e f)
      (by norm_num : (0:ℝ)≤1/2)
    dsimp only [κ,coef]
    rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
    convert H using 1
    ring
  have HQ : T.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ=>(Q σ)^2) 0=R^2:=by
    dsimp only [Q]
    simp_rw [native_rest_high_kernel_square_eq_profile]
    rw [T.disorderExpect_pairAtSlot_actual (fullWeight_pos n) (fullFeature n) ho 0 q 0 e f hef
      (fun σ τ=>(ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n V 0 b h K)
        (T.splitIndex e f) σ τ)^2)]
    exact nativeWholeLawErrorSecond_eq_radius_sq n ho q (cutTSlope n V 0 b h K) _
  have HC:=T.disorderExpect_mul_sq_le (fullWeight_pos n) (fullFeature n) ho 0 q P Q 0
  rw [HQ] at HC
  have Hprod : abs (T.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ=>P σ*Q σ) 0)≤A*R:=by
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hA hR)).mp
    rw [sq_abs,mul_pow]
    exact HC.trans (mul_le_mul_of_nonneg_right hP (sq_nonneg R))
  have HT : (fun σ=>P σ*(nativeOriginalHighGAtom T U K b C a c e f σ-
      nativeOriginalHighGAtom T V K b C a c e f σ))=(fun σ=>κ*(P σ*Q σ)):=by
    funext σ
    rw [native_original_high_G_atom_eq_unmasked_rest_kernel T ho U b h K C hKC a c e f (hUV.trans hV),
      native_original_high_G_atom_eq_unmasked_rest_kernel T ho V b h K C hKC a c e f hV]
    have HQcut : restHighKernel n U b h K (T.splitIndex e f) (T.atSlot σ e).1 (T.atSlot σ f).1=
        restHighKernel n V b h K (T.splitIndex e f) (T.atSlot σ e).1 (T.atSlot σ f).1:=by
      simp only [restHighKernel,hlow,hmid,ite_false]
    rw [HQcut]
    dsimp only [κ,Q]
    ring
  rw [HT,T.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) ho,abs_mul]
  change _≤A*(coef*R)
  exact (mul_le_mul Hκ Hprod (abs_nonneg _) hc).trans_eq (by ring)

end OAI.SKFluctuations.Cavity
