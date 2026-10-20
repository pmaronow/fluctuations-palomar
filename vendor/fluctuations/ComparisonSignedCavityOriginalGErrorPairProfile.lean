module

public import ComparisonSignedCavityOriginalGWordProfileLedger
public import ComparisonSignedCavityGRestorationProfile
public import ComparisonSignedCavityTransientForkCost

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set Classical
open scoped BigOperators NNReal

theorem native_original_G_pair_expect_abs_le_radius
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (U : ℕ) (hU : U ≤ as.length)
    (b h K C : ℕ→ℝ) (hKC : ∀j,K j=h j+b j*C j)
    (q : ℕ→FullCoordinate n→ℝ) (P : T.Assignment→ℝ) (a c e f : T.Slot)
    (A : ℝ) (hA : 0 ≤ A)
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ=>(P σ)^2) 0 ≤ A^2) :
    abs (T.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ=>P σ*nativeOriginalHighGAtom T U K b C a c e f σ) 0) ≤
      A*(if U ≤ T.splitIndex e f ∧ e≠f then
        nativeWholeLawErrorRadius n as q (cutTSlope n U 0 b h K) (T.splitIndex e f) else 0) := by
  by_cases HS : U ≤ T.splitIndex e f ∧ e≠f
  · rw [ite_eq_left HS]
    let Q:=fun σ=>restHighKernel n U b h K (T.splitIndex e f) (T.atSlot σ e).1 (T.atSlot σ f).1
    let R:=nativeWholeLawErrorRadius n as q (cutTSlope n U 0 b h K) (T.splitIndex e f)
    let κ:=(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f
    have hR : 0 ≤ R:=Real.sqrt_nonneg _
    have Hκ : abs κ ≤ 1:=by
      have H:=native_full_scalar_connected_four_abs_le_two T ho U K a c e f
      dsimp only [κ]
      rw [abs_mul]
      norm_num only [abs_of_nonneg (show (0:ℝ)≤1/2 by norm_num)]
      linarith
    have HQ : T.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ=>(Q σ)^2) 0=R^2:=by
      dsimp only [Q]
      simp_rw [native_rest_high_kernel_square_eq_profile]
      rw [T.disorderExpect_pairAtSlot_actual (fullWeight_pos n) (fullFeature n) ho 0 q 0 e f HS.2
        (fun σ τ=>(ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K)
          (T.splitIndex e f) σ τ)^2)]
      exact nativeWholeLawErrorSecond_eq_radius_sq n ho q (cutTSlope n U 0 b h K) _
    have HC:=T.disorderExpect_mul_sq_le (fullWeight_pos n) (fullFeature n) ho 0 q P Q 0
    rw [HQ] at HC
    have Hprod : abs (T.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ=>P σ*Q σ) 0)≤A*R:=by
      apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hA hR)).mp
      rw [sq_abs,mul_pow]
      exact HC.trans (mul_le_mul_of_nonneg_right hP (sq_nonneg R))
    have HT : (fun σ=>P σ*nativeOriginalHighGAtom T U K b C a c e f σ)=
        (fun σ=>κ*(P σ*Q σ)):=by
      funext σ
      rw [native_original_high_G_atom_eq_unmasked_rest_kernel T ho U b h K C hKC a c e f hU]
      dsimp only [κ,Q]
      ring
    rw [HT,T.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) ho,abs_mul]
    exact (mul_le_mul_of_nonneg_left Hprod (abs_nonneg κ)).trans
      (mul_le_of_le_one_left (mul_nonneg hA hR) Hκ)
  · rw [ite_eq_right HS,mul_zero]
    have Hzero (σ : T.Assignment) : nativeOriginalHighGAtom T U K b C a c e f σ=0:=by
      unfold nativeOriginalHighGAtom
      split_ifs with HH
      · exact False.elim (HS ⟨T.splitIndex_cut_trans U e a f
          (by simpa only [T.splitIndex_symm] using HH.2.1) HH.2.2.1,HH.2.2.2⟩)
      · rfl
    simp only [Hzero,mul_zero,ClockTree.disorderExpect,Finset.sum_const_zero,abs_zero,le_refl]

theorem native_original_longitudinal_abs_le_high_profile
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (U : ℕ) (hU : U ≤ as.length)
    (b h K C : ℕ→ℝ) (hKC : ∀j,K j=h j+b j*C j)
    (q : ℕ→FullCoordinate n→ℝ) (P : T.Assignment→ℝ) (a : T.Slot)
    (A : ℝ) (hA : 0 ≤ A)
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ=>(P σ)^2) 0 ≤ A^2)
    (r : ℕ) (hr : T.leaves ≤ r) :
    let f:=fun j=>if j<U then 0 else nativeWholeLawErrorRadius n as q (cutTSlope n U 0 b h K) j
    abs (nativeOriginalLongitudinalPairing n 0 q 0 U K b C T P a) ≤
      A*forkVariation r 3*(T.forkCost f+edgeBudget 0 as f) := by
  dsimp only
  let f:=fun j=>if j<U then 0 else nativeWholeLawErrorRadius n as q (cutTSlope n U 0 b h K) j
  have hf j : 0 ≤ f j:=by dsimp only [f];split_ifs <;> first | exact le_rfl | exact Real.sqrt_nonneg _
  let F:=fun (p : MarkedPlacement T) (r : MarkedPlacement p.tree) (z : MarkedPlacement r.tree)=>
    z.tree.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ=>P (p.restrict (r.restrict (z.restrict σ)))*nativeOriginalHighGAtom z.tree U K b C
        (z.embed (r.embed (p.embed a))) (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark σ) 0
  have HE : nativeOriginalLongitudinalPairing n 0 q 0 U K b C T P a=
      ((nativeOriginalGMarkedWords T).map (fun g=>g.coefficient*F g.p g.r g.z)).sum:=by
    rw [nativeOriginalGMarkedWords_weighted_kernel_sum]
    rfl
  have HB (g : NativeOriginalGMarkedWord T) : abs (F g.p g.r g.z) ≤ A*g.tree.forkCost f:=by
    have HP : g.z.tree.disorderExpect (fullWeight n) (fullFeature n) 0 q
        (fun σ=>(P (g.p.restrict (g.r.restrict (g.z.restrict σ))))^2) 0 ≤ A^2:=by
      rw [g.r.tree.markedAttach_disorderPreserves_actual (fullWeight_pos n) (fullFeature n) ho
        g.z g.hz 0 q (fun σ=>(P (g.p.restrict (g.r.restrict σ)))^2) 0,
        g.p.tree.markedAttach_disorderPreserves_actual (fullWeight_pos n) (fullFeature n) ho
          g.r g.hr 0 q (fun σ=>(P (g.p.restrict σ))^2) 0,
        T.markedAttach_disorderPreserves_actual (fullWeight_pos n) (fullFeature n) ho
          g.p g.hp 0 q (fun σ=>(P σ)^2) 0]
      exact hP
    have H:=native_original_G_pair_expect_abs_le_radius g.z.tree ho U hU b h K C hKC q
      (fun σ=>P (g.p.restrict (g.r.restrict (g.z.restrict σ))))
      (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
      (g.z.embed g.r.mark) g.z.mark A hA HP
    apply H.trans
    apply mul_le_mul_of_nonneg_left _ hA
    change _ ≤ g.z.tree.forkCost f
    split_ifs with HS
    · have HF:=g.z.tree.split_le_forkCost hf (g.z.embed g.r.mark) g.z.mark HS.2
      simpa only [f,not_lt.mpr HS.1,ite_false] using HF
    · exact g.tree.forkCost_nonneg hf
  have Habs (l : List ℝ) : abs l.sum ≤ (l.map abs).sum:=by
    induction l with
    | nil=>simp
    | cons u l ih=>
      simp only [List.sum_cons,List.map_cons]
      linarith [abs_add_le u l.sum]
  rw [HE]
  calc
    _ ≤ ((nativeOriginalGMarkedWords T).map (fun g=>abs (g.coefficient*F g.p g.r g.z))).sum:=
      by simpa only [List.map_map,Function.comp_def] using
        Habs ((nativeOriginalGMarkedWords T).map (fun g=>g.coefficient*F g.p g.r g.z))
    _ ≤ ((nativeOriginalGMarkedWords T).map (fun g=>A*(abs g.coefficient*g.tree.forkCost f))).sum:=by
      apply List.sum_le_sum
      intro g hg
      rw [abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left (HB g) (abs_nonneg g.coefficient)]
    _ = A*((nativeOriginalGMarkedWords T).map (fun g=>abs g.coefficient*g.tree.forkCost f)).sum:=
      List.sum_map_mul_left _ _ _
    _ ≤ A*(forkVariation r 3*(T.forkCost f+edgeBudget 0 as f)):=
      mul_le_mul_of_nonneg_left (nativeOriginalGMarkedWords_forkProfile_le T ho f hf r hr) hA
    _ = _:=by ring

end OAI.SKFluctuations.Cavity
