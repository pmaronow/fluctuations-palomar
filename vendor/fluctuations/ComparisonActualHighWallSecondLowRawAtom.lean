module

public import ComparisonActualHighWallHighAllDegreeContinuumMoments
public import ComparisonActualHighWallLowProfileMoments
public import ComparisonActualHighWallSourceClockBudget
public import ComparisonSignedCavityInheritedRawLowAtomBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_second_low_raw_atom_budget
    (degree rows rBound : ℕ) (Bclock Cmass Ccut : ℝ) (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp Cr : ℝ,0 < Cp ∧ 0 < Cr ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d → ∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),U ≤ as.length →
          partitionPoint 0 as U ≤ Ccut*M.data.d → l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n degree T) (forms : Fin degree → NativeSourceFactorForm),
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀(u z : T.Slot),T.splitIndex u z < U →
        ∀(site : Fin rows → Bool) (v : Fin rows → ℝ) (s w : Fin rows → T.Slot),
          (∀e,v e∈Icc (0:ℝ) 1) → (∀e,s e ≠ w e) →
          let C:=Real.exp (wholeLawRowComparisonConstant rBound*(2*max Bclock 0))*Cp^degree*M.data.d^degree
          let dErr:=actualLowErrorComparisonConstant (2*M.data.T) M.data.T*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex u z)+1/(n+1:ℕ))
          |T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
            (nativeOldInitialRowProduct n T (G.canonicalHighWallSource M forms).restProduct
              (nativeSmallCutOldErrorRestKernel n U b h K) u z
              (fun e=>nativeSmallCutOrdinaryRestKernel n U b h K (site e) (v e)) s w) 0| ≤
            C*dErr*(∏e,if site e then 1 else Cr*M.data.d) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_high_wall_all_degree_continuum_square_even_moment
    (D:=D) degree 2 rBound (by norm_num) Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cr,hCr,HR⟩:=eventually_actual_high_wall_continuum_low_profile_moment
    (D:=D) (2*(rows+1)) (by omega) Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Cr,hCp,hCr,?_⟩
  filter_upwards [HP,HR] with n hnP hnR
  intro M hwork L us hus hret hmesh
  filter_upwards [hnP M hwork L us hus hret hmesh,hnR M hwork L us hus hret hmesh] with k hkP hkR
  dsimp only at hkP hkR ⊢
  intro U T l t hU hcut hl ht hT G forms hmass u z huz site v s w hv hne
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*(2*max Bclock 0))*Cp^degree*M.data.d^degree
  let dErr:=actualLowErrorComparisonConstant (2*M.data.T) M.data.T*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex u z)+1/(n+1:ℕ))
  let r:=fun e=>if site e then 1 else Cr*M.data.d
  have ho:=finiteCutMasses_ordered us hus k
  have hC : 0 ≤ C:=by dsimp only [C];positivity [M.data.hd]
  have hErr : 0 ≤ dErr:=mul_nonneg (actualLowErrorComparisonConstant_nonneg _
    (M.data.hepsilon.1.trans M.data.hepsilon.2).le)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hneUZ : u ≠ z:=by intro H;rw [H,T.splitIndex_self] at huz;omega
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun sigma=>|(G.canonicalHighWallSource M forms).product sigma|^4) 0 ≤ C^4:=by
    simpa only [Nat.reduceMul,C,law,q,b,h,K,as] using
      hkP U T l t hl ht hT G forms hmass
  have Herror : (pairClock as (T.splitIndex u z)).disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun sigma=>(nativeRestRowKernel n (nativeSmallCutOldErrorRestKernel n U b h K) (T.splitIndex u z)
        (pairSpin as (T.splitIndex u z) sigma).1 (pairSpin as (T.splitIndex u z) sigma).2)^2) 0 ≤ dErr^2:=by
    rw [native_small_cut_old_error_eq_original_profile]
    change nativeWholeLawErrorSecond n as law (cutLowError n U b h K) (T.splitIndex u z) ≤ dErr^2
    rw [nativeWholeLawErrorSecond_eq_radius_sq n ho law]
    apply pow_le_pow_left₀ (nativeWholeLawErrorRadius_nonneg _ _ _ _ _) _ 2
    have H:=M.data.current_low_error_radius_le_original M.alpha as ho U hl ht
      (T.splitIndex u z) (T.splitIndex_le_clockLength u z)
    rw [ite_eq_left huz] at H
    simpa only [law,q,b,h,K,dErr,as] using H
  have HE e : (pairClock as (T.splitIndex (s e) (w e))).disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun sigma=>|nativeRestRowKernel n (nativeSmallCutOrdinaryRestKernel n U b h K (site e) (v e))
        (T.splitIndex (s e) (w e)) (pairSpin as (T.splitIndex (s e) (w e)) sigma).1
          (pairSpin as (T.splitIndex (s e) (w e)) sigma).2|^(4*(rows+1))) 0 ≤ (r e)^(4*(rows+1)):=by
    cases hs : site e
    · dsimp only [nativeSmallCutOrdinaryRestKernel,r]
      simp only [hs,Bool.false_eq_true,ite_false]
      rw [native_small_cut_moving_kernel_eq_original_profile]
      simpa only [←Nat.mul_assoc,Nat.reduceMul,law,q,b,h,K,as] using
        hkR U l t (v e) hl ht (hv e) hcut (T.splitIndex (s e) (w e)) (T.splitIndex_le_clockLength _ _)
    · dsimp only [nativeSmallCutOrdinaryRestKernel,r]
      simp only [hs,ite_true,native_small_cut_site_row_abs_one,one_pow]
      exact le_of_eq (ClockTree.disorderExpect_one (fullWeight_pos n) (fullFeature n) _ ho 0 law 0)
  have hr e : 0 < r e:=by dsimp only [r];split_ifs <;> positivity [M.data.hd]
  have HH:=ClockTree.native_initial_observed_error_product_abs_le (fullWeight_pos n) (fullFeature n) T ho
    0 law 0 (G.canonicalHighWallSource M forms).product hC hErr HPmoment
    (nativeRestRowKernel n (nativeSmallCutOldErrorRestKernel n U b h K)) u z hneUZ Herror
    (fun e=>nativeRestRowKernel n (nativeSmallCutOrdinaryRestKernel n U b h K (site e) (v e))) s w hne r hr HE
  unfold nativeOldInitialRowProduct
  simp_rw [(G.canonicalHighWallSource M forms).product_eq_restProduct] at HH
  exact HH

end OAI.SKFluctuations.Cavity
