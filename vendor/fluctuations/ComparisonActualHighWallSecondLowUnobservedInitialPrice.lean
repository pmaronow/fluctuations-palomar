module

public import ComparisonActualHighWallSecondLowOriginalInitialWord
public import ComparisonActualHighWallSecondLowUnobservedPrice

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false

theorem eventually_actual_high_wall_second_low_unobserved_class_initial_modulus_price
    (degree rBound : ℕ) (Bclock Cmass Ccut : ℝ) (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C Ci : ℝ,0 < C ∧ 0 < Ci ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d → ∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (hU : U ≤ as.length),
          partitionPoint 0 as U ≤ Ccut*M.data.d → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n (degree+1) T) (forms : Fin (degree+1) → NativeSourceFactorForm),
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
          ∀(e0 : Fin (degree+1)) (i : ℕ),forms e0=.centered →
            T.splitIndex (G.i e0) (G.j e0)=i → ∀a z : T.Slot,T.splitIndex a z < U →
        ∀j : Fin 8,|nativeSecondLowClassLedger n q U b h K T hU
          (G.canonicalHighWallSource M forms).restProduct a z j false/2| ≤ C*M.data.d^3*M.data.d^degree*(Ci*M.data.d*
            originalInitialLowMomentModulus
              (originalHighWallInitialPairErrorScale M as i) (Ci*M.data.d) 8) := by
  obtain ⟨Cw,Ci,hCw,hCi,HW⟩:=eventually_actual_high_wall_second_low_original_word_initial_modulus_budget
    (D:=D) degree rBound Bclock Cmass Ccut hCm hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cd,hCd,HD⟩:=eventually_actual_high_wall_original_low_error_radius_bigO
    (D:=D) Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let CB:=actualLowErrorComparisonConstant (2*max Bclock 0) (max Bclock 0)
  have hCB : 0 ≤ CB:=actualLowErrorComparisonConstant_nonneg _ (le_max_right _ _)
  let Poly:=4*(rBound:ℝ)*(rBound+1)*(rBound+2)*(rBound+3)
  let C:=Poly*Ccut*Cw*CB*(Cd+1)+1
  have hPoly : 0 ≤ Poly:=by dsimp only [Poly];positivity
  refine ⟨C,Ci,by dsimp only [C];positivity,hCi,?_⟩
  filter_upwards [HW,HD,eventually_actual_high_wall_site_le_square (delta:=delta) (cl:=cl) (cu:=cu)
    (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0] with n hnW hnD hnSite
  intro M hwork L us hus hret hmesh
  filter_upwards [hnW M hwork L us hus hret hmesh,hnD M hwork L us hus hret hmesh] with k hkW hkD
  dsimp only at hkW hkD ⊢
  intro U T hU hcut hT G forms hmass e0 i hform hinit a z haz j
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let P:=(G.canonicalHighWallSource M forms).restProduct
  let F:=nativeSecondLowUnobservedWord n q U b h K hU P a z j
  let eta:=originalInitialLowMomentModulus
    (originalHighWallInitialPairErrorScale M as i) (Ci*M.data.d) 8
  let A:=Ci*M.data.d*eta
  have he:=original_high_wall_initial_pair_error_scale_nonneg M as i
  have hA : 0 ≤ A:=mul_nonneg (mul_nonneg hCi.le M.data.hd.le)
    (original_initial_low_moment_modulus_nonneg he (mul_nonneg hCi.le M.data.hd.le) 8)
  let Bd:=2*Cw*CB*(Cd+1)*M.data.d^2*M.data.d^degree*A
  have hd : 0 < M.data.d:=M.data.hd
  have hBd : 0 ≤ Bd:=by dsimp only [Bd];positivity
  have ho:=finiteCutMasses_ordered us hus k
  have Hsite : (1:ℝ)/(n+1:ℕ) ≤ M.data.d:=by
    have HH:=hnSite M hwork
    have HH' : 3*(1/((n+1:ℕ):ℝ)) ≤ M.data.d^2:=by convert HH using 1;ring
    have Hds : M.data.d^2 ≤ M.data.d:=by nlinarith only [hd.le,M.data.hd1]
    linarith only [HH',Hds,show (0:ℝ) ≤ 1/(n+1:ℕ) by positivity]
  have Hfactor : actualLowErrorComparisonConstant (2*M.data.T) M.data.T ≤ CB:=actual_wall_low_error_comparison_constant_le
    (M.data.hepsilon.1.trans M.data.hepsilon.2).le (M.hT.trans (le_max_left _ _))
  have HF : ∀p∈T.markedAttach 0,∀r∈p.tree.markedAttach 0,∀s∈r.tree.markedAttach 0,∀t∈s.tree.markedAttach 0,
      |F p r s t| ≤ Bd:=by
    intro p hp r hr s hs t ht
    unfold F nativeSecondLowUnobservedWord
    split_ifs with Hpath
    · by_cases Hfirst : r.tree.splitIndex (r.embed p.mark) r.mark < U
      · by_cases Hsecond : t.tree.splitIndex (t.embed s.mark) t.mark < U
        · have HH:=hkW U T hU hcut hT G forms hmass e0 i hform hinit a z haz p hp r hr s hs t ht Hfirst Hsecond
          have Hm1 : partitionPoint 0 as (r.tree.splitIndex (r.embed p.mark) r.mark) ≤ Ccut*M.data.d:=
            (partitionPoint_mono as ho Hfirst.le).trans hcut
          have Hm2 : partitionPoint 0 as (t.tree.splitIndex (t.embed s.mark) t.mark) ≤ Ccut*M.data.d:=
            (partitionPoint_mono as ho Hsecond.le).trans hcut
          have HD1:=hkD _ (r.tree.splitIndex_le_clockLength _ _) Hm1
          have HD2:=hkD _ (t.tree.splitIndex_le_clockLength _ _) Hm2
          have Hsum : nativeOriginalCutLowErrorRadius n M.bf M.hf as (r.tree.splitIndex (r.embed p.mark) r.mark)+
              nativeOriginalCutLowErrorRadius n M.bf M.hf as (t.tree.splitIndex (t.embed s.mark) t.mark)+2/(n+1:ℕ)
              ≤ 2*(Cd+1)*M.data.d:=by
                dsimp only [as]
                have HH:=mul_le_mul_of_nonneg_left Hsite (by norm_num : (0:ℝ) ≤ 2)
                have HH' : 2/((n+1:ℕ):ℝ) ≤ 2*M.data.d:=by convert HH using 1 <;> ring
                linarith only [HD1,HD2,HH']
          have HP:=mul_le_mul Hfactor Hsum
            (add_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by positivity)) hCB
          apply HH.trans
          have HM:=mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left HP (mul_nonneg hCw.le hd.le))
              (pow_nonneg hd.le degree)) hA
          change _ ≤ 2*Cw*CB*(Cd+1)*M.data.d^2*M.data.d^degree*A
          convert HM using 1 <;> ring
        · rw [native_second_low_original_word_eq_error_allocations n q U b h K T ho P a z p r s hs t ht,
            native_second_low_first_error_word_zero_second_high n q U b h K P a z p r s t (not_lt.mp Hsecond),
            native_second_low_second_error_word_zero_second_high n q U b h K P a z p r s t (not_lt.mp Hsecond),zero_add,abs_zero]
          exact hBd
      · rw [native_second_low_original_word_eq_error_allocations n q U b h K T ho P a z p r s hs t ht,
          native_second_low_first_error_word_zero_first_high n q U b h K P a z p r s hs t ht (not_lt.mp Hfirst),
          native_second_low_second_error_word_zero_first_high n q U b h K P a z p r s hs t ht (not_lt.mp Hfirst),zero_add,abs_zero]
        exact hBd
    · simpa only [abs_zero] using hBd
  have HE:=native_second_low_entry_four_average_abs_le T U hU ho hT (nativeSecondLowFirstMiddleIsFirst j) F hBd HF
  rw [←actual_general_second_low_unobserved_class_eq_entry_four n q U b h K T hU P a z j] at HE
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have HB:=div_le_div_of_nonneg_right HE (by norm_num : (0:ℝ) ≤ 2)
  apply HB.trans
  have HM:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcut hPoly) hBd
  have HM':=div_le_div_of_nonneg_right HM (by norm_num : (0:ℝ) ≤ 2)
  dsimp only [Bd] at HM'
  have HC:=mul_le_mul_of_nonneg_right
    (show Poly*Ccut*Cw*CB*(Cd+1) ≤ C by dsimp only [C];linarith)
    (mul_nonneg (mul_nonneg (pow_nonneg hd.le 3) (pow_nonneg hd.le degree)) hA)
  apply HM'.trans
  convert HC using 1 <;> ring

end OAI.SKFluctuations.Cavity
