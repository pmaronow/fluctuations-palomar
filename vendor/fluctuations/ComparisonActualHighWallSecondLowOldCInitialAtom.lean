module

public import ComparisonActualHighWallSecondLowRawInitialAtom
public import ComparisonActualHighWallSecondLowOldCAtomBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal ENNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_second_low_old_c_error_atom_initial_modulus_budget
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
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length →
          partitionPoint 0 as U ≤ Ccut*M.data.d → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n (degree+1) T) (forms : Fin (degree+1) → NativeSourceFactorForm),
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀(e0 : Fin (degree+1)) (i : ℕ),forms e0=.centered →
          T.splitIndex (G.i e0) (G.j e0)=i →
        ∀(f c z : T.Slot),T.splitIndex f c < U → T.splitIndex c z < U → f ≠ z → ∀firstError : Bool,
          let errorCut:=if firstError then T.splitIndex f c else T.splitIndex c z
          let dErr:=actualLowErrorComparisonConstant (2*M.data.T) M.data.T*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as errorCut+1/(n+1:ℕ))
          |T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K)
            (nativeSecondLowOldCBaselineErrorAtom n U b h K T
              (G.canonicalHighWallSource M forms).restProduct f c z firstError) 0| ≤
            C*M.data.d*dErr*M.data.d^degree*(Ci*M.data.d*
              originalInitialLowMomentModulus
                (originalHighWallInitialPairErrorScale M as i) (Ci*M.data.d) 8) := by
  obtain ⟨Cp,Ci,Cr,hCp,hCi,hCr,H⟩:=eventually_actual_high_wall_second_low_raw_atom_initial_modulus_budget
    (D:=D) degree 2 rBound Bclock Cmass Ccut hCm hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*(2*max Bclock 0))*Cp^degree*Cr
  refine ⟨C,Ci,by dsimp [C];positivity,hCi,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro U T hU hcut hT G forms hmass e0 i hform hinit f c z Hfc Hcz Hfz firstError
  have Hfn:f ≠ c:=native_second_low_low_slots_ne T U hU f c Hfc
  have Hcn:c ≠ z:=native_second_low_low_slots_ne T U hU c z Hcz
  have hz0:(0:ℝ)∈Icc (0:ℝ) 1:=by norm_num
  cases firstError
  · have HH:=hk U T 0 0 hU hcut hz0 hz0 hT G forms hmass e0 i hform hinit c z Hcz
      ![false,true] ![0,0] ![f,f] ![c,z]
      (by intro e;fin_cases e <;> norm_num) (by intro e;fin_cases e;exact Hfn;exact Hfz)
    simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
      Bool.false_eq_true,ite_false,ite_true,mul_one] at HH
    apply HH.trans_eq
    simp only [C,Bool.false_eq_true,ite_false]
    ring
  · have HH:=hk U T 0 0 hU hcut hz0 hz0 hT G forms hmass e0 i hform hinit f c Hfc
      ![false,true] ![1,0] ![c,f] ![z,z]
      (by intro e;fin_cases e <;> norm_num) (by intro e;fin_cases e;exact Hcn;exact Hfz)
    simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
      Bool.false_eq_true,ite_false,ite_true,mul_one] at HH
    apply HH.trans_eq
    simp only [C,ite_true]
    ring

end OAI.SKFluctuations.Cavity
