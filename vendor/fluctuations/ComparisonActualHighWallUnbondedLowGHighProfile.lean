module

public import ComparisonSignedCavityGRestorationProfile
public import ComparisonActualHighWallUnbondedLowFactorMoments
public import ComparisonSignedCavityMixedErrorCanonicalLedger

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem eventually_actual_high_wall_unbonded_low_G_high_profile
    (aDegree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Cmass : ℝ) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0 < Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=2*max Bclock 0
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (t : ℝ),
          U ≤ as.length → t∈Icc (0:ℝ) 1 → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm),
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀u z a c e f : T.Slot,u≠z →
          partitionPoint 0 as (T.splitIndex u z) ≤ Cmass*M.data.d → e≠f →
          let law:=cutFullVariance n q U 0 t b h K
          let high:=cutTSlope n U 0 b h K
          |cutMixedJet n q U b h K T (fun σ=>(fun σ=>(G.canonicalHighWallSource M forms).product σ* (deletedOverlap n (joinSpin (T.atSlot σ u)) (joinSpin (T.atSlot σ z))-S (T.splitIndex u z))) σ*
            nativeOriginalHighGAtom T U K b S a c e f σ) 0 0 0 t| ≤
            |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
              (ClockTree.pairForkVariation rBound*
                (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^(aDegree+1)*
                  (M.data.d*M.data.d^aDegree))*(2*M.data.T)^((p-2)/p)*(2*M.data.T)^((p-2)/p)*
                (nativeWholeLawErrorRadius n as law high (T.splitIndex e f))^(2/p)*
                nativeWholeLawProfileCost n law high T (2/p)) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_high_wall_canonical_unbonded_low_factor_even_moment
    (D:=D) aDegree dOrder rBound hd Bclock Cmass hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [HP] with n hnP
  intro M hwork L us hus hret hmesh
  filter_upwards [hnP M hwork L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T t hU ht hT G forms hmass u z a c e f huz hnew hef
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U 0 t b h K
  let high:=cutTSlope n U 0 b h K
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*
    (2*max Bclock 0))*Cp^(aDegree+1)*
      (M.data.d*M.data.d^aDegree)
  let P:=(fun σ=>(G.canonicalHighWallSource M forms).product σ* (deletedOverlap n (joinSpin (T.atSlot σ u)) (joinSpin (T.atSlot σ z))-S (T.splitIndex u z)))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from M.data.bf_monotone M.alpha hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from M.data.hf_monotone M.alpha hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha)) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have Hb j : b j ≤ M.data.T:=by
    have HH:=M.data.total_clock_le M.alpha _ (partitionPoint_mem as ho j)
    have Hnonneg:=(M.hf (partitionPoint 0 as j)).coe_nonneg
    change (M.bf (partitionPoint 0 as j):ℝ) ≤ M.data.T
    linarith
  have hd := M.data.hd
  have HC : 0 ≤ C:=by dsimp only [C];positivity
  have Hraw:=hgrid U T 0 t (by norm_num) ht hT G forms hmass u z huz hnew
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|P σ|^(2*(p/(p-2)))) 0 ≤ C^(2*(p/(p-2))) := by
    apply T.disorderExpect_rpow_moment_le (fullWeight_pos n) (fullFeature n) ho 0 law 0 P
      (by have Hq : 0 < p/(p-2):=div_pos (by linarith) (by linarith);positivity)
      (show 2*(p/(p-2)) ≤ ((2*dOrder:ℕ):ℝ) by push_cast;linarith) HC
    simpa only [Real.rpow_natCast,P,C,law,q,b,h,S,K,as] using Hraw
  have Hcap:=native_centered_high_kernel_abs_le n U b h S (fun _=>NNReal.coe_nonneg _) Hb HS
  have hTemp := (M.data.hepsilon.1.trans M.data.hepsilon.2).le
  have H:=native_original_G_profile_restoration_bound n U b h K S (fun _=>rfl)
    T ho hU hT law P a c e f hef high HC hp (by positivity) (by positivity) HPmoment Hcap Hcap
  rw [native_cutMixedJet_zero_eq_profile n q U b h K T ho _ 0
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm (by norm_num) ht]
  exact H

end OAI.SKFluctuations.Cavity
