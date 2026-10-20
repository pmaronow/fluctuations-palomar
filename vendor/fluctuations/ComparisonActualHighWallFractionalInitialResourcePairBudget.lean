module

public import ComparisonActualHighWallInitialPairMomentInterpolation
public import ComparisonActualHighWallRawResourcePairBudget
public import ComparisonSignedCavityActualResourcePairBudgets
public import ComparisonSignedCavityOriginalPhysicalClock

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal ENNReal
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_fractional_initial_resource_pair_budget
    (degree : ℕ) (hd : 0 < degree) (Bclock Cmass : ℝ) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃A Cr : ℝ,1 ≤ A ∧ 0 < Cr ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        ∀(U i star k : ℕ) (T : ClockTree (Spin n×Bool) as)
          (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U [.initial] k T P →
          1+k≤degree → i ≤ star → star≤as.length →
          partitionPoint 0 as i≤Cmass*M.data.d →
          partitionPoint 0 as star≤Cmass*M.data.d →
          let eta:=originalInitialLowMomentModulus
            (originalHighWallInitialPairErrorScale M as i) (Cr*M.data.d) (2*degree)
          let x:=Cr*M.data.d*eta+M.data.d^4
          P.PairMomentBudget (fullWeight n) (fullFeature n) 0
            (finitePhysicalCavitySquareVariance n U as b h 1 1)
            (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
            (nativePhysicalResourceCenter n M.bf M.hf as) 0 A x M.data.d 1 := by
  obtain ⟨Cr,hCr,HI⟩:=eventually_actual_high_wall_initial_pair_moment_interpolate
    (D:=D) degree hd Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_high_wall_raw_resource_initial_pair_even_moment
    (D:=D) degree hd Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  let A:=max 1 Cs
  have hA : 1≤A:=le_max_left _ _
  have hCsA : Cs≤A:=le_max_right _ _
  refine ⟨A,Cr,hA,hCr,?_⟩
  filter_upwards [HI,HS] with n hnI hnS
  intro M hwork L us hus hret hmesh
  filter_upwards [hnI M hwork L us hus hret hmesh,
    hnS M hwork L us hus hret hmesh] with jGrid hjI hjS
  dsimp only at hjI hjS ⊢
  intro U i star k T P hP hdepth hi hs hmi hms
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let error:=originalHighWallInitialPairErrorScale M as i
  let eta:=originalInitialLowMomentModulus error (Cr*M.data.d) (2*degree)
  let x:=Cr*M.data.d*eta+M.data.d^4
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have herror : 0≤error:=original_high_wall_initial_pair_error_scale_nonneg M as i
  have heta : 0≤eta:=original_initial_low_moment_modulus_nonneg herror
    (mul_nonneg hCr.le M.data.hd.le) _
  have hx : 0<x:=by
    dsimp only [x]
    have hprod : 0≤Cr*M.data.d*eta:=mul_nonneg (mul_nonneg hCr.le M.data.hd.le) heta
    have hpow : 0<M.data.d^4:=pow_pos M.data.hd _
    linarith
  have hCrda : Cr*M.data.d*eta≤A*x:=by
    have hbase : Cr*M.data.d*eta≤x:=by
      dsimp only [x]
      exact le_add_of_nonneg_right (pow_nonneg M.data.hd.le _)
    exact hbase.trans (le_mul_of_one_le_left hx.le hA)
  have hda : Cs*M.data.d≤A*M.data.d:=mul_le_mul_of_nonneg_right hCsA M.data.hd.le
  let law:=finitePhysicalCavitySquareVariance n U as b h 1 1
  have Hinitial (l : ℕ) (hl : 0<l) (hlD : l≤degree) :
      (pairClock as i).disorderExpect (fullWeight n) (fullFeature n) 0 law
        (fun σ=>|R (pairSpin as i σ).1 (pairSpin as i σ).2-C i|^(2*l)) 0≤
        (A*x)^(2*l):=by
    have hii : i≤as.length:=hi.trans hs
    have HC : C i=S i:=(native_ordered_source_center_eq_completed n M.bf M.hf
      (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha)
      (partitionPoint_mem as ho i)).symm
    have Htop : (pairClock as i).disorderExpect (fullWeight n) (fullFeature n) 0 law
        (fun σ=>|R (pairSpin as i σ).1 (pairSpin as i σ).2-C i|^(2*degree)) 0≤
          (Cr*M.data.d*eta)^(2*degree):=by
      have HH:=hjI U 1 1 (by norm_num) (by norm_num) i hii hmi
      rw [HC]
      rw [show law=cutFullVariance n q U 1 1 b h K by
        exact (native_full_endpoint_clock_mixed_independent n q U 1 b h K
          (finitePhysicalMixedClock (n+1) as b h)).symm] 
      simpa only [law,R,C,eta,error,S,q,K,b,h,as,finitePhysicalCavitySquareVariance] using HH
    have Hlow: (pairClock as i).disorderExpect (fullWeight n) (fullFeature n) 0 law
        (fun σ=>|R (pairSpin as i σ).1 (pairSpin as i σ).2-C i|^(2*l)) 0≤
          (Cr*M.data.d*eta)^(2*l):=by
      let F:=fun σ : (pairClock (S:=Spin n×Bool) as i).Assignment=>
        R (pairSpin as i σ).1 (pairSpin as i σ).2-C i
      have HH:=(pairClock (S:=Spin n×Bool) as i).disorderExpect_rpow_moment_le
        (fullWeight_pos n) (fullFeature n) ho 0 law 0 F
        (p:=(2*l:ℕ)) (r:=(2*degree:ℕ))
        (by exact_mod_cast (show 0<2*l by omega))
        (by exact_mod_cast (show 2*l≤2*degree by omega))
        (mul_nonneg (mul_nonneg hCr.le M.data.hd.le) heta)
        (by simpa only [Real.rpow_natCast,F] using Htop)
      simpa only [Real.rpow_natCast,F] using HH
    exact Hlow.trans (pow_le_pow_left₀
      (mul_nonneg (mul_nonneg hCr.le M.data.hd.le) heta) hCrda _)
  have Hstar (l : ℕ) (hl : 0<l) (hlD : l≤degree) :
      (pairClock as star).disorderExpect (fullWeight n) (fullFeature n) 0 law
        (fun σ=>|R (pairSpin as star σ).1 (pairSpin as star σ).2-C star|^(2*l)) 0≤
        (A*M.data.d)^(2*l):=by
    have Htop:=hjS U star 1 1 (by norm_num) (by norm_num) hs hms
    have Htop' : (pairClock as star).disorderExpect (fullWeight n) (fullFeature n) 0 law
        (fun σ=>|R (pairSpin as star σ).1 (pairSpin as star σ).2-C star|^(2*degree)) 0≤
          (A*M.data.d)^(2*degree):=by
      exact Htop.trans (pow_le_pow_left₀ (mul_nonneg hCs.le M.data.hd.le) hda _)
    let F:=fun σ : (pairClock (S:=Spin n×Bool) as star).Assignment=>
      R (pairSpin as star σ).1 (pairSpin as star σ).2-C star
    have HH:=(pairClock (S:=Spin n×Bool) as star).disorderExpect_rpow_moment_le
      (fullWeight_pos n) (fullFeature n) ho 0 law 0 F
      (p:=(2*l:ℕ)) (r:=(2*degree:ℕ))
      (by exact_mod_cast (show 0<2*l by omega))
      (by exact_mod_cast (show 2*l≤2*degree by omega))
      (mul_nonneg (zero_le_one.trans hA) M.data.hd.le)
      (by simpa only [Real.rpow_natCast,F] using Htop')
    simpa only [Real.rpow_natCast,F] using HH
  exact hP.pairMomentBudget_of_initial_star_bounds degree hdepth (fullWeight n) (fullFeature n)
    0 law R C 0 A x M.data.d 1 Hinitial (by
      intro l hl hlD
      simpa only [one_mul] using Hstar l hl hlD)

end OAI.SKFluctuations.Cavity
