module

public import ComparisonSignedCavitySmallCutAtomicBudget
public import ComparisonSignedCavityBareContinuumLowProfile

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

theorem native_small_cut_low_profile_eq_scaled (n U V : ℕ) (hVU : V ≤ U)
    (l t : ℝ) (b h K : ℕ→ℝ) (j : ℕ) (hj : j < V) (σ τ : Spin n×Bool) :
    ReplicaTree.coordinateProfile (fullFeature n)
      (cutLSlope n V t (relocatedClock U l b) (relocatedClock U l h) (relocatedClock U l K)) j σ τ=
      l*ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K) j σ τ := by
  have hju : j < U:=lt_of_lt_of_le hj hVU
  have HE (i : FullCoordinate n) :
      cutLSlope n V t (relocatedClock U l b) (relocatedClock U l h) (relocatedClock U l K) j i=
        l*cutLSlope n U t b h K j i := by
    rcases i with (i|i)|(i|i) <;>
      simp only [cutLSlope,hj,hju,ite_true,relocatedClock,fullVariance,Sum.elim_inl,Sum.elim_inr,Pi.zero_apply,mul_zero] <;>ring
  unfold ReplicaTree.coordinateProfile
  simp only [HE,mul_assoc,Finset.mul_sum]

theorem eventually_actual_minimum_bare_small_cut_low_moment
    (order : ℕ) (horder : 0 < order) (Bclock Temp Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cq : ℝ,0 < Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U V : ℕ),V ≤ U → partitionPoint 0 as V ≤ Ccut*M.xs →
        ∀(l t s : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → s∈Icc (0:ℝ) 1 →
        ∀j ≤ as.length,
          (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n q U l t b h K)
            (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n)
              (cutLSlope n V s (relocatedClock U l b) (relocatedClock U l h) (relocatedClock U l K)) j
              (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(2*order)) 0 ≤
            (Cq*(1+Ccut)*M.xs)^(2*order) := by
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_bare_continuum_low_profile_moment
    (D:=D) order horder Bclock Temp hTemp hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cq,hCq,?_⟩
  filter_upwards [HQ] with n hnQ
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hnQ M hb hh hxs L us hus hret hmesh] with jGrid hgridQ
  dsimp only at hgridQ ⊢
  intro U V hVU hcut l t s hl ht hs j hj
  let as:=finiteCutMasses us jGrid
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  by_cases hjV : j < V
  · have Hraw:=hgridQ U l t s hl ht hs j hj
    have HE (σ : (ClockTree.pairClock as j).Assignment) :=
      native_small_cut_low_profile_eq_scaled n U V hVU l s
        (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
        (fun j=>(M.hf (partitionPoint 0 as j):ℝ))
        (fun j=>(M.hf (partitionPoint 0 as j):ℝ)+(M.bf (partitionPoint 0 as j):ℝ)*
          orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)) j hjV
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2
    dsimp only [as] at HE
    conv_lhs => simp only [HE,abs_mul,abs_of_nonneg hl.1,mul_pow]
    rw [ClockTree.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) _ ho]
    have Hl : l^(2*order) ≤ 1:=pow_le_one₀ hl.1 hl.2
    have Hnonneg : 0 ≤ (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
        (cutFullVariance n (fun j=>Sum.elim (fun _=>(M.bf (partitionPoint 0 as j):ℝ))
          (fun _=>(M.hf (partitionPoint 0 as j):ℝ))) U l t
          (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ))
          (fun j=>(M.hf (partitionPoint 0 as j):ℝ)+(M.bf (partitionPoint 0 as j):ℝ)*
            orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)))
        (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n)
          (cutLSlope n U s (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
            (fun j=>(M.hf (partitionPoint 0 as j):ℝ))
            (fun j=>(M.hf (partitionPoint 0 as j):ℝ)+(M.bf (partitionPoint 0 as j):ℝ)*
              orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j))) j
          (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(2*order)) 0:=by
      unfold ClockTree.disorderExpect
      exact Finset.sum_nonneg fun σ _=>mul_nonneg
        (((ClockTree.pairClock as j).disorderWeight_probability
          (fullWeight_pos n) (fullFeature n) ho _ _ _).1 σ)
        (pow_nonneg (abs_nonneg _) _)
    apply (mul_le_of_le_one_left Hnonneg Hl).trans
    apply Hraw.trans
    apply pow_le_pow_left₀ (mul_nonneg hCq.le (add_nonneg M.hxs.le (partitionPoint_mem as ho j).1))
    have Hmass:=partitionPoint_mono as ho hjV.le
    have Hscale : M.xs+partitionPoint 0 as j ≤ (1+Ccut)*M.xs:=by nlinarith only [hcut,Hmass]
    exact (mul_le_mul_of_nonneg_left Hscale hCq.le).trans_eq (by ring)
  · have HE : (fun σ=>|ReplicaTree.coordinateProfile (fullFeature n)
        (cutLSlope n V s (relocatedClock U l (fun j=>(M.bf (partitionPoint 0 as j):ℝ)))
          (relocatedClock U l (fun j=>(M.hf (partitionPoint 0 as j):ℝ)))
          (relocatedClock U l (fun j=>(M.hf (partitionPoint 0 as j):ℝ)+
            (M.bf (partitionPoint 0 as j):ℝ)*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)))) j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(2*order))=fun _=>0:=by
      funext σ
      simp only [ReplicaTree.coordinateProfile,cutLSlope,hjV,ite_false,Pi.zero_apply,
        zero_mul,Finset.sum_const_zero,abs_zero,zero_pow (by omega : 2*order≠0)]
    rw [HE]
    simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
    exact pow_nonneg (mul_nonneg (mul_nonneg hCq.le (add_nonneg zero_le_one hCcut)) M.hxs.le) _

end OAI.SKFluctuations.Cavity
