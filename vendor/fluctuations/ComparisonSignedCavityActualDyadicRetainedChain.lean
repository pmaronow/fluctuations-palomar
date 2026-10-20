module

public import ComparisonSignedCavityActualDyadicCutReadout
public import ComparisonSignedCavityActualDyadicCutCountAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum Set Filter
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000

structure NativeDyadicRetainedReadout (a : ℝ) (ha : 0 < a)
    (as : List PositiveMass) (U : ℕ) : Prop where
  first_virtual : (nativeDyadicMassCut a ha 0).val=a/2
  first_physical : (nativeDyadicMassCut a ha 1).val=a
  terminal_mass : (nativeDyadicMassCut a ha (nativeDyadicCutDepth a)).val=1
  literal_source_mass : partitionPoint 0 as U=a
  literal_source_lower : (nativeDyadicMassCut a ha 0).val ≤ partitionPoint 0 as U
  comparable : ∀j < nativeDyadicCutDepth a,
    (nativeDyadicMassCut a ha (j+1)).val ≤ 2*(nativeDyadicMassCut a ha j).val
  cut_monotone : Monotone (fun j=>(nativeDyadicMassCut a ha j).val)
  source_index : ∀j,1 ≤ j → j ≤ nativeDyadicCutDepth a → U ≤ nativeDyadicRetainedIndex a ha as j
  index_le_length : ∀j,nativeDyadicRetainedIndex a ha as j ≤ as.length
  exact_mass : ∀j ≤ nativeDyadicCutDepth a,
    partitionPoint 0 as (nativeDyadicRetainedIndex a ha as j)=(nativeDyadicMassCut a ha j).val
  prefix_mass : ∀j ≤ nativeDyadicCutDepth a,
    ∀u∈as.take (nativeDyadicRetainedIndex a ha as j),u.val ≤ (nativeDyadicMassCut a ha j).val
  index_monotone : ∀j k,j ≤ k → k ≤ nativeDyadicCutDepth a →
    nativeDyadicRetainedIndex a ha as j ≤ nativeDyadicRetainedIndex a ha as k
  terminal_index : nativeDyadicRetainedIndex a ha as (nativeDyadicCutDepth a)=as.length

theorem native_dyadic_retained_readout {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (hret : ∀j ≤ nativeDyadicCutDepth a,nativeDyadicMassCut a ha j∈as)
    (U : ℕ) (hU : U ≤ as.length) (hUa : partitionPoint 0 as U=a) :
    NativeDyadicRetainedReadout a ha as U := by
  obtain ⟨Hmass,Hsource,Hprefix,Hmono,Hend⟩:=nativeDyadicRetainedIndex_readout ha ha1
    (nativeDyadicCutDepth a) (nativeDyadicCutDepth_pos a)
    (nativeDyadicCutDepth_one_le_two_pow_mul_half ha) as ho hret U hU hUa
  exact ⟨nativeDyadicMassCut_zero ha ha1,nativeDyadicMassCut_one ha ha1,
    nativeDyadicMassCut_terminal ha _ (nativeDyadicCutDepth_one_le_two_pow_mul_half ha),
    hUa,by rw [nativeDyadicMassCut_zero ha ha1,hUa];linarith,
    fun j _=>nativeDyadicMassCut_comparable ha j,nativeDyadicMassCut_monotone ha,
    fun j hj hk=>(Hsource j hj hk).1,fun j=>retainedMassPrefixIndex_le_length _ _,
    Hmass,Hprefix,Hmono,Hend⟩

theorem NativeDyadicRetainedReadout.sampled_prefix_mass
    {a : ℝ} {ha : 0 < a} {as : List PositiveMass} {U : ℕ}
    (_H : NativeDyadicRetainedReadout a ha as U) (ho : MassOrdered 0 as)
    {ι : Type*} (q : ℝ→ι→ℝ≥0) (j : ℕ) :
    ∀s∈(sampleClockSteps q 0 as).take (nativeDyadicRetainedIndex a ha as j),
      s.1 ≤ (nativeDyadicMassCut a ha j).val :=
  native_retained_prefix_sampled_take_mass_le q as ho _ (nativeDyadicMassCut_le_one ha j)

theorem NativeDyadicRetainedReadout.old_index_lt
    {a : ℝ} {ha : 0 < a} {as : List PositiveMass} {U : ℕ}
    (H : NativeDyadicRetainedReadout a ha as U) {i j : ℕ}
    (hi : i < U) (hj : 1 ≤ j) (hjq : j ≤ nativeDyadicCutDepth a) :
    i < nativeDyadicRetainedIndex a ha as j := hi.trans_le (H.source_index j hj hjq)

theorem native_dyadic_chain_exists_common_net {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (L : ℕ) (extra : List PositiveMass) (hextra : ∀u∈extra,u.val ≤ 1) :
    ∃us : List PositiveMass,(∀u∈us,u.val ≤ 1) ∧
      (∀j ≤ nativeDyadicCutDepth a,nativeDyadicMassCut a ha j∈us) ∧
      (∀u∈extra,u∈us) ∧ (∀u∈uniformMasses L,u∈us) ∧
      ∀k U,U ≤ (finiteCutMasses us k).length → partitionPoint 0 (finiteCutMasses us k) U=a →
        NativeDyadicRetainedReadout a ha (finiteCutMasses us k) U := by
  obtain ⟨us,hus,hcuts,hextra',hmesh⟩:=nativeDyadicMassCutNodes_exists_common_net ha
    (nativeDyadicCutDepth a) L extra hextra
  refine ⟨us,hus,hcuts,hextra',hmesh,?_⟩
  intro k U hU hUa
  exact native_dyadic_retained_readout ha ha1 _ (finiteCutMasses_ordered us hus k)
    (fun j hj=>finiteCutMasses_nodes us k (hcuts j hj)) U hU hUa

theorem eventually_actual_dyadic_retained_chain_along
    {m delta cl cu Az C0 Ct D Bclock Cx eps : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hCx : 0 < Cx) (heps : 0 < eps)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀a : ℝ,∀ha : 0 < a,Cx*M.xs ≤ a → a ≤ 1 →
        0 < nativeDyadicCutDepth a ∧
        (nativeDyadicCutDepth a:ℝ) ≤ 2+Real.logb 2 a⁻¹ ∧
        (nativeDyadicCutDepth a:ℝ) ≤ (2+3/Real.log 2)*Real.log M.context.N ∧
        (nativeDyadicCutDepth a:ℝ) ≤ M.context.N^eps ∧
        ∀(L : ℕ) (extra : List PositiveMass),(∀u∈extra,u.val ≤ 1) →
          ∃us : List PositiveMass,(∀u∈us,u.val ≤ 1) ∧
            (∀j ≤ nativeDyadicCutDepth a,nativeDyadicMassCut a ha j∈us) ∧
            (∀u∈extra,u∈us) ∧ (∀u∈uniformMasses L,u∈us) ∧
            ∀k U,U ≤ (finiteCutMasses us k).length → partitionPoint 0 (finiteCutMasses us k) U=a →
              NativeDyadicRetainedReadout a ha (finiteCutMasses us k) U := by
  filter_upwards [eventually_actual_dyadic_cut_depth_log_bound_along
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0 hCx dim hdim,
    eventually_actual_dyadic_cut_depth_power_bound_along
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0 hCx heps dim hdim]
    with n hnLog hnPower
  intro M a ha hlow ha1
  exact ⟨nativeDyadicCutDepth_pos a,nativeDyadicCutDepth_le_two_add_logb ha ha1,
    hnLog M a hlow ha1,hnPower M a hlow ha1,
    fun L extra hextra=>native_dyadic_chain_exists_common_net ha ha1 L extra hextra⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
