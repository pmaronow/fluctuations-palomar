module

public import ComparisonSignedCavityActualFrozenGResourcePairing
public import ComparisonSignedCavityActualOriginalClockResponse

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

def nativeMinimumClockHighGAtom {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (U : ℕ) (a c e f : T.Slot) : T.Assignment→ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  nativeOriginalHighGAtom T U K b
    (nativePhysicalResourceCenter n M.bf M.hf as) a c e f

theorem native_minimum_clock_high_g_atom_abs_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (K : ℕ→ℝ)
    (hcl : 0 < cl) (hAz : 0≤Az) (hTemp : 0≤Temp)
    (hb : ∀u,M.b u=Temp) (hh : ∀u,M.h u=0)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (a c e f : T.Slot) (σ : T.Assignment) :
    |nativeMinimumClockHighGAtom M K T U a c e f σ|≤2*Temp := by
  have Hbond:=M.bare_source_clock_bounds hcl hAz Temp hb hh (partitionPoint_mem as ho (T.splitIndex e f))
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  change |nativeOriginalHighGAtom T U K b
    (nativePhysicalResourceCenter n M.bf M.hf as) a c e f σ|≤_
  exact native_original_high_g_atom_abs_le T ho U K b
    (nativePhysicalResourceCenter n M.bf M.hf as) a c e f hTemp
    (by rw [abs_of_nonneg Hbond.1];exact Hbond.2.1)
    (native_physical_resource_center_abs_le_one n M.bf M.hf (toNNReal_monotoneOn had.1)
      (toNNReal_monotoneOn had.2.1) as ho _) σ

theorem native_minimum_clock_high_g_atom_second_moment_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (K : ℕ→ℝ)
    (hcl : 0 < cl) (hAz : 0≤Az) (hTemp : 0≤Temp)
    (hb : ∀u,M.b u=Temp) (hh : ∀u,M.h u=0)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (a c e f : T.Slot) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) :
    T.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(nativeMinimumClockHighGAtom M K T U a c e f σ)^2) x≤(2*Temp)^2 := by
  have hw:=T.disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho v q x
  unfold ClockTree.disorderExpect
  calc
    _≤∑σ : T.Assignment,T.disorderWeight (fullWeight n) (fullFeature n) v q σ x*(2*Temp)^2 := by
      apply Finset.sum_le_sum
      intro σ _
      have H:=native_minimum_clock_high_g_atom_abs_le M K hcl hAz hTemp hb hh T ho U a c e f σ
      have Hsq:=(sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤2*Temp)).mpr H
      rw [sq_abs] at Hsq
      exact mul_le_mul_of_nonneg_left Hsq (hw.1 σ)
    _=(2*Temp)^2 := by rw [←Finset.sum_mul,hw.2,one_mul]

def NativeOriginalGMarkedWord.clockAtom {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (K : ℕ→ℝ)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (g : NativeOriginalGMarkedWord T) (U : ℕ) (a : T.Slot) : g.tree.Assignment→ℝ :=
  nativeMinimumClockHighGAtom M K g.tree U
    (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
    (g.z.embed g.r.mark) g.z.mark

theorem NativeOriginalGMarkedWord.actual_clock_second_moment_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (K : ℕ→ℝ)
    (hcl : 0 < cl) (hAz : 0≤Az) (hTemp : 0≤Temp)
    (hb : ∀u,M.b u=Temp) (hh : ∀u,M.h u=0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (g : NativeOriginalGMarkedWord T) (ho : MassOrdered 0 as) (U : ℕ) (a : T.Slot)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ) :
    g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(g.clockAtom M K U a σ)^2) x≤(2*Temp)^2 :=
  native_minimum_clock_high_g_atom_second_moment_le M K hcl hAz hTemp hb hh g.tree ho U _ _ _ _ v q x

end OAI.SKFluctuations.Cavity
