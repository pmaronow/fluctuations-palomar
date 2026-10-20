module

public import ComparisonNativeWeightedDyadicCover
public import ComparisonPhysicalDyadicSum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology BigOperators
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

namespace NativeContactDyadicBandFamily

def finitePhysicalConsumers {m : NativeBandModel} (g : NativeContactDyadicBandFamily m)
    {exponent : ℝ} (hUlower : 1/m.N ≤ m.U)
    (hordinary : ∀j : comparisonMassDyadicIndices m.U,
      (∫u in 0..1,(g.model j).ordinaryMask ((g.model j).R u)*(g.model j).comparisonErrorDensity u) ≤
        m.N^exponent*m.E)
    (hbroad : ∀(c : NativeActualCapInterval m) (f : NativeWholeCapBroadSampler m c) (i : Fin f.count),
      ((m.H c.a=0 ∧ m.H c.z=0) ∨ (c.a=0 ∧ m.H c.z=0) ∨ (m.H c.a=0 ∧ c.z=1)) →
      (∫u in 0..1,(f.slice i).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u) ≤
        m.N^exponent*m.E) : NativeFiniteBandConsumers m where
  budget := 48*Real.log m.N*m.N^exponent*m.E+
    (∫u in 0..min (8*m.U) 1,m.comparisonErrorDensity u)
  consume := by
    intro F c hcase _hunion hd
    have ho := comparison_physical_dyadic_sum (Finset.univ : Finset (comparisonMassDyadicIndices m.U))
      (fun j=>(j:ℕ)) m.hN m.hlog m.hU hUlower m.hE.le
      (fun j _=>by simpa only [mul_comm] using (comparison_mass_dyadic_scale m.hU j).2.2)
      (fun k=>by
        have hc : (Finset.univ.filter (fun j : comparisonMassDyadicIndices m.U=>(j:ℕ)=k)).card ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro i hi j hj
          exact Subtype.ext ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
        omega)
      (fun j=>∫u in 0..1,(g.model j).ordinaryMask ((g.model j).R u)*(g.model j).comparisonErrorDensity u)
      (fun j _=>hordinary j)
    have hb := comparison_physical_dyadic_sum (Finset.univ : Finset (nativeActualBroadSliceIndex m c))
      (nativeActualBroadDyadIndex m c) m.hN m.hlog m.hU hUlower m.hE.le
      (fun i _=>by
        have hh := nativeActualBroadSliceScale_le_one m c i
        rw [nativeActualBroadSliceScale_eq_dyad,nativeDyadicMass] at hh
        simpa only [mul_comm] using hh)
      (nativeActualBroadDyadIndex_card_le_four m c hd)
      (fun i=>∫u in 0..1,(nativeActualBroadSlice m c i).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u)
      (fun i _=>hbroad (c i.1.val) (nativeActualBroadCapSampler m c i.1) i.2 (hcase i.1.val))
    have hcc := g.contact_comparable_error_le_sum c hcase
    rw [nativeBroadNearZero_integral_eq_initial_mass] at hcc
    linarith

end NativeContactDyadicBandFamily
end OAI.SKFluctuations.LaplaceWindowFormalization
