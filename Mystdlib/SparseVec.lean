

namespace BitVec 

theorem cpopNatRec_leq
  {v : BitVec w}
  {n k m : Nat}
  : n < k -> cpopNatRec v n m ≤ cpopNatRec v k m := by
    intro lt
    rw [cpopNatRec_eq]; rw (occs := [2]) [cpopNatRec_eq]
    simp
    induction k <;> expose_names
    · simp_all
    · by_cases h' : n < n_1
      · simp only [cpopNatRec_succ, Nat.zero_add]
        rw (occs := [2]) [cpopNatRec_eq] 
        grind
      · have : n_1 ≤ n := by grind
        rw [Nat.le_iff_lt_or_eq] at this
        rcases this with h'' | h''
        · simp_all; grind
        · simp; rw (occs := [2]) [cpopNatRec_eq]
          simp_all

theorem cpopNatRec_lt
  {v : BitVec w}
  {n m : Nat}
  : ∀k, n ≤ k -> (h : k < w) -> v.getLsb ⟨k, h⟩ = true -> cpopNatRec v n m < cpopNatRec v w m := by
    intro i h lt eq
    rw [cpopNatRec_eq]; rw (occs := [2]) [cpopNatRec_eq]; simp
    induction v; simp_all; expose_names
    simp_all
    rw [BitVec.getElem_cons] at *
    split at eq
    · simp_all only [Nat.lt_add_one, Nat.lt_irrefl, forall_false, cpopNatRec_cons_of_le,
      ↓reduceDIte, Bool.toNat_true]
      rw (occs := [2]) [cpopNatRec_eq]
      subst_vars
      rw [Nat.le_iff_lt_or_eq] at h
      rcases h with h | h
      · have := cpopNatRec_leq h (m := 0) (v := bv)
        grind [cpopNatRec_leq]
      · grind
    · grind [cpopNatRec_eq, BitVec.cpopNatRec_cons_of_le]

theorem setWidth_cpop_leq
  {n w : Nat}
  {v : BitVec w}
  {h : n ≤ w}
  : (v.setWidth n).cpop.toNat ≤ v.cpop.toNat := by
    simp only [toNat_cpop]
    rw [Nat.le_iff_lt_or_eq] at h
    rcases h with h | h <;> simp_all [cpopNatRec_leq]

theorem setWidth_cpop_lt
  {n w : Nat}
  {v : BitVec w}
  {h : n < w}
  : ∀k, n ≤ k -> (h : k < w) -> v.getLsb ⟨k, h⟩ = true -> (v.setWidth n).cpop.toNat < v.cpop.toNat := by
    intro i leq lt eq
    simp only [toNat_cpop]
    simp_all
    apply cpopNatRec_lt i leq lt eq


def leqCpop {w : Nat} (bits : BitVec w) (idx : Fin w) :=
  (bits.extractLsb' 0 idx).cpop

theorem leqCpop_cpop_toNat_leq
  : (leqCpop v idx).toNat ≤ v.cpop.toNat := by
    unfold leqCpop
    rw [<- BitVec.setWidth_eq_extractLsb' (by grind)]
    simp [setWidth_cpop_leq]


theorem leqCpop_cpop_toNat_lt
  {v : BitVec w}
  {idx : Fin w}
  : ∀k, idx ≤ k -> (h : k < w) -> v.getLsb ⟨k, h⟩ = true -> (leqCpop v idx).toNat < v.cpop.toNat := by
    intro i leq h eq
    unfold leqCpop
    rw [<- BitVec.setWidth_eq_extractLsb' (by grind)]
    apply setWidth_cpop_lt i leq h eq
    grind

end BitVec

namespace SparseVec 

structure Raw (w : Nat) (α : Type) where
  mask : BitVec w
  elems : Array α

namespace Raw

def get?Impl {α : Type} {w : Nat} (vec : Raw w α) (idx : Fin w) : Option α :=
  if vec.mask[idx] 
  then
    let denseIdx := vec.mask.leqCpop idx
    vec.elems[denseIdx.toNat]?
  else .none

theorem get?Impl_if_eq
  {xraw : Raw w α}
  : ∀idx : Fin w, xraw.mask[idx] -> xraw.get?Impl idx = xraw.elems[xraw.mask.leqCpop idx |>.toNat]? := by
    grind [get?Impl]

def WF (xraw : Raw w α) : Prop :=
  xraw.elems.size = xraw.mask.cpop.toNat

theorem WF.leqCpop_mask_toNat_leq_elems_size
  {xraw : Raw w α}
  {wf : xraw.WF}
  {idx : Fin w}
  : ∀k, idx ≤ k -> (h : k < w) -> xraw.mask.getLsb ⟨k, h⟩ = true -> (xraw.mask.leqCpop idx).toNat < xraw.elems.size := by
    intro i leq h eq
    unfold WF at wf
    rw [wf]
    apply BitVec.leqCpop_cpop_toNat_lt i leq h eq

end Raw

structure _root_.SparseVec (w : Nat) (α : Type) where
  raw : Raw w α
  wf : raw.WF

def mask (v : SparseVec w α) : BitVec w :=
  v.raw.mask

def elems (v : SparseVec w α) : Array α :=
  v.raw.elems

theorem SparseVec.property (v : SparseVec w α)
  : v.elems.size = v.mask.cpop.toNat := by
    rcases v with ⟨raw, wf⟩
    unfold Raw.WF at wf
    simp_all [elems, mask]


def get? {α : Type} {w : Nat } (vec : SparseVec w α) (idx : Fin w) : Option α :=
  vec.raw.get?Impl idx

theorem get?_eq_aux
  {vec : SparseVec w α}
  {idx : Fin w}
  : vec.mask[idx] = true -> (vec.mask.leqCpop idx).toNat < vec.elems.size := by
    intro h
    obtain ⟨raw, wf⟩ := vec
    unfold Raw.WF at wf
    simp_all [elems, mask]
    have := Raw.WF.leqCpop_mask_toNat_leq_elems_size (xraw := raw) (wf := wf) (idx := idx) idx (by simp) (by simp) h
    grind


theorem get?_eq
  {vec : SparseVec w α}
  {idx : Fin w}
  : vec.get? idx = if h : vec.mask[idx] then Option.some (getElem vec.elems (vec.mask.leqCpop idx).toNat (get?_eq_aux h)) else Option.none := by
    unfold get? Raw.get?Impl
    simp only [Fin.getElem_fin]
    split <;> expose_names
    · split
      · simp_all [mask, elems]
      · grind [mask]
    · grind [mask]





