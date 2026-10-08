/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Ordinals.Ordinal.Basic

/-!
# Basic constructions on ordinals

The tree constructions of `Ordinals.Tree.Constructions` under the quotient, and limit ordinals.
Suprema of families choose representatives (`Ordinal.out`), so they are noncomputable.
-/

@[expose] public section

namespace Ordinals

universe u v w

namespace Ordinal

/-! ## Zero -/

instance : Zero Ordinal.{u} :=
  ⟨mk OTree.zero⟩

instance : Inhabited Ordinal.{u} :=
  ⟨0⟩

theorem zero_def : (0 : Ordinal.{u}) = mk OTree.zero :=
  rfl

protected theorem zero_le (a : Ordinal.{u}) : 0 ≤ a :=
  Ordinal.inductionOn a OTree.zero_le

protected theorem not_lt_zero (a : Ordinal.{u}) : ¬a < 0 :=
  Ordinal.inductionOn a OTree.not_lt_zero

protected theorem le_zero {a : Ordinal.{u}} : a ≤ 0 ↔ a = 0 :=
  ⟨fun h => Ordinal.le_antisymm h (Ordinal.zero_le a), fun h => h ▸ Ordinal.le_rfl⟩

protected theorem pos_iff_ne_zero {a : Ordinal.{u}} : 0 < a ↔ a ≠ 0 :=
  ⟨fun h e => Ordinal.lt_irrefl 0 (e ▸ h),
   fun h => Ordinal.not_le.mp fun h' => h (Ordinal.le_zero.mp h')⟩

protected theorem eq_zero_or_pos (a : Ordinal.{u}) : a = 0 ∨ 0 < a :=
  (Classical.em (a = 0)).elim .inl fun h => .inr (Ordinal.pos_iff_ne_zero.mpr h)

/-! ## Successor -/

/-- The successor `a + 1` (snu-sf: `Ord.S`). -/
def succ : Ordinal.{u} → Ordinal.{u} :=
  Quotient.lift (fun t => mk (OTree.succ t)) fun _ _ h => sound (OTree.succ_congr h)

@[simp] theorem succ_mk (t : OTree.{u}) : succ (mk t) = mk (OTree.succ t) :=
  rfl

theorem lt_succ (a : Ordinal.{u}) : a < succ a :=
  Ordinal.inductionOn a OTree.lt_succ

theorem le_succ (a : Ordinal.{u}) : a ≤ succ a :=
  Ordinal.le_of_lt (lt_succ a)

theorem succ_le_iff {a b : Ordinal.{u}} : succ a ≤ b ↔ a < b :=
  Ordinal.inductionOn₂ a b fun _ _ => OTree.succ_le_iff

theorem succ_le_of_lt {a b : Ordinal.{u}} (h : a < b) : succ a ≤ b :=
  succ_le_iff.mpr h

theorem lt_succ_iff {a b : Ordinal.{u}} : a < succ b ↔ a ≤ b :=
  Ordinal.inductionOn₂ a b fun _ _ => OTree.lt_succ_iff

theorem succ_le_succ_iff {a b : Ordinal.{u}} : succ a ≤ succ b ↔ a ≤ b :=
  Ordinal.inductionOn₂ a b fun _ _ => OTree.succ_le_succ_iff

theorem succ_lt_succ_iff {a b : Ordinal.{u}} : succ a < succ b ↔ a < b :=
  Ordinal.inductionOn₂ a b fun _ _ => OTree.succ_lt_succ_iff

theorem succ_le_succ {a b : Ordinal.{u}} (h : a ≤ b) : succ a ≤ succ b :=
  succ_le_succ_iff.mpr h

theorem succ_inj {a b : Ordinal.{u}} : succ a = succ b ↔ a = b :=
  ⟨fun h => Ordinal.le_antisymm (succ_le_succ_iff.mp (Ordinal.le_of_eq h))
      (succ_le_succ_iff.mp (Ordinal.le_of_eq h.symm)),
   fun h => h ▸ rfl⟩

theorem zero_lt_succ (a : Ordinal.{u}) : 0 < succ a :=
  Ordinal.lt_of_le_of_lt (Ordinal.zero_le a) (lt_succ a)

theorem succ_ne_zero (a : Ordinal.{u}) : succ a ≠ 0 :=
  fun h => Ordinal.not_lt_zero a (h ▸ lt_succ a)

/-- No ordinal is strictly between `a` and `succ a`. -/
theorem not_lt_of_lt_succ {a b : Ordinal.{u}} (h : b < succ a) : ¬a < b :=
  Ordinal.not_lt_of_le (lt_succ_iff.mp h)

/-! ## Suprema -/

/-- Each family of ordinals is a family of ordinals of trees. -/
theorem exists_eq_mk_comp {ι : Sort v} (f : ι → Ordinal.{u}) :
    ∃ g : ι → OTree.{u}, f = fun i => mk (g i) :=
  ⟨fun i => (f i).out, funext fun i => (mk_out (f i)).symm⟩

/-- The supremum (least upper bound) of a family (snu-sf: `Ord.join`). -/
noncomputable def sup {ι : Type u} (f : ι → Ordinal.{u}) : Ordinal.{u} :=
  mk (OTree.sup fun i => (f i).out)

theorem sup_mk {ι : Type u} (g : ι → OTree.{u}) : sup (fun i => mk (g i)) = mk (OTree.sup g) :=
  sound (OTree.sup_congr fun i => out_mk_equiv (g i))

theorem le_sup {ι : Type u} (f : ι → Ordinal.{u}) (i : ι) : f i ≤ sup f := by
  have h := OTree.le_sup (fun i => (f i).out) i
  rw [← mk_le_mk, mk_out] at h
  exact h

theorem sup_le {ι : Type u} {f : ι → Ordinal.{u}} {a : Ordinal.{u}} (h : ∀ i, f i ≤ a) :
    sup f ≤ a := by
  induction a using Ordinal.ind with
  | _ t =>
    exact OTree.sup_le fun i => by
      have := h i
      rw [← mk_out (f i), mk_le_mk] at this
      exact this

theorem sup_le_iff {ι : Type u} {f : ι → Ordinal.{u}} {a : Ordinal.{u}} :
    sup f ≤ a ↔ ∀ i, f i ≤ a :=
  ⟨fun h i => Ordinal.le_trans (le_sup f i) h, sup_le⟩

theorem lt_sup_iff {ι : Type u} {f : ι → Ordinal.{u}} {a : Ordinal.{u}} :
    a < sup f ↔ ∃ i, a < f i := by
  constructor
  · intro h
    refine Classical.byContradiction fun h' => ?_
    have : sup f ≤ a := sup_le fun i =>
      Ordinal.not_lt.mp fun hi => h' ⟨i, hi⟩
    exact Ordinal.not_le_of_lt h this
  · exact fun ⟨i, hi⟩ => Ordinal.lt_of_lt_of_le hi (le_sup f i)

theorem sup_mono {ι : Type u} {f g : ι → Ordinal.{u}} (h : ∀ i, f i ≤ g i) : sup f ≤ sup g :=
  sup_le fun i => Ordinal.le_trans (h i) (le_sup g i)

theorem sup_le_sup_of_forall_exists {ι κ : Type u} {f : ι → Ordinal.{u}} {g : κ → Ordinal.{u}}
    (h : ∀ i, ∃ j, f i ≤ g j) : sup f ≤ sup g :=
  sup_le fun i => let ⟨j, hj⟩ := h i; Ordinal.le_trans hj (le_sup g j)

theorem sup_const {ι : Type u} [Nonempty ι] (a : Ordinal.{u}) : sup (fun _ : ι => a) = a :=
  Ordinal.le_antisymm (sup_le fun _ => Ordinal.le_rfl)
    (let ⟨i⟩ := ‹Nonempty ι›; le_sup (fun _ : ι => a) i)

theorem sup_of_isEmpty {ι : Type u} (h : ι → False) (f : ι → Ordinal.{u}) : sup f = 0 :=
  Ordinal.le_zero.mp (sup_le fun i => (h i).elim)

/-! ## Strict suprema -/

/-- The strict supremum: the least ordinal above all members (snu-sf: `Ord.build`). -/
noncomputable def ssup {ι : Type u} (f : ι → Ordinal.{u}) : Ordinal.{u} :=
  mk (OTree.mk ι fun i => (f i).out)

theorem ssup_mk {ι : Type u} (g : ι → OTree.{u}) : ssup (fun i => mk (g i)) = mk (OTree.mk ι g) :=
  sound (OTree.mk_congr fun i => out_mk_equiv (g i))

theorem lt_ssup {ι : Type u} (f : ι → Ordinal.{u}) (i : ι) : f i < ssup f := by
  have h := OTree.child_lt (OTree.mk ι fun i => (f i).out) i
  rw [← mk_lt_mk, OTree.child_mk, mk_out] at h
  exact h

theorem ssup_le_iff {ι : Type u} {f : ι → Ordinal.{u}} {a : Ordinal.{u}} :
    ssup f ≤ a ↔ ∀ i, f i < a := by
  constructor
  · exact fun h i => Ordinal.lt_of_lt_of_le (lt_ssup f i) h
  · intro h
    induction a using Ordinal.ind with
    | _ t =>
      exact OTree.mk_le.mpr fun i => by
        have := h i
        rw [← mk_out (f i), mk_lt_mk] at this
        exact this

theorem ssup_le {ι : Type u} {f : ι → Ordinal.{u}} {a : Ordinal.{u}} (h : ∀ i, f i < a) :
    ssup f ≤ a :=
  ssup_le_iff.mpr h

theorem lt_ssup_iff {ι : Type u} {f : ι → Ordinal.{u}} {a : Ordinal.{u}} :
    a < ssup f ↔ ∃ i, a ≤ f i := by
  constructor
  · intro h
    refine Classical.byContradiction fun h' => ?_
    exact Ordinal.not_le_of_lt h (ssup_le fun i => Ordinal.not_le.mp fun hi => h' ⟨i, hi⟩)
  · exact fun ⟨i, hi⟩ => Ordinal.lt_of_le_of_lt hi (lt_ssup f i)

/-- snu-sf: `Ord.build_join_S`. -/
theorem ssup_eq_sup_succ {ι : Type u} (f : ι → Ordinal.{u}) : ssup f = sup fun i => succ (f i) :=
  Ordinal.le_antisymm
    (ssup_le fun i => Ordinal.lt_of_lt_of_le (lt_succ (f i)) (le_sup (fun i => succ (f i)) i))
    (sup_le fun i => succ_le_of_lt (lt_ssup f i))

theorem sup_le_ssup {ι : Type u} (f : ι → Ordinal.{u}) : sup f ≤ ssup f :=
  sup_le fun i => Ordinal.le_of_lt (lt_ssup f i)

/-- Each ordinal is the strict supremum of its predecessors. -/
theorem ssup_lt (a : Ordinal.{u}) : ssup (fun b : a.out.Index => mk (a.out.child b)) = a := by
  conv => rhs; rw [← mk_out a]
  rw [ssup_mk, OTree.eta]

theorem succ_eq_ssup (a : Ordinal.{u}) : succ a = ssup fun _ : PUnit => a :=
  Ordinal.le_antisymm (succ_le_of_lt (lt_ssup _ ⟨⟩))
    (ssup_le fun _ => lt_succ a)

/-! ## Maximum and minimum -/

instance : Max Ordinal.{u} :=
  ⟨Quotient.lift₂ (fun s t => mk (OTree.max s t)) fun _ _ _ _ hs ht =>
    sound (OTree.max_congr hs ht)⟩

@[simp] theorem max_mk (s t : OTree.{u}) : max (mk s) (mk t) = mk (OTree.max s t) :=
  rfl

protected theorem le_max_left (a b : Ordinal.{u}) : a ≤ max a b :=
  Ordinal.inductionOn₂ a b OTree.le_max_left

protected theorem le_max_right (a b : Ordinal.{u}) : b ≤ max a b :=
  Ordinal.inductionOn₂ a b OTree.le_max_right

protected theorem max_le_iff {a b c : Ordinal.{u}} : max a b ≤ c ↔ a ≤ c ∧ b ≤ c :=
  Ordinal.inductionOn₃ a b c fun _ _ _ => OTree.max_le_iff

protected theorem max_eq_right {a b : Ordinal.{u}} (h : a ≤ b) : max a b = b :=
  Ordinal.le_antisymm (Ordinal.max_le_iff.mpr ⟨h, Ordinal.le_rfl⟩) (Ordinal.le_max_right a b)

protected theorem max_eq_left {a b : Ordinal.{u}} (h : b ≤ a) : max a b = a :=
  Ordinal.le_antisymm (Ordinal.max_le_iff.mpr ⟨Ordinal.le_rfl, h⟩) (Ordinal.le_max_left a b)

instance : Std.LawfulOrderMax Ordinal.{u} where
  max_le_iff _ _ _ := Ordinal.max_le_iff
  max_eq_or a b := (Ordinal.le_total a b).elim (fun h => .inr (Ordinal.max_eq_right h))
    (fun h => .inl (Ordinal.max_eq_left h))

/-- The minimum (classical). -/
noncomputable instance : Min Ordinal.{u} :=
  ⟨fun a b => if a ≤ b then a else b⟩

protected theorem min_def (a b : Ordinal.{u}) : min a b = if a ≤ b then a else b :=
  rfl

protected theorem le_min_iff {a b c : Ordinal.{u}} : a ≤ min b c ↔ a ≤ b ∧ a ≤ c := by
  rw [Ordinal.min_def]
  split
  · next h => exact ⟨fun h' => ⟨h', Ordinal.le_trans h' h⟩, fun h' => h'.1⟩
  · next h =>
    have h := Ordinal.le_of_lt (Ordinal.not_le.mp h)
    exact ⟨fun h' => ⟨Ordinal.le_trans h' h, h'⟩, fun h' => h'.2⟩

instance : Std.LawfulOrderMin Ordinal.{u} where
  le_min_iff _ _ _ := Ordinal.le_min_iff
  min_eq_or a b := by
    rw [Ordinal.min_def]
    split
    · exact .inl rfl
    · exact .inr rfl

/-! ## Natural numbers and `ω` -/

/-- The natural number `n` as an ordinal (snu-sf: `Ord.from_nat`). -/
def ofNat (n : Nat) : Ordinal.{u} :=
  mk (OTree.ofNat n)

instance : NatCast Ordinal.{u} :=
  ⟨ofNat⟩

instance (n : Nat) : OfNat Ordinal.{u} n :=
  ⟨ofNat n⟩

instance : One Ordinal.{u} :=
  ⟨ofNat 1⟩

theorem natCast_def (n : Nat) : (n : Ordinal.{u}) = ofNat n :=
  rfl

@[simp] theorem ofNat_zero : ofNat.{u} 0 = 0 :=
  rfl

@[simp] theorem ofNat_succ (n : Nat) : ofNat.{u} (n + 1) = succ (ofNat n) :=
  rfl

theorem one_eq_succ_zero : (1 : Ordinal.{u}) = succ 0 :=
  rfl

theorem ofNat_lt_ofNat_iff {m n : Nat} : ofNat.{u} m < ofNat n ↔ m < n :=
  OTree.ofNat_lt_ofNat_iff

theorem ofNat_le_ofNat_iff {m n : Nat} : ofNat.{u} m ≤ ofNat n ↔ m ≤ n :=
  OTree.ofNat_le_ofNat_iff

theorem ofNat_inj {m n : Nat} : ofNat.{u} m = ofNat n ↔ m = n :=
  ⟨fun h => Nat.le_antisymm (ofNat_le_ofNat_iff.mp (Ordinal.le_of_eq h))
      (ofNat_le_ofNat_iff.mp (Ordinal.le_of_eq h.symm)),
   fun h => h ▸ rfl⟩

/-- The first infinite ordinal (snu-sf: `Ord.omega`). -/
def omega : Ordinal.{u} :=
  mk OTree.omega

@[inherit_doc] scoped notation "ω" => Ordinal.omega

theorem ofNat_lt_omega (n : Nat) : ofNat.{u} n < ω :=
  OTree.ofNat_lt_omega n

theorem omega_le {a : Ordinal.{u}} (h : ∀ n, ofNat n ≤ a) : ω ≤ a :=
  Ordinal.inductionOn a (motive := fun a => (∀ n, ofNat n ≤ a) → ω ≤ a)
    (fun _ h => OTree.omega_le h) h

theorem omega_le_iff {a : Ordinal.{u}} : ω ≤ a ↔ ∀ n, ofNat n ≤ a :=
  ⟨fun h n => Ordinal.le_of_lt (Ordinal.lt_of_lt_of_le (ofNat_lt_omega n) h), omega_le⟩

theorem lt_omega_iff {a : Ordinal.{u}} : a < ω ↔ ∃ n, a = ofNat n := by
  constructor
  · intro h
    refine Classical.byContradiction fun h' => ?_
    have : ω ≤ a := omega_le fun n => by
      induction n with
      | zero => exact Ordinal.zero_le a
      | succ n ih =>
        refine succ_le_of_lt (Ordinal.lt_iff_le_and_ne.mpr ⟨ih, fun e => h' ⟨n, e.symm⟩⟩)
    exact Ordinal.not_le_of_lt h this
  · rintro ⟨n, rfl⟩
    exact ofNat_lt_omega n

/-! ## Limit ordinals and case analysis -/

/-- A limit ordinal: not zero, and not a successor. -/
def IsLimit (a : Ordinal.{u}) : Prop :=
  a ≠ 0 ∧ ∀ b, b < a → succ b < a

theorem IsLimit.ne_zero {a : Ordinal.{u}} (h : IsLimit a) : a ≠ 0 :=
  h.1

theorem IsLimit.succ_lt {a b : Ordinal.{u}} (h : IsLimit a) (hb : b < a) : succ b < a :=
  h.2 b hb

theorem not_isLimit_zero : ¬IsLimit (0 : Ordinal.{u}) :=
  fun h => h.1 rfl

theorem not_isLimit_succ (a : Ordinal.{u}) : ¬IsLimit (succ a) :=
  fun h => Ordinal.lt_irrefl _ (h.2 a (lt_succ a))

theorem isLimit_omega : IsLimit (ω : Ordinal.{u}) := by
  refine ⟨Ordinal.ne_of_lt (b := ω) (ofNat_lt_omega 0) |>.symm, fun b hb => ?_⟩
  obtain ⟨n, rfl⟩ := lt_omega_iff.mp hb
  exact ofNat_lt_omega (n + 1)

theorem zero_or_succ_or_limit (a : Ordinal.{u}) :
    a = 0 ∨ (∃ b, a = succ b) ∨ IsLimit a := by
  refine (Classical.em (a = 0)).elim .inl fun h₀ => .inr ?_
  refine (Classical.em (∃ b, a = succ b)).elim .inl fun hs => .inr ⟨h₀, fun b hb => ?_⟩
  refine Ordinal.lt_iff_le_and_ne.mpr ⟨succ_le_of_lt hb, fun e => hs ⟨b, e.symm⟩⟩

/-- Induction with the three cases zero, successor and limit. -/
@[elab_as_elim]
theorem limitInduction {motive : Ordinal.{u} → Prop} (a : Ordinal.{u}) (zero : motive 0)
    (succ : ∀ b, motive b → motive (Ordinal.succ b))
    (limit : ∀ b, IsLimit b → (∀ c, c < b → motive c) → motive b) : motive a := by
  induction a using Ordinal.induction with
  | _ a ih =>
    rcases zero_or_succ_or_limit a with rfl | ⟨b, rfl⟩ | h
    · exact zero
    · exact succ b (ih b (lt_succ b))
    · exact limit a h ih

/-- A limit ordinal is the supremum of its predecessors. -/
theorem IsLimit.sup_eq {a : Ordinal.{u}} (h : IsLimit a) :
    sup (fun b : a.out.Index => mk (a.out.child b)) = a := by
  refine Ordinal.le_antisymm (sup_le fun b => Ordinal.le_of_lt ?_) ?_
  · conv => rhs; rw [← mk_out a]
    exact OTree.child_lt _ b
  · refine le_of_forall_lt fun c hc => ?_
    have hc' := h.succ_lt hc
    rw [← ssup_lt a] at hc'
    obtain ⟨b, hb⟩ := lt_ssup_iff.mp hc'
    exact lt_sup_iff.mpr ⟨b, Ordinal.lt_of_lt_of_le (lt_succ c) hb⟩

end Ordinal

end Ordinals
