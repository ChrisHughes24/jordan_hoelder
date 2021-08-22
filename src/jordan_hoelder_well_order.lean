import order.bounded_lattice
import data.finset.lattice
import tactic.ext
import data.set_like.basic
import data.fintype.basic

universe u

structure composition_series (X : Type u) [preorder X] : Type u :=
(carrier : finset X)
(total' : ∀ x y ∈ carrier, x ≤ y ∨ y ≤ x)
(saturated' : ∀ x y ∈ carrier,
  (∀ z ∈ carrier, x < z → z < y → false) → --NOOO
  ∀ z, x < z → z < y → false)
(nonempty' : carrier.nonempty)

namespace composition_series

variables {X : Type u} (isom : (X × X) → (X × X) → Prop)

instance [preorder X] : has_coe (composition_series X) (finset X) :=
⟨composition_series.carrier⟩

@[simp] def coe_finset_mk  [preorder X] (carrier total saturated nonempty) :
  ((composition_series.mk carrier total saturated nonempty : composition_series X) : finset X) =
  carrier := rfl

@[simp] def coe_set_mk  [preorder X] (carrier total saturated nonempty) :
  ((composition_series.mk carrier total saturated nonempty : composition_series X) : set X) =
  carrier := rfl

instance decidable_mem_coe [preorder X] [decidable_eq X] (s : composition_series X) :
  decidable_pred (∈ (s : set X)) :=
show decidable_pred (∈ (s : finset X)), by apply_instance

instance (X : Type u) [preorder X] : set_like (composition_series X) X :=
{ coe := λ s, s,
  coe_injective' := λ x y, by cases x; cases y; simp, }

@[simp] def mem_mk  [preorder X] (carrier total saturated nonempty) {x : X} :
  x ∈ (composition_series.mk carrier total saturated nonempty : composition_series X) ↔
  x ∈ carrier := iff.rfl

@[simp] lemma mem_coe_finset [preorder X] {s : composition_series X} {x : X} :
  x ∈ (s : finset X) ↔ x ∈ s := iff.rfl

@[simp] lemma mem_coe_set [preorder X] {s : composition_series X} {x : X} :
  x ∈ (s : set X) ↔ x ∈ s := iff.rfl

@[ext] protected lemma ext [preorder X] {s₁ s₂ : composition_series X}
  (h : ∀ x, x ∈ s₁ ↔ x ∈ s₂) : s₁ = s₂ :=
begin
  cases s₁, cases s₂,
  simpa [finset.ext_iff] using h
end

@[ext] protected lemma ext_iff [preorder X] {s₁ s₂ : composition_series X} :
   s₁ = s₂ ↔ ∀ x, x ∈ s₁ ↔ x ∈ s₂  :=
⟨λ h _, by rw h, composition_series.ext⟩

lemma total [preorder X] (s : composition_series X) {x y : X} (hx : x ∈ s)
  (hy : y ∈ s) : x ≤ y ∨ y ≤ x := s.total' _ _ hx hy

lemma saturated [preorder X] (s : composition_series X) {x y : X} (hx : x ∈ s)
  (hy : y ∈ s)
  (h : ∀ z ∈ s, x < z → z < y → false) :
  ∀ z, x < z → z < y → false :=
s.saturated' _ _ hx hy h

lemma nonempty [preorder X] (s : composition_series X) : (s : finset X).nonempty :=
s.nonempty'

def dual [preorder X] (s : composition_series X) : composition_series (order_dual X) :=
{ carrier := s.carrier,
  total' := λ x y hx hy, s.total hy hx,
  saturated' := λ x y hx hy h z hxz hzy, s.saturated hy hx
    (λ z hzs hyz hzx, h z hzs hzx hyz) z hzy hxz,
  nonempty' := s.nonempty }


-- instance [order_bot X] : order_bot (composition_series X) :=
-- { bot := ⟨∅, by simp, by simp, _⟩,
--   bot_le := λ _ x h, (finset.not_mem_empty x h).elim,
--   ..show partial_order (composition_series X), by apply_instance }

-- @[simp] def coe_finset_bot [order_bot X] : ((⊥ : composition_series X) : finset X) = ∅ := rfl
-- @[simp] def coe_set_bot [order_bot X] : ((⊥ : composition_series X) : set X) = ∅ := rfl

def top [semilattice_sup X] (s : composition_series X) : X :=
(s : finset X).sup' s.nonempty id

lemma sup_mem [semilattice_sup X] {s : composition_series X} {x y : X}
  (hx : x ∈ s) (hy : y ∈ s) : x ⊔ y ∈ s :=
(s.total hx hy).elim
  (λ hxy, (sup_eq_right.2 hxy).symm ▸ hy)
  (λ hyx, (sup_eq_left.2 hyx).symm ▸ hx)

lemma top_mem [semilattice_sup X] (s : composition_series X) : s.top ∈ s :=
finset.sup'_mem (s : set X) (λ x y, sup_mem) _ _ _ (λ _, id)

lemma le_top [semilattice_sup X] {s : composition_series X} {x : X}
  (hx : x ∈ s) : x ≤ s.top :=
finset.le_sup' _ hx

def bot [semilattice_inf X] (s : composition_series X) : X :=
(s : finset X).inf' s.nonempty id

lemma inf_mem [semilattice_inf X] {s : composition_series X} {x y : X}
  (hx : x ∈ s) (hy : y ∈ s) : x ⊓ y ∈ s :=
@sup_mem (order_dual X) _ s.dual _ _  hx hy

lemma bot_mem [semilattice_inf X] (s : composition_series X) : s.bot ∈ s :=
@top_mem (order_dual X) _ s.dual

lemma bot_le [semilattice_inf X] {s : composition_series X} {x : X}
  (hx : x ∈ s) : s.bot ≤ x :=
finset.inf'_le _ hx

@[simps] def insert [lattice X] [decidable_eq X]
  (s : composition_series X)
  (x : X)
  (hlt : ∀ y ∈ s, y < x)
  (hsat : ∀ z, s.top < z → z < x → false) :
  composition_series X :=
{ carrier := insert x (s : finset X),
  total' := λ y z hy hz, begin
    rw [finset.mem_insert] at *,
    rcases hy with rfl | hy,
    { rcases hz with rfl | hz,
      { left, refl },
      { right, exact le_of_lt (hlt _ hz) } },
    { rcases hz with rfl | hz,
      { left, exact le_of_lt (hlt _ hy) },
      { exact s.total hy hz } }
  end,
  saturated' := λ y z hy hz h k hxk hky,
  begin
    rw [finset.mem_insert] at *,
    rcases hy with rfl | hy,
    { rcases hz with rfl | hz,
      { exact not_lt_of_lt hky hxk },
      { exact not_lt_of_lt (lt_trans hxk hky) (hlt _ hz) } },
    { rcases hz with rfl | hz,
      { rcases lt_or_eq_of_le (le_top hy) with hyt | rfl,
        { exact h _ (finset.mem_insert_of_mem s.top_mem) hyt
            (hlt _ s.top_mem) },
        { exact hsat k hxk hky } },
      { exact s.saturated hy hz
          (λ z hz, h z (finset.mem_insert_of_mem hz)) _
          hxk hky } }
  end,
  nonempty' := ⟨x, finset.mem_insert_self _ _⟩ }

@[simp] lemma mem_insert [lattice X] [decidable_eq X]
  {s : composition_series X}
  {x y : X}
  {hlt : ∀ y ∈ s, y < x}
  {hsat : ∀ z, s.top < z → z < x → false} :
  y ∈ insert s x hlt hsat ↔ y = x ∨ y ∈ s :=
finset.mem_insert

def append [lattice X] [decidable_eq X] (s₁ s₂ : composition_series X)
  (htb : s₁.top = s₂.bot) : composition_series X :=
{ carrier := (s₁ : finset X) ∪ s₂,
  total' := λ x y hx hy,
    (finset.mem_union.1 hx).elim
      (λ hxs₁, (finset.mem_union.1 hy).elim
        (λ hys₁, s₁.total hxs₁ hys₁)
        (λ hys₂, or.inl $
          calc x ≤ s₁.top : le_top hxs₁
             ... = s₂.bot : htb
             ... ≤ y : bot_le hys₂))
      (λ hxs₂, (finset.mem_union.1 hy).elim
        (λ hys₁, or.inr $
          calc y ≤ s₁.top : le_top hys₁
             ... = s₂.bot : htb
             ... ≤ x : bot_le hxs₂)
        (λ hys₂, s₂.total hxs₂ hys₂)),
  saturated' := λ x y hx hy h, begin
    rw [finset.mem_union] at *,
    cases hx with hxs₁ hxs₂,
    { cases hy with hys₁ hys₂,
      { exact s₁.saturated hxs₁ hys₁ (λ z hz, h _ (finset.mem_union_left _ hz)) },
      { rcases lt_or_eq_of_le (le_top hxs₁) with hxt | rfl,
        { rcases lt_or_eq_of_le (bot_le hys₂) with hyb | rfl,
          { intros,
            exact h s₂.bot (finset.mem_union_right _ s₂.bot_mem) (htb ▸ hxt) hyb },
          { intros z hxz hzb,
            exact s₁.saturated hxs₁ s₁.top_mem
              (λ z hz, htb.symm ▸ h _ (finset.mem_union_left _ hz))
              z hxz (htb.symm ▸ hzb) } },
        { intros z htz hzy,
          exact s₂.saturated s₂.bot_mem hys₂
            (λ z hz, htb ▸ h _ (finset.mem_union_right _ hz)) z (htb ▸ htz) hzy } } },
    { cases hy with hys₁ hys₂,
      { intros z hxz hzy,
        refine lt_irrefl x _,
        calc x < z : hxz
           ... < y : hzy
           ... ≤ s₁.top : le_top hys₁
           ... = s₂.bot : htb
           ... ≤ x : bot_le hxs₂ },
      { exact s₂.saturated hxs₂ hys₂ (λ z hz, h _ (finset.mem_union_right _ hz)) } }
  end,
  nonempty' := let ⟨y, hy⟩ := s₁.nonempty in ⟨y, finset.mem_union_left _ hy⟩ }

def length [preorder X] (s : composition_series X) :=
(s : finset X).card - 1

@[simp] lemma coe_finset_append [lattice X] [decidable_eq X] (s₁ s₂ : composition_series X)
  (htb : s₁.top = s₂.bot) : (append s₁ s₂ htb : finset X) = s₁ ∪ s₂ := rfl

instance [preorder X] : has_singleton X (composition_series X) :=
⟨λ x : X,
  { carrier := {x},
    total' := by simp {contextual := tt},
    saturated' := by simp [lt_iff_le_not_le] {contextual := tt},
    nonempty' := by simp }⟩

@[simp] lemma mem_singleton_iff [preorder X] {x y} :
  x ∈ ({y} : composition_series X) ↔ x = y :=
finset.mem_singleton

lemma inter_eq_single_of_top_eq_bot [lattice X] [decidable_eq X]
  {s₁ s₂ : composition_series X}
  (htb : s₁.top = s₂.bot) : (s₁ ∩ s₂ : finset X) = {s₁.top} :=
suffices ∀ (a : X), a ∈ ↑s₁ ∧ a ∈ ↑s₂ ↔ a = s₁.top, by simpa [finset.ext_iff],
begin
  intros a,
  split,
  { rintros ⟨has₁, has₂⟩,
    exact le_antisymm (le_top has₁) (htb.symm ▸ bot_le has₂) },
  { intro h,
    exact h.symm ▸ ⟨top_mem _, htb.symm ▸ bot_mem _⟩ }
end

@[simp] lemma length_append [lattice X] [decidable_eq X] (s₁ s₂ : composition_series X)
  (htb : s₁.top = s₂.bot) : (append s₁ s₂ htb).length = s₁.length + s₂.length :=
have (s₁ : finset X).card + (s₂ : finset X).card =
    (s₁ ∪ s₂ : finset X).card + 1,
  by rw [← finset.card_union_add_card_inter, inter_eq_single_of_top_eq_bot htb,
      finset.card_singleton],
by rw [length, nat.sub_eq_iff_eq_add (finset.card_pos.2 (s₁.append s₂ htb).nonempty),
    length, length, add_assoc, nat.sub_add_cancel (finset.card_pos.2 s₂.nonempty),
    coe_finset_append, ← @add_right_cancel_iff _ _ 1, ← this, add_assoc, add_left_comm,
    nat.sub_add_cancel (finset.card_pos.2 s₁.nonempty), add_comm]

def erase_top [lattice X] [decidable_eq X] (s : composition_series X)
  (hs : 0 < s.length ) : composition_series X :=
{ carrier := (s : finset X).erase s.top,
  total' := λ x y, begin
    simp only [finset.mem_erase, and_imp],
    intros,
    apply s.total;
    assumption
  end,
  saturated' := λ x y, begin
    simp only [finset.mem_erase, and_imp, mem_coe_finset],
    intros _ hxs _ hys h,
    refine s.saturated hxs hys _,
    intros z hzs hxs hzy,
    refine h z _ hzs hxs hzy,
    exact ne_of_lt (lt_of_lt_of_le hzy (le_top hys))
  end,
  nonempty' := finset.card_pos.1 (lt_of_lt_of_le hs finset.pred_card_le_card_erase) }

lemma lt_top_of_mem_erase_top [lattice X] [decidable_eq X]
  {s : composition_series X} (h : 0 < s.length) {x : X}
  (hx : x ∈ erase_top s h) : x < s.top :=
lt_of_le_of_ne (le_top (finset.mem_erase.1 hx).2) (finset.mem_erase.1 hx).1

lemma erase_top_top_mem [lattice X] [decidable_eq X]
  {s : composition_series X} (h : 0 < s.length) :
  (s.erase_top h).top ∈ s :=
finset.mem_of_mem_erase (top_mem (s.erase_top h))

lemma erase_top_is_succ [lattice X] [decidable_eq X]
  {s : composition_series X} (h : 0 < s.length) {x : X} :
  (erase_top s h).top < x → x < s.top → false :=
s.saturated (erase_top_top_mem h) s.top_mem
  begin
    intros z hz htz hzt,
    have : z ∈ s.erase_top h, from finset.mem_erase_of_ne_of_mem (ne_of_lt hzt) hz,
    exact not_le_of_gt htz (le_top this)
  end _

@[simp] lemma insert_erase_top [lattice X] [decidable_eq X]
  {s : composition_series X} (h : 0 < s.length) :
  insert (erase_top s h) s.top (λ x, lt_top_of_mem_erase_top h)
    (λ x, erase_top_is_succ h) = s :=
begin
  ext x,
  simp [erase_top, insert],
  by_cases hx : x = s.top;
  simp [*, s.top_mem]
end

lemma finset.card_eq_one_iff_of_mem {X : Type*} {s : finset X} {x : X} (hx : x ∈ s):
  s.card = 1 ↔ s = {x} :=
begin
  split,
  { assume h,
    rw [finset.eq_singleton_iff_unique_mem],
    exact ⟨hx, λ y hy, finset.card_le_one_iff.1 (le_of_eq h) hy hx⟩ },
  { rintros rfl; simp }

end

@[simp] lemma length_eq_zero_iff_eq_single [lattice X] {s : composition_series X} :
  s.length = 0 ↔ s = ({s.top} : composition_series X) :=
begin
  rw [length, nat.sub_eq_iff_eq_add (finset.card_pos.2 s.nonempty), zero_add,
    finset.card_eq_one_iff_of_mem (show s.top ∈ (s : finset X), from s.top_mem)],
  simp [composition_series.ext_iff, finset.ext_iff]
end

lemma bot_eq_top_iff_eq_single [bounded_lattice X] {s : composition_series X} :
  s.bot = s.top ↔ s = {s.top} :=
begin
  simp only [composition_series.ext_iff, mem_singleton_iff],
  split,
  { intros h x,
    split,
    { intro hxs,
      exact le_antisymm (le_top hxs) (h ▸ bot_le hxs) },
    { intro hxt,
      exact hxt.symm ▸ s.top_mem } },
  { intro h,
    rw ← h,
    exact bot_mem _ }
end

section

variable [preorder X]

open_locale classical

noncomputable def succ (s : composition_series X) (x : X) : X :=
if h : ∃ y ∈ s, x < y ∧ ∀ z ∈ s, x < z → y ≤ z
then classical.some h
else x

def eqv (s₁ s₂ : composition_series X) : Prop :=
∃ f : s₁ ≃ s₂, ∀ x : s₁, isom ((x : X), s₁.succ x) (f x, s₂.succ (f x))

end

namespace eqv

section

variable [preorder X]

@[refl] protected def refl [is_refl _ isom] (s : composition_series X) : eqv isom s s :=
⟨equiv.refl _, λ _, is_refl.refl _⟩

@[symm] protected def symm [is_symm _ isom] {s₁ s₂ : composition_series X}
  (h : eqv isom s₁ s₂) : eqv isom s₂ s₁ :=
let ⟨f, hf⟩ := h in ⟨f.symm, λ x, is_symm.symm _ _ $ by simpa using hf (f.symm x)⟩

@[trans] protected def trans [is_trans _ isom] {s₁ s₂ s₃ : composition_series X}
  (h₁ : eqv isom s₁ s₂) (h₂ : eqv isom s₂ s₃) : eqv isom s₁ s₃ :=
let ⟨f, hf⟩ := h₁, ⟨g, hg⟩ := h₂ in
⟨f.trans g, λ x, is_trans.trans _ _ _ (hf _) (hg _)⟩

lemma card_eq {s₁ s₂ : composition_series X} (h : eqv isom s₁ s₂) :
  finset.card (s₁ : finset X) = finset.card (s₂ : finset X) :=
let ⟨f, hf⟩ := h in
begin
  rw [← fintype.card_of_finset (s₁ : finset X) (λ _, iff.rfl),
      ← fintype.card_of_finset (s₂ : finset X) (λ _, iff.rfl)],
  exact @fintype.card_congr _ _ (id _) (id _) f
end

lemma length_eq
  {s₁ s₂ : composition_series X} (h : eqv isom s₁ s₂) :
  s₁.length = s₂.length :=
by rw [length, card_eq _ h, length]

end

lemma insert [lattice X] [decidable_eq X]
  {s₁ s₂ : composition_series X}
  (x : X)
  (hlt₁ hsat₁ hlt₂ hsat₂)
  (heqv : eqv isom s₁ s₂) :
  eqv isom (insert s₁ x hlt₁ hsat₁) (insert s₂ x hlt₂ hsat₂) :=
let ⟨f, hf⟩ := heqv in
let e : ↥(has_insert.insert x (s₁ : finset X)) ≃ ↥(has_insert.insert x (s₂ : finset X)) :=
  calc ↥(has_insert.insert x (s₁ : finset X)) ≃ ↥(has_insert.insert x (s₁ : set X)) :
    equiv.set.of_eq (finset.coe_insert x s₁)
  ... ≃ (s₁ : set X) ⊕ punit.{u + 1} : @equiv.set.insert X s₁ _ x
    (λ h, lt_irrefl x (hlt₁ _ h))
  ... ≃ (s₂ : set X) ⊕ punit.{u+1} : equiv.sum_congr f (equiv.refl _)
  ... ≃ ↥(has_insert.insert x (s₂ : set X)) : (@equiv.set.insert X s₂ _ x (λ h, lt_irrefl x (hlt₂ _ h))).symm
  ... ≃ ↥(has_insert.insert x (s₂ : finset X)) : equiv.set.of_eq (finset.coe_insert x s₂).symm in
begin
  use e,
  rintros ⟨y, hy⟩,
  change y ∈ insert s₁ x hlt₁ hsat₁ at hy,
  clear_aux_decl,
  rcases mem_insert.1 hy with rfl | h,

end

end eqv

end

variables [bounded_lattice X] [is_equiv _ isom]

lemma jordan_hoelder
  (s₁ s₂ : composition_series X)
  (hinf : s₁.bot = s₂.bot)
  (hsup : s₁.top = s₂.top) :
  eqv isom s₁ s₂ :=
begin
  classical,
  induction hs₁ : s₁.length with n hn generalizing s₁ s₂,
  { suffices : s₁ = s₂, rw this,
    rw [length_eq_zero_iff_eq_single] at hs₁,
    rw [hs₁],
    rw [← bot_eq_top_iff_eq_single] at hs₁,
    rw [bot_eq_top_iff_eq_single.1 (show s₂.bot = s₂.top, by cc)],
    congr,
    cc },
  { have h0s₁ : 0 < s₁.length, from hs₁.symm ▸ nat.succ_pos _,
    have h0s₂ : 0 < s₂.length, from nat.pos_of_ne_zero
      (by rw [ne.def, length_eq_zero_iff_eq_single]; admit),
    by_cases h : (s₁.erase_top h0s₁).top = (s₂.erase_top h0s₂).top,
    {  }  }

end

end composition_series