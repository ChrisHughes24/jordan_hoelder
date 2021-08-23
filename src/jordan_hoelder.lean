import order.bounded_lattice
import data.set.intervals.basic
import data.fin
import .fin
import data.set_like.basic
import data.list.sort
import data.equiv.fin
import data.equiv.option

universe u

open set

class jordan_hoelder_class (X : Type u) [lattice X] :=
(is_maximal : X → X → Prop)
(lt_of_is_maximal : ∀ {x y}, is_maximal x y → x < y)
(sup_eq_of_is_maximal : ∀ {x y z}, is_maximal x z → is_maximal y z →
  x ≠ y → x ⊔ y = z)
(is_maximal_inf : ∀ {x y z}, is_maximal x z → is_maximal y z → x ≠ y →
  is_maximal (x ⊓ y) y)
(isom : (X × X) → (X × X) → Prop)
(isom_refl : ∀ x, isom x x)
(isom_symm : ∀ {x y}, isom x y → isom y x)
(isom_trans : ∀ {x y z}, isom x y → isom y z → isom x z)
(second_iso : ∀ x y, isom (y, x ⊔ y) (x ⊓ y, x))

open jordan_hoelder_class

attribute [refl] isom_refl
attribute [symm] isom_symm
attribute [trans] isom_trans

structure composition_series (X : Type u) [lattice X] [jordan_hoelder_class X] : Type u :=
(length : ℕ)
(series : fin length.succ → X)
(step' : ∀ i : fin length, is_maximal (series i.cast_succ) (series i.succ))

namespace composition_series

variables {X : Type u} [lattice X] [jordan_hoelder_class X]

instance : has_coe_to_fun (composition_series X) :=
{ F := _, coe := composition_series.series }

variables {X}

lemma step (s : composition_series X) : ∀ i : fin s.length,
  is_maximal (s i.cast_succ) (s i.succ) := s.step'

@[simp] lemma coe_fn_mk (length : ℕ) (series step) :
  (@composition_series.mk X _ _ length series step : fin length.succ → X) = series := rfl

theorem lt_succ (s : composition_series X) (i : fin s.length) :
  s i.cast_succ < s i.succ :=
lt_of_is_maximal (s.step _)

protected theorem strict_mono (s : composition_series X) : strict_mono s :=
fin.strict_mono_iff_lt_succ.2 (λ i h, s.lt_succ ⟨i, nat.lt_of_succ_lt_succ h⟩)

protected theorem injective (s : composition_series X) : function.injective s :=
s.strict_mono.injective

@[simp] protected theorem inj (s : composition_series X) {i j : fin s.length.succ} :
  s i = s j ↔ i = j :=
s.injective.eq_iff

instance : has_mem X (composition_series X) :=
⟨λ x s, x ∈ set.range s⟩

lemma mem_def {x : X} {s : composition_series X} : x ∈ s ↔ x ∈ set.range s := iff.rfl

lemma total {s : composition_series X} {x y : X} (hx : x ∈ s) (hy : y ∈ s) : x ≤ y ∨ y ≤ x :=
begin
  rcases set.mem_range.1 hx with ⟨i, rfl⟩,
  rcases set.mem_range.1 hy with ⟨j, rfl⟩,
  rw [s.strict_mono.le_iff_le, s.strict_mono.le_iff_le],
  exact le_total i j
end

def to_list (s : composition_series X) : list X := list.of_fn s

lemma ext_fun {s₁ s₂ : composition_series X}
  (hl : s₁.length = s₂.length)
  (h : ∀ i, s₁ i = s₂ (fin.cast (congr_arg nat.succ hl) i)) :
  s₁ = s₂ :=
begin
  cases s₁, cases s₂,
  dsimp at *,
  subst hl,
  simpa [function.funext_iff] using h
end

lemma length_to_list (s : composition_series X) : s.to_list.length = s.length.succ :=
by rw [to_list, list.length_of_fn]

lemma to_list_injective : function.injective (@composition_series.to_list X _ _) :=
λ s₁ s₂ (h : list.of_fn s₁ = list.of_fn s₂),
have h₁ : s₁.length = s₂.length,
  from nat.succ_injective
    ((list.length_of_fn s₁).symm.trans $
      (congr_arg list.length h).trans $
      list.length_of_fn s₂),
have h₂ : ∀ i : fin s₁.length.succ, (s₁ i) = s₂ (fin.cast (congr_arg nat.succ h₁) i),
  begin
    assume i,
    rw [← list.nth_le_of_fn s₁ i, ← list.nth_le_of_fn s₂],
    simp [h]
  end,
begin
  cases s₁, cases s₂,
  dsimp at *,
  subst h₁,
  simp only [heq_iff_eq, eq_self_iff_true, true_and],
  simp only [fin.cast_refl] at h₂,
  exact funext h₂
end

lemma to_list_sorted (s : composition_series X) : s.to_list.sorted (<) :=
list.pairwise_iff_nth_le.2 (λ i j hi hij,
  begin
    dsimp [to_list],
    rw [list.nth_le_of_fn', list.nth_le_of_fn'],
    exact s.strict_mono hij
  end)

lemma to_list_nodup (s : composition_series X) : s.to_list.nodup :=
list.nodup_iff_nth_le_inj.2
  (λ i j hi hj,
    begin
      delta to_list,
      rw [list.nth_le_of_fn', list.nth_le_of_fn', s.injective.eq_iff, fin.ext_iff, fin.coe_mk, fin.coe_mk],
      exact id
    end)

@[simp] lemma mem_to_list {s : composition_series X} {x : X} : x ∈ s.to_list ↔ x ∈ s :=
begin
  rw [to_list, list.mem_of_fn],
  refl
end

@[ext] lemma ext {s₁ s₂ : composition_series X} (h : ∀ x, x ∈ s₁ ↔ x ∈ s₂) : s₁ = s₂ :=
to_list_injective $ list.eq_of_perm_of_sorted
  (by classical; exact list.perm_of_nodup_nodup_to_finset_eq
    s₁.to_list_nodup
    s₂.to_list_nodup
    (finset.ext $ by simp *))
  s₁.to_list_sorted s₂.to_list_sorted

def top (s : composition_series X) : X := s (fin.last _)

lemma top_mem (s : composition_series X) : s.top ∈ s :=
mem_def.2 (set.mem_range.2 ⟨fin.last _, rfl⟩)

lemma le_top {s : composition_series X} {x : X} (hx : x ∈ s) : x ≤ s.top :=
let ⟨i, hi⟩ := set.mem_range.1 hx in hi ▸ s.strict_mono.monotone (fin.le_last _)

def bot (s : composition_series X) : X := s 0

lemma bot_mem (s : composition_series X) : s.bot ∈ s :=
mem_def.2 (set.mem_range.2 ⟨0, rfl⟩)

lemma bot_le {s : composition_series X} {x : X} (hx : x ∈ s) : s.bot ≤ x :=
let ⟨i, hi⟩ := set.mem_range.1 hx in hi ▸ s.strict_mono.monotone (fin.zero_le _)

instance : set_like (composition_series X) X :=
{ coe := λ s, set.range s,
  coe_injective' := λ s₁ s₂ h, ext $ λ x, begin
    dsimp at h,
    rw [mem_def, mem_def, h]
  end }

@[simps] def erase_top (s : composition_series X) : composition_series X :=
{ length := s.length - 1,
  series := λ i, s ⟨i, lt_of_lt_of_le i.2 (nat.succ_le_succ (nat.sub_le_self _ _))⟩,
  step' := λ i, begin
    have := s.step ⟨i, lt_of_lt_of_le i.2 (nat.sub_le_self _ _)⟩,
    cases i,
    exact this
  end }

lemma top_erase_top (s : composition_series X) :
  s.erase_top.top = s ⟨s.length - 1, lt_of_le_of_lt (nat.sub_le_self _ _) (nat.lt_succ_self _)⟩ :=
show s _ = s _, from congr_arg s
begin
  ext,
  simp only [erase_top_length, fin.coe_last, fin.coe_cast_succ, fin.coe_of_nat_eq_mod,
    fin.coe_mk, coe_coe]
end

@[simp] lemma bot_erase_top (s : composition_series X) : s.erase_top.bot = s.bot := rfl

lemma length_pos_of_mem_ne {s : composition_series X}
  {x y : X} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) :
  0 < s.length :=
let ⟨i, hi⟩ := hx, ⟨j, hj⟩ := hy in
have hij : i ≠ j, from mt s.inj.2 $ λ h, hxy (hi ▸ hj ▸ h),
hij.lt_or_lt.elim
  (λ hij, (lt_of_le_of_lt (zero_le i)
    (lt_of_lt_of_le hij (nat.le_of_lt_succ j.2))))
  (λ hji, (lt_of_le_of_lt (zero_le j)
    (lt_of_lt_of_le hji (nat.le_of_lt_succ i.2))))

lemma forall_mem_eq_of_length_eq_zero {s : composition_series X}
  (hs : s.length = 0) {x y} (hx : x ∈ s) (hy : y ∈ s) : x = y :=
by_contradiction (λ hxy, pos_iff_ne_zero.1 (length_pos_of_mem_ne hx hy hxy) hs)

lemma mem_erase_top_of_ne_of_mem {s : composition_series X} {x : X}
  (hx : x ≠ s.top) (hxs : x ∈ s) : x ∈ s.erase_top :=
begin
  { rcases hxs with ⟨i, rfl⟩,
    have hi : (i : ℕ) < (s.length - 1).succ,
    { conv_rhs { rw [← nat.succ_sub (length_pos_of_mem_ne ⟨i, rfl⟩ s.top_mem hx),
        nat.succ_sub_one] },
      exact lt_of_le_of_ne
        (nat.le_of_lt_succ i.2)
        (by simpa [top, s.inj, fin.ext_iff] using hx) },
    refine ⟨i.cast_succ, _⟩,
    simp [fin.ext_iff, nat.mod_eq_of_lt hi] }
end

lemma erase_top_le (s : composition_series X) : s.erase_top ≤ s :=
begin
  rintros x ⟨i, rfl⟩,
  simp [mem_def],
end

lemma mem_erase_top {s : composition_series X} {x : X}
  (h : 0 < s.length) : x ∈ s.erase_top ↔ x ≠ s.top ∧ x ∈ s :=
begin
  simp only [mem_def],
  dsimp only [erase_top, coe_fn_mk],
  split,
  { rintros ⟨i, rfl⟩,
    have hi : (i : ℕ) < s.length,
    { conv_rhs { rw [← nat.succ_sub_one s.length, nat.succ_sub h] },
      exact i.2 },
    simp [top, fin.ext_iff, (ne_of_lt hi)] },
  { intro h,
    exact mem_erase_top_of_ne_of_mem h.1 h.2 }
end

lemma lt_top_of_mem_erase_top
  {s : composition_series X} {x : X}
  (h : 0 < s.length)
  (hx : x ∈ s.erase_top) :
  x < s.top :=
lt_of_le_of_ne
  (le_top ((mem_erase_top h).1 hx).2)
  ((mem_erase_top h).1 hx).1

lemma is_maximal_erase_top_top {s : composition_series X} (h : 0 < s.length) :
  is_maximal s.erase_top.top s.top :=
have s.length - 1 + 1 = s.length,
  by conv_rhs { rw [← nat.succ_sub_one s.length] }; rw nat.succ_sub h,
begin
  rw [top_erase_top, top],
  convert s.step ⟨s.length - 1, nat.sub_lt h zero_lt_one⟩;
  ext; simp [this]
end

lemma append_cast_add_aux
  {s₁ s₂ : composition_series X}
  (h : s₁ (fin.last _) = s₂ 0)
  (i : fin s₁.length) :
  fin.append (nat.add_succ _ _).symm (s₁ ∘ fin.cast_succ) s₂
  (fin.cast_add s₂.length i).cast_succ = s₁ i.cast_succ :=
by { cases i, simp [fin.append, *] }

lemma append_succ_cast_add_aux
  {s₁ s₂ : composition_series X}
  (h : s₁ (fin.last _) = s₂ 0)
  (i : fin s₁.length) :
  fin.append (nat.add_succ _ _).symm (s₁ ∘ fin.cast_succ) s₂
  (fin.cast_add s₂.length i).succ = s₁ i.succ :=
begin
  cases i with i hi,
  simp only [fin.append, hi, fin.succ_mk, function.comp_app, fin.cast_succ_mk,
    fin.coe_mk, fin.cast_add_mk],
  split_ifs,
  { refl },
  { have : i + 1 = s₁.length, from le_antisymm hi (le_of_not_gt h_1),
    calc s₂ ⟨i + 1 - s₁.length, by simp [this]⟩
        = s₂ 0 : congr_arg s₂ (by simp [fin.ext_iff, this])
    ... = s₁ (fin.last _) : h.symm
    ... = _ : congr_arg s₁ (by simp [fin.ext_iff, this]) }
end

lemma append_cast_add_right_aux
  {s₁ s₂ : composition_series X}
  (h : s₁ (fin.last _) = s₂ 0)
  (i : fin s₂.length) :
  fin.append (nat.add_succ _ _).symm (s₁ ∘ fin.cast_succ) s₂
  (fin.cast_add_right s₁.length i).cast_succ = s₂ i.cast_succ :=
by { cases i, simp [fin.append, *] }

lemma append_succ_cast_add_right_aux
  {s₁ s₂ : composition_series X}
  (h : s₁ (fin.last _) = s₂ 0)
  (i : fin s₂.length) :
  fin.append (nat.add_succ _ _).symm (s₁ ∘ fin.cast_succ) s₂
  (fin.cast_add_right s₁.length i).succ = s₂ i.succ :=
begin
  cases i with i hi,
  simp [fin.append, add_assoc]
end

@[simps length] def append {s₁ s₂ : composition_series X}
  (h : s₁.top = s₂.bot) :
  composition_series X :=
{ length := s₁.length + s₂.length,
  series := fin.append (nat.add_succ _ _).symm (s₁ ∘ fin.cast_succ) s₂,
  step' := λ i, begin
    refine fin.add_cases  _ _ i,
    { intro i,
      rw [append_succ_cast_add_aux h, append_cast_add_aux h],
      exact s₁.step i },
    { intro i,
      rw [append_cast_add_right_aux h, append_succ_cast_add_right_aux h],
      exact s₂.step i }
  end }

@[simp] lemma append_cast_add
  {s₁ s₂ : composition_series X}
  (h : s₁.top = s₂.bot)
  (i : fin s₁.length) :
  append h (fin.cast_add s₂.length i).cast_succ = s₁ i.cast_succ :=
append_cast_add_aux h i

@[simp] lemma append_succ_cast_add
  {s₁ s₂ : composition_series X}
  (h : s₁.top = s₂.bot)
  (i : fin s₁.length) :
  append h (fin.cast_add s₂.length i).succ = s₁ i.succ :=
append_succ_cast_add_aux h i

@[simp] lemma append_cast_add_right
  {s₁ s₂ : composition_series X}
  (h : s₁.top = s₂.bot)
  (i : fin s₂.length) :
  append h (fin.cast_add_right s₁.length i).cast_succ = s₂ i.cast_succ :=
append_cast_add_right_aux h i

@[simp] lemma append_succ_cast_add_right
  {s₁ s₂ : composition_series X}
  (h : s₁.top = s₂.bot)
  (i : fin s₂.length) :
  append h (fin.cast_add_right s₁.length i).succ = s₂ i.succ :=
append_succ_cast_add_right_aux h i

@[simps] def insert
  (s : composition_series X)
  (x : X)
  (hsat : is_maximal s.top x) :
  composition_series X :=
{ length := s.length + 1,
  series := fin.snoc s x,
  step' := λ i, begin
    refine fin.last_cases _ _ i,
    { rwa [fin.snoc_cast_succ, fin.succ_last, fin.snoc_last, ← top] },
    { intro i,
      rw [fin.snoc_cast_succ, ← fin.cast_succ_fin_succ, fin.snoc_cast_succ],
      exact s.step _ }
  end }

-- @[simp] lemma insert_series'
--   (s : composition_series X)
--   (x : X)
--   (hlt : ∀ y ∈ s, y < x)
--   (hsat : is_maximal s.top x) :
--   @eq (fin (s.length + 2) → X) (insert s x hlt hsat) (fin.snoc s x) :=
-- rfl

@[simp] lemma top_insert
  (s : composition_series X)
  (x : X)
  (hsat : is_maximal s.top x) :
  (insert s x hsat).top = x :=
fin.snoc_last _ _

@[simp] lemma insert_last
  (s : composition_series X)
  (x : X)
  (hsat : is_maximal s.top x) :
  insert s x hsat (fin.last _) = x :=
fin.snoc_last _ _

@[simp] lemma insert_cast_succ
  (s : composition_series X)
  (x : X)
  (hsat : is_maximal s.top x) (i : fin (s.length + 1)) :
  insert s x hsat (i.cast_succ) = s i :=
fin.snoc_cast_succ _ _ _

@[simp] lemma bot_insert
  (s : composition_series X)
  (x : X)
  (hsat : is_maximal s.top x) :
  (insert s x hsat).bot = s.bot :=
by rw [bot, bot, ← fin.cast_succ_zero, insert_cast_succ]

lemma mem_insert
  {s : composition_series X}
  {x y: X}
  {hsat : is_maximal s.top x} :
  y ∈ insert s x hsat ↔ y ∈ s ∨ y = x :=
begin
  simp only [insert, mem_def],
  split,
  { rintros ⟨i, rfl⟩,
    refine fin.last_cases _ (λ i, _) i,
    { right, simp },
    { left, simp } },
  { intro h,
    rcases h with ⟨i, rfl⟩ | rfl,
    { use i.cast_succ, simp },
    { use (fin.last _), simp } }
end

lemma eq_insert_erase_top
  {s : composition_series X}
  (h : 0 < s.length) :
  s = insert (erase_top s) s.top
    (is_maximal_erase_top_top h) :=
begin
  ext x,
  simp [mem_insert, mem_erase_top h],
  by_cases h : x = s.top; simp [*, s.top_mem]
end

@[simp] lemma insert_erase_top_top {s : composition_series X}
  (h : is_maximal s.erase_top.top s.top) :
  s.erase_top.insert s.top h = s :=
have h : 0 < s.length,
  from nat.pos_of_ne_zero begin
    assume hs,
    refine ne_of_gt (lt_of_is_maximal h) _,
    simp [top, fin.ext_iff, hs]
  end,
(eq_insert_erase_top h).symm

def equivalent (s₁ s₂ : composition_series X) : Prop :=
∃ f : fin s₁.length ≃ fin s₂.length,
  ∀ i : fin s₁.length,
    isom (s₁ i.cast_succ, s₁ i.succ)
    (s₂ (f i).cast_succ, s₂ (f i).succ)

namespace equivalent

@[refl] lemma refl (s : composition_series X) : equivalent s s :=
⟨equiv.refl _, λ _, isom_refl _⟩

@[symm] lemma symm {s₁ s₂ : composition_series X} (h : equivalent s₁ s₂) :
  equivalent s₂ s₁ :=
⟨h.some.symm, λ i, isom_symm (by simpa using h.some_spec (h.some.symm i))⟩

@[trans] lemma trans {s₁ s₂ s₃ : composition_series X}
  (h₁ : equivalent s₁ s₂)
  (h₂ : equivalent s₂ s₃) :
  equivalent s₁ s₃ :=
⟨h₁.some.trans h₂.some, λ i, isom_trans (h₁.some_spec i) (h₂.some_spec (h₁.some i))⟩

def append
  {s₁ s₂ t₁ t₂ : composition_series X}
  (hs : s₁.top = s₂.bot)
  (ht : t₁.top = t₂.bot)
  (h₁ : equivalent s₁ t₁)
  (h₂ : equivalent s₂ t₂) :
  equivalent (append hs) (append ht) :=
let e : fin (s₁.length + s₂.length) ≃ fin (t₁.length + t₂.length) :=
  calc fin (s₁.length + s₂.length) ≃ fin s₁.length ⊕ fin s₂.length : fin_sum_fin_equiv.symm
  ... ≃ fin t₁.length ⊕ fin t₂.length : equiv.sum_congr h₁.some h₂.some
  ... ≃ fin (t₁.length + t₂.length) : fin_sum_fin_equiv in
⟨e, begin
  assume i,
  refine fin.add_cases _ _ i,
  { assume i,
    simpa [top, bot] using h₁.some_spec i },
  { assume i,
    simpa [top, bot] using h₂.some_spec i }
end⟩

lemma fin.succ_cast_succ {n : ℕ} (i : fin n) :
  i.cast_succ.succ = i.succ.cast_succ :=
fin.ext (by simp)

protected lemma insert
  {s₁ s₂ : composition_series X}
  {x₁ x₂ : X}
  {hsat₁ : is_maximal s₁.top x₁}
  {hsat₂ : is_maximal s₂.top x₂}
  (hequiv : equivalent s₁ s₂)
  (htop : isom (s₁.top, x₁) (s₂.top, x₂)) :
  equivalent (s₁.insert x₁ hsat₁) (s₂.insert x₂ hsat₂) :=
let e : fin s₁.length.succ ≃ fin s₂.length.succ :=
  calc fin (s₁.length + 1) ≃ option (fin s₁.length) : fin_succ_equiv_last
  ... ≃ option (fin s₂.length) : functor.map_equiv option hequiv.some
  ... ≃ fin (s₂.length + 1) : fin_succ_equiv_last.symm in
⟨e,  λ i, begin
  refine fin.last_cases _ _ i,
  { simpa [top] using htop },
  { assume i,
    simpa [fin.succ_cast_succ] using hequiv.some_spec i }
end⟩

variables {α β : Type*} (e : α ≃ β)

def swap_top_two_fin {m n : ℕ} (e : fin m ≃ fin n) : fin (m + 2) ≃ fin (n + 2) :=
calc fin (m + 2)
    ≃ fin m ⊕ fin 2 : fin_sum_fin_equiv.symm
... ≃ fin n ⊕ fin 2 : equiv.sum_congr e (equiv.swap 0 1)
... ≃ fin (n + 2) : fin_sum_fin_equiv

@[simp] lemma swap_top_two_fin_last {m n : ℕ} (e : fin m ≃ fin n) :
  swap_top_two_fin e (fin.last _) = fin.cast_succ (fin.last _) :=
by simp [swap_top_two_fin, fin.ext_iff]

@[simp] lemma swap_top_two_fin_cast_succ_last {m n : ℕ} (e : fin m ≃ fin n) :
  swap_top_two_fin e (fin.cast_succ (fin.last _)) = fin.last _ :=
by simp [swap_top_two_fin, fin.ext_iff]

@[simp] lemma swap_top_two_fin_cast_succ_cast_succ {m n : ℕ} (e : fin m ≃ fin n) (i : fin m) :
  swap_top_two_fin e i.cast_succ.cast_succ = (e i).cast_succ.cast_succ :=
have ∀ {m : ℕ} {i : fin m}, i.cast_succ.cast_succ = fin.cast_add 2 i := λ _ _, fin.ext rfl,
by simp [swap_top_two_fin, this]

lemma insert_insert_swap
  {s₁ s₂ : composition_series X}
  {x₁ x₂ y₁ y₂ : X}
  {hsat₁ : is_maximal s₁.top x₁}
  {hsat₂ : is_maximal s₂.top x₂}
  {hsaty₁ : is_maximal (insert s₁ x₁ hsat₁).top y₁}
  {hsaty₂ : is_maximal (insert s₂ x₂ hsat₂).top y₂}
  (hequiv : equivalent s₁ s₂)
  (hr₁ : isom (s₁.top, x₁) (x₂, y₂))
  (hr₂ : isom (x₁, y₁) (s₂.top, x₂)) :
  equivalent
    (insert (insert s₁ x₁ hsat₁) y₁ hsaty₁)
    (insert (insert s₂ x₂ hsat₂) y₂ hsaty₂) :=
let e : fin (s₁.length + 1 + 1) ≃ fin (s₂.length + 1 + 1) :=
swap_top_two_fin hequiv.some in
⟨e, begin
  intro i,
  dsimp only [e],
  refine fin.last_cases _ (λ i, _) i,
  { erw [swap_top_two_fin_last, insert_cast_succ, insert_last, fin.succ_last, insert_last,
      insert_cast_succ, insert_cast_succ, fin.succ_cast_succ, insert_cast_succ,
      fin.succ_last, insert_last],
    exact hr₂ },
  { refine fin.last_cases _ (λ i, _) i,
    { erw [swap_top_two_fin_cast_succ_last, insert_cast_succ, insert_cast_succ,
        insert_cast_succ, fin.succ_cast_succ, insert_cast_succ,
        fin.succ_last, insert_last, insert_last, fin.succ_last, insert_last],
      exact hr₁ },
    { erw [swap_top_two_fin_cast_succ_cast_succ, insert_cast_succ, insert_cast_succ,
        insert_cast_succ, insert_cast_succ, fin.succ_cast_succ, insert_cast_succ,
        fin.succ_cast_succ, insert_cast_succ, fin.succ_cast_succ, insert_cast_succ,
        fin.succ_cast_succ, insert_cast_succ],
      exact hequiv.some_spec i } }
end⟩

lemma length_eq {s₁ s₂ : composition_series X} (h : equivalent s₁ s₂) : s₁.length = s₂.length :=
by simpa using fintype.card_congr h.some

end equivalent

lemma length_eq_zero_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero
  {s₁ s₂ : composition_series X}
  (hb : s₁.bot = s₂.bot) (ht : s₁.top = s₂.top)
  (hs₁ : s₁.length = 0) : s₂.length = 0 :=
begin
  have : s₁.bot = s₁.top,
    from congr_arg s₁ (fin.ext (by simp [hs₁])),
  have : (fin.last s₂.length) = (0 : fin s₂.length.succ),
    from s₂.injective (hb.symm.trans (this.trans ht)).symm,
  simpa [fin.ext_iff]
end

lemma length_pos_of_bot_eq_bot_of_top_eq_top_of_length_pos
  {s₁ s₂ : composition_series X}
  (hb : s₁.bot = s₂.bot) (ht : s₁.top = s₂.top) :
  0 < s₁.length → 0 < s₂.length :=
not_imp_not.1 begin
  simp only [pos_iff_ne_zero, ne.def, not_iff_not, not_not],
  exact length_eq_zero_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero hb.symm ht.symm
end

lemma eq_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero
  {s₁ s₂ : composition_series X}
  (hb : s₁.bot = s₂.bot) (ht : s₁.top = s₂.top)
  (hs₁0 : s₁.length = 0) :
  s₁ = s₂ :=
have ∀ x, x ∈ s₁ ↔ x = s₁.top,
  from λ x, ⟨λ hx, forall_mem_eq_of_length_eq_zero hs₁0 hx s₁.top_mem, λ hx, hx.symm ▸ s₁.top_mem⟩,
have ∀ x, x ∈ s₂ ↔ x = s₂.top,
  from λ x, ⟨λ hx, forall_mem_eq_of_length_eq_zero
      (length_eq_zero_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero hb ht hs₁0)
    hx s₂.top_mem, λ hx, hx.symm ▸ s₂.top_mem⟩,
by { ext, simp * }

lemma intersection (s : composition_series X) (x : X)
  (hm : is_maximal x s.top) (hb : s.bot ≤ x) :
  ∃ t : composition_series X, t.bot = s.bot ∧ t.length + 1 = s.length ∧
    ∃ htx : t.top = x, equivalent s (insert t s.top (htx.symm ▸ hm)) :=
begin
  induction hn : s.length with n ih generalizing s x,
  { exact (ne_of_gt (lt_of_le_of_lt hb (lt_of_is_maximal hm))
      (forall_mem_eq_of_length_eq_zero hn s.top_mem s.bot_mem)).elim },
  { have h0s : 0 < s.length, from hn.symm ▸ nat.succ_pos _,
    by_cases hetx : s.erase_top.top = x,
    { use s.erase_top,
      simp [← hetx, hn] },
    { have imxs : is_maximal (x ⊓ s.erase_top.top) s.erase_top.top,
        from is_maximal_inf hm (is_maximal_erase_top_top h0s) (ne.symm hetx),
      have := ih _ _ imxs (le_inf (by simpa) (le_top s.erase_top.bot_mem)) (by simp [hn]),
      rcases this with ⟨t, htb, htl, htt, hteqv⟩,
      have hmtx : is_maximal t.top x,
      { rw [htt, inf_comm],
        exact is_maximal_inf (is_maximal_erase_top_top h0s) hm  hetx },
      use insert t x hmtx,
      refine ⟨by simp [htb], by simp [htl], by simp, _⟩,
      have : s.equivalent ((insert t s.erase_top.top (htt.symm ▸ imxs)).insert s.top
        (by simpa using is_maximal_erase_top_top h0s)),
      { conv_lhs { rw eq_insert_erase_top h0s },
        exact equivalent.insert hteqv (by simp) },
      refine this.trans _,
      refine equivalent.insert_insert_swap (by refl) _ _,
      { rw [← sup_eq_of_is_maximal (is_maximal_erase_top_top h0s) hm hetx, htt, inf_comm],
        exact isom_symm (second_iso s.erase_top.top x) },
      { rw [← sup_eq_of_is_maximal (is_maximal_erase_top_top h0s) hm hetx, htt, sup_comm],
        exact second_iso _ _ } } }
end

theorem jordan_hoelder (s₁ s₂ : composition_series X)
  (hb : s₁.bot = s₂.bot) (ht : s₁.top = s₂.top) :
  equivalent s₁ s₂ :=
begin
  induction hle : s₁.length with n ih generalizing s₁ s₂,
  { rw [eq_of_bot_eq_bot_of_top_eq_top_of_length_eq_zero hb ht hle] },
  { have h0s₂ : 0 < s₂.length,
      from length_pos_of_bot_eq_bot_of_top_eq_top_of_length_pos hb ht (hle.symm ▸ nat.succ_pos _),
    rcases intersection s₁ s₂.erase_top.top
      (ht.symm ▸ is_maximal_erase_top_top h0s₂)
      (hb.symm ▸ s₂.bot_erase_top ▸ bot_le (top_mem _)) with ⟨t₂, htb₂, htl₂, htt₂, hteq₂⟩,
    have := ih t₂ s₂.erase_top (by simp [htb₂, ← hb]) htt₂ (nat.succ_inj'.1 (htl₂.trans hle)),
    refine hteq₂.trans _,
    conv_rhs { rw [eq_insert_erase_top h0s₂] },
    simp only [ht],
    refine equivalent.insert this (by simp [htt₂]) }
end

end composition_series
