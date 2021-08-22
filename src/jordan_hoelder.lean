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

class jordan_hoelder_class (X : Type u) extends bounded_lattice X :=
(is_maximal : X → X → Prop)
(lt_of_is_maximal : ∀ x y, is_maximal x y → x < y)
(isom : (X × X) → (X × X) → Prop)

variables {X : Type u} [bounded_lattice X]

structure composition_series (is_maximal : X → X → Prop) : Type u :=
(length : ℕ)
(series : fin length.succ → X)
(step' : ∀ i : fin length, is_maximal (series i.cast_succ) (series i.succ))

namespace composition_series

variable {im : X → X → Prop}

instance : has_coe_to_fun (composition_series im) :=
{ F := _, coe := composition_series.series }

variables {X}

lemma step (s : composition_series im) : ∀ i : fin s.length,
  im (s i.cast_succ) (s i.succ) := s.step'

@[simp] lemma coe_fn_mk (length : ℕ) (series step) :
  (@composition_series.mk X _ im length series step : fin length.succ → X) = series := rfl

theorem lt_succ (him : ∀ x y, im x y → x < y)(s : composition_series im) (i : fin s.length) :
  s i.cast_succ < s i.succ :=
him _ _ (s.step _)

protected theorem strict_mono (s : composition_series im)
  (him : ∀ x y, im x y → x < y) : strict_mono s :=
fin.strict_mono_iff_lt_succ.2 (λ i h, s.lt_succ him ⟨i, nat.lt_of_succ_lt_succ h⟩)

protected theorem injective (s : composition_series im) : function.injective s :=
s.strict_mono.injective

@[simp] protected theorem inj (s : composition_series im) {i j : fin s.length.succ} :
  s i = s j ↔ i = j :=
s.injective.eq_iff

instance : has_mem X (composition_series im) :=
⟨λ x s, x ∈ set.range s⟩

lemma mem_def {x : X} {s : composition_series im} : x ∈ s ↔ x ∈ set.range s := iff.rfl

lemma total {s : composition_series im} {x y : X} (hx : x ∈ s) (hy : y ∈ s) : x ≤ y ∨ y ≤ x :=
begin
  rcases set.mem_range.1 hx with ⟨i, rfl⟩,
  rcases set.mem_range.1 hy with ⟨j, rfl⟩,
  rw [s.strict_mono.le_iff_le, s.strict_mono.le_iff_le],
  exact le_total i j
end

def to_list (s : composition_series im) : list X := list.of_fn s

lemma ext_fun {s₁ s₂ : composition_series im}
  (hl : s₁.length = s₂.length)
  (h : ∀ i, s₁ i = s₂ (fin.cast (congr_arg nat.succ hl) i)) :
  s₁ = s₂ :=
begin
  cases s₁, cases s₂,
  dsimp at *,
  subst hl,
  simpa [function.funext_iff] using h
end

lemma length_to_list (s : composition_series im) : s.to_list.length = s.length.succ :=
by rw [to_list, list.length_of_fn]

lemma to_list_injective : function.injective (@composition_series.to_list X _) :=
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

lemma to_list_sorted (s : composition_series im) : s.to_list.sorted (<) :=
list.pairwise_iff_nth_le.2 (λ i j hi hij,
  begin
    dsimp [to_list],
    rw [list.nth_le_of_fn', list.nth_le_of_fn'],
    exact s.strict_mono hij
  end)

lemma to_list_nodup (s : composition_series im) : s.to_list.nodup :=
list.nodup_iff_nth_le_inj.2
  (λ i j hi hj,
    begin
      delta to_list,
      rw [list.nth_le_of_fn', list.nth_le_of_fn', s.injective.eq_iff, fin.ext_iff, fin.coe_mk, fin.coe_mk],
      exact id
    end)

@[simp] lemma mem_to_list {s : composition_series im} {x : X} : x ∈ s.to_list ↔ x ∈ s :=
begin
  rw [to_list, list.mem_of_fn],
  refl
end

@[ext] lemma ext {s₁ s₂ : composition_series im} (h : ∀ x, x ∈ s₁ ↔ x ∈ s₂) : s₁ = s₂ :=
to_list_injective $ list.eq_of_perm_of_sorted
  (by classical; exact list.perm_of_nodup_nodup_to_finset_eq
    s₁.to_list_nodup
    s₂.to_list_nodup
    (finset.ext $ by simp *))
  s₁.to_list_sorted s₂.to_list_sorted

def top (s : composition_series im) : X := s (fin.last _)

lemma top_mem (s : composition_series im) : s.top ∈ s :=
mem_def.2 (set.mem_range.2 ⟨fin.last _, rfl⟩)

lemma le_top {s : composition_series im} {x : X} (hx : x ∈ s) : x ≤ s.top :=
let ⟨i, hi⟩ := set.mem_range.1 hx in hi ▸ s.strict_mono.monotone (fin.le_last _)

def bot (s : composition_series im) : X := s 0

lemma bot_mem (s : composition_series im) : s.bot ∈ s :=
mem_def.2 (set.mem_range.2 ⟨0, rfl⟩)

lemma bot_le {s : composition_series im} {x : X} (hx : x ∈ s) : s.bot ≤ x :=
let ⟨i, hi⟩ := set.mem_range.1 hx in hi ▸ s.strict_mono.monotone (fin.zero_le _)

instance : set_like (composition_series im) X :=
{ coe := λ s, set.range s,
  coe_injective' := λ s₁ s₂ h, ext $ λ x, begin
    dsimp at h,
    rw [mem_def, mem_def, h]
  end }

@[simps] def erase_top (s : composition_series im) : composition_series im :=
{ length := s.length - 1,
  series := λ i, s ⟨i, lt_of_lt_of_le i.2 (nat.succ_le_succ (nat.sub_le_self _ _))⟩,
  step' := λ i, begin
    have := s.step ⟨i, lt_of_lt_of_le i.2 (nat.sub_le_self _ _)⟩,
    cases i,
    exact this
  end }

lemma top_erase_top (s : composition_series im) :
  s.erase_top.top = s ⟨s.length - 1, lt_of_le_of_lt (nat.sub_le_self _ _) (nat.lt_succ_self _)⟩ :=
show s _ = s _, from congr_arg s
begin
  ext,
  simp only [erase_top_length, fin.coe_last, fin.coe_cast_succ, fin.coe_of_nat_eq_mod,
    fin.coe_mk, coe_coe]
end

@[simp] lemma bot_erase_top (s : composition_series im) : s.erase_top.bot = s.bot := rfl

lemma length_pos_of_mem_ne {s : composition_series im}
  {x y : X} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) :
  0 < s.length :=
let ⟨i, hi⟩ := hx, ⟨j, hj⟩ := hy in
have hij : i ≠ j, from mt s.inj.2 $ λ h, hxy (hi ▸ hj ▸ h),
hij.lt_or_lt.elim
  (λ hij, (lt_of_le_of_lt (zero_le i)
    (lt_of_lt_of_le hij (nat.le_of_lt_succ j.2))))
  (λ hji, (lt_of_le_of_lt (zero_le j)
    (lt_of_lt_of_le hji (nat.le_of_lt_succ i.2))))

lemma mem_erase_top_of_ne_of_mem {s : composition_series im} {x : X}
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

lemma erase_top_le (s : composition_series im) : s.erase_top ≤ s :=
begin
  rintros x ⟨i, rfl⟩,
  simp [mem_def],
end

lemma mem_erase_top {s : composition_series im} {x : X}
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
  {s : composition_series im} {x : X}
  (h : 0 < s.length)
  (hx : x ∈ s.erase_top) :
  x < s.top :=
lt_of_le_of_ne (le_top (s.erase_top_le hx)) ((mem_erase_top h).1 hx).1

lemma Ico_erase_top_top {s : composition_series im} (h : 0 < s.length) :
  Ico s.erase_top.top s.top = {s.erase_top.top} :=
have s.length - 1 + 1 = s.length,
  by conv_rhs { rw [← nat.succ_sub_one s.length] }; rw nat.succ_sub h,
begin
  rw [top_erase_top, top],
  convert s.step ⟨s.length - 1, nat.sub_lt h zero_lt_one⟩;
  ext; simp [this]
end

lemma append_cast_add_aux
  {s₁ s₂ : composition_series im}
  (h : s₁ (fin.last _) = s₂ 0)
  (i : fin s₁.length) :
  fin.append (nat.add_succ _ _).symm (s₁ ∘ fin.cast_succ) s₂
  (fin.cast_add s₂.length i).cast_succ = s₁ i.cast_succ :=
by { cases i, simp [fin.append, *] }

lemma append_succ_cast_add_aux
  {s₁ s₂ : composition_series im}
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
  {s₁ s₂ : composition_series im}
  (h : s₁ (fin.last _) = s₂ 0)
  (i : fin s₂.length) :
  fin.append (nat.add_succ _ _).symm (s₁ ∘ fin.cast_succ) s₂
  (fin.cast_add_right s₁.length i).cast_succ = s₂ i.cast_succ :=
by { cases i, simp [fin.append, *] }

lemma append_succ_cast_add_right_aux
  {s₁ s₂ : composition_series im}
  (h : s₁ (fin.last _) = s₂ 0)
  (i : fin s₂.length) :
  fin.append (nat.add_succ _ _).symm (s₁ ∘ fin.cast_succ) s₂
  (fin.cast_add_right s₁.length i).succ = s₂ i.succ :=
begin
  cases i with i hi,
  simp [fin.append, add_assoc]
end

@[simps length] def append {s₁ s₂ : composition_series im}
  (h : s₁.top = s₂.bot) :
  composition_series im :=
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
  {s₁ s₂ : composition_series im}
  (h : s₁.top = s₂.bot)
  (i : fin s₁.length) :
  append h (fin.cast_add s₂.length i).cast_succ = s₁ i.cast_succ :=
append_cast_add_aux h i

@[simp] lemma append_succ_cast_add
  {s₁ s₂ : composition_series im}
  (h : s₁.top = s₂.bot)
  (i : fin s₁.length) :
  append h (fin.cast_add s₂.length i).succ = s₁ i.succ :=
append_succ_cast_add_aux h i

@[simp] lemma append_cast_add_right
  {s₁ s₂ : composition_series im}
  (h : s₁.top = s₂.bot)
  (i : fin s₂.length) :
  append h (fin.cast_add_right s₁.length i).cast_succ = s₂ i.cast_succ :=
append_cast_add_right_aux h i

@[simp] lemma append_succ_cast_add_right
  {s₁ s₂ : composition_series im}
  (h : s₁.top = s₂.bot)
  (i : fin s₂.length) :
  append h (fin.cast_add_right s₁.length i).succ = s₂ i.succ :=
append_succ_cast_add_right_aux h i

@[simps] def insert
  (s : composition_series im)
  (x : X)
  (hlt : ∀ y ∈ s, y < x)
  (hsat : Ico s.top x = {s.top}) :
  composition_series im :=
{ length := s.length + 1,
  series := fin.snoc s x,
  step' := λ i, begin
    refine fin.last_cases _ _ i,
    { rw [fin.snoc_cast_succ, fin.succ_last, fin.snoc_last, ← top, hsat] },
    { intro i,
      rw [fin.snoc_cast_succ, ← fin.cast_succ_fin_succ, fin.snoc_cast_succ],
      exact s.step _ }
  end }

@[simp] lemma insert_series'
  (s : composition_series im)
  (x : X)
  (hlt : ∀ y ∈ s, y < x)
  (hsat : Ico s.top x = {s.top}) :
  @eq (fin (s.length + 2) → X) (insert s x hlt hsat) (fin.snoc s x) :=
rfl

@[simp] lemma top_insert
  (s : composition_series im)
  (x : X)
  (hlt : ∀ y ∈ s, y < x)
  (hsat : Ico s.top x = {s.top}) :
  (insert s x hlt hsat).top = x :=
fin.snoc_last _ _

@[simp] lemma insert_last
  (s : composition_series im)
  (x : X)
  (hlt : ∀ y ∈ s, y < x)
  (hsat : Ico s.top x = {s.top}) :
  insert s x hlt hsat (fin.last _) = x :=
fin.snoc_last _ _

@[simp] lemma insert_cast_succ
  (s : composition_series im)
  (x : X)
  (hlt : ∀ y ∈ s, y < x)
  (hsat : Ico s.top x = {s.top}) (i : fin (s.length + 1)) :
  insert s x hlt hsat (i.cast_succ) = s i :=
fin.snoc_cast_succ _ _ _

lemma mem_insert
  {s : composition_series im}
  {x y: X}
  {hlt : ∀ y ∈ s, y < x}
  {hsat : Ico s.top x = {s.top}} :
  y ∈ insert s x hlt hsat ↔ y ∈ s ∨ y = x :=
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

lemma insert_erase_top
  {s : composition_series im}
  (h : 0 < s.length) :
  s = insert (erase_top s) s.top
    (λ y, lt_top_of_mem_erase_top h)
    (Ico_erase_top_top h) :=
begin
  ext x,
  simp [mem_insert, mem_erase_top h],
  by_cases h : x = s.top; simp [*, s.top_mem]
end


variables (r : (X × X) → (X × X) → Prop)

def equivalence (s₁ s₂ : composition_series im) : Type* :=
{ f : fin s₁.length ≃ fin s₂.length //
  ∀ i : fin s₁.length,
    r (s₁ i.cast_succ, s₁ i.succ)
    (s₂ (f i).cast_succ, s₂ (f i).succ) }

namespace equivalence

variables [is_equiv _ r]

@[refl] def refl (s : composition_series im) : equivalence r s s :=
⟨equiv.refl _, λ _, is_refl.reflexive _⟩

@[symm] def symm {s₁ s₂ : composition_series im} (h : equivalence r s₁ s₂) :
  equivalence r s₂ s₁ :=
⟨h.1.symm, λ i, is_symm.symm _ _ (by simpa using h.2 (h.1.symm i))⟩

@[trans] def trans {s₁ s₂ s₃ : composition_series im}
  (h₁ : equivalence r s₁ s₂)
  (h₂ : equivalence r s₂ s₃) :
  equivalence r s₁ s₃ :=
⟨h₁.1.trans h₂.1, λ i, is_trans.trans _ _ _ (h₁.2 i) (h₂.2 (h₁.1 i))⟩

def append
  {s₁ s₂ t₁ t₂ : composition_series im}
  (hs : s₁.top = s₂.bot)
  (ht : t₁.top = t₂.bot)
  (h₁ : equivalence r s₁ t₁)
  (h₂ : equivalence r s₂ t₂) :
  equivalence r (append hs) (append ht) :=
let e : fin (s₁.length + s₂.length) ≃ fin (t₁.length + t₂.length) :=
  calc fin (s₁.length + s₂.length) ≃ fin s₁.length ⊕ fin s₂.length : fin_sum_fin_equiv.symm
  ... ≃ fin t₁.length ⊕ fin t₂.length : equiv.sum_congr h₁.1 h₂.1
  ... ≃ fin (t₁.length + t₂.length) : fin_sum_fin_equiv in
⟨e, begin
  assume i,
  refine fin.add_cases _ _ i,
  { assume i,
    simpa [top, bot] using h₁.2 i },
  { assume i,
    simpa [top, bot] using h₂.2 i }
end⟩

lemma fin.succ_cast_succ {n : ℕ} (i : fin n) :
  i.cast_succ.succ = i.succ.cast_succ :=
fin.ext (by simp)

protected lemma insert
  {s₁ s₂ : composition_series im}
  {x₁ x₂ : X}
  {hlt₁ : ∀ y ∈ s₁, y < x₁}
  {hlt₂ : ∀ y ∈ s₂, y < x₂}
  {hsat₁ : Ico s₁.top x₁ = {s₁.top}}
  {hsat₂ : Ico s₂.top x₂ = {s₂.top}}
  (hequiv : equivalence r s₁ s₂)
  (htop : r (s₁.top, x₁) (s₂.top, x₂)) :
  equivalence r (s₁.insert x₁ hlt₁ hsat₁) (s₂.insert x₂ hlt₂ hsat₂) :=
let e : fin s₁.length.succ ≃ fin s₂.length.succ :=
  calc fin (s₁.length + 1) ≃ option (fin s₁.length) : fin_succ_equiv_last
  ... ≃ option (fin s₂.length) : functor.map_equiv option hequiv.1
  ... ≃ fin (s₂.length + 1) : fin_succ_equiv_last.symm in
⟨e,  λ i, begin
  refine fin.last_cases _ _ i,
  { simpa [top] using htop },
  { assume i,
    simpa [fin.succ_cast_succ] using hequiv.2 i }
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

def option_option_equiv_swap :
  option (option α) ≃ option (option β) :=
{ to_fun := λ o, option.elim o (some none) (λ o, option.map (λ a, some (e a)) o),
  inv_fun := λ o, option.elim o (some none) (λ o, option.map (λ a, some (e.symm a)) o),
  left_inv := λ o,by rcases o with _|_|_; simp,
  right_inv := λ o, by rcases o with _|_|_; simp }

@[simp] lemma option_option_equiv_swap_none :
  option_option_equiv_swap e none = some none := rfl

@[simp] lemma option_option_equiv_swap_some_none :
  option_option_equiv_swap e (some none) = none := rfl

@[simp] lemma option_option_equiv_swap_some (a : α) :
  option_option_equiv_swap e (some a) = some (e a) := rfl

@[simp] lemma option_option_equiv_swap_symm_none :
  (option_option_equiv_swap e).symm none = some none := rfl

@[simp] lemma option_option_equiv_swap_symm_some_none :
  (option_option_equiv_swap e).symm (some none) = none := rfl

@[simp] lemma option_option_equiv_swap_symm_some (a : β) :
  (option_option_equiv_swap e).symm (some a) = some (e.symm a) := rfl

lemma insert_insert_swap
  {s₁ s₂ : composition_series im}
  {x₁ x₂ y₁ y₂ : X}
  {hlt₁ : ∀ y ∈ s₁, y < x₁}
  {hlt₂ : ∀ y ∈ s₂, y < x₂}
  {hsat₁ : Ico s₁.top x₁ = {s₁.top}}
  {hsat₂ : Ico s₂.top x₂ = {s₂.top}}
  {hlty₁ : ∀ y ∈ insert s₁ x₁ hlt₁ hsat₁, y < y₁}
  {hlty₂ : ∀ y ∈ insert s₂ x₂ hlt₂ hsat₂, y < y₂}
  {hsaty₁ : Ico (insert s₁ x₁ hlt₁ hsat₁).top y₁ = {(insert s₁ x₁ hlt₁ hsat₁).top}}
  {hsaty₂ : Ico (insert s₂ x₂ hlt₂ hsat₂).top y₂ = {(insert s₂ x₂ hlt₂ hsat₂).top}}
  (hequiv : equivalence r s₁ s₂)
  (hr₁ : r (s₁.top, x₁) (x₂, y₂))
  (hr₂ : r (x₁, y₁) (s₂.top, x₂)) :
  equivalence r
    (insert (insert s₁ x₁ hlt₁ hsat₁) y₁ hlty₁ hsaty₁)
    (insert (insert s₂ x₂ hlt₂ hsat₂) y₂ hlty₂ hsaty₂) :=
let e : fin (s₁.length + 1 + 1) ≃ fin (s₂.length + 1 + 1) :=
swap_top_two_fin hequiv.1 in
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
      exact hequiv.2 i } }
end⟩

end equivalence


  -- (second_iso : ∀ h k, r (h ⊔ k, k) (h, h ⊓ k))
--   -- (hIco : ∀ g h k : X, Ico h g = {h} → Ico k g = {k} → Ico (h ⊓ k) h = {h ⊓ k}) Not right. Need h ≠ k

lemma length_pos_of_length_pos_of_bot_eq_bot_of_top_eq_top
  {s₁ s₂ : composition_series im}
  (hb : s₁.bot = s₂.bot) (ht : s₁.top = s₂.top) :
  0 < s₁.length →  0 < s₂.length :=
not_imp_not.1 begin
  simp only [pos_iff_ne_zero, ne.def, not_iff_not, not_not],
  assume hs₂,
  have : s₂.bot = s₂.top,
    from congr_arg s₂ (fin.ext (by simp [hs₂])),
  have : (fin.last s₁.length) = (0 : fin s₁.length.succ),
    from s₁.injective (hb.trans (this.trans ht.symm)).symm,
  simpa [fin.ext_iff]
end
-- Maybe a series is just a set?
theorem jordan_hoelder [is_equiv _ r] (s₁ s₂ : composition_series im)
  (hb : s₁.bot = s₂.bot) (ht : s₁.top = s₂.top) :
  equivalence r s₁ s₂ :=
begin
  induction hle : s₁.length with n ih generalizing s₁ s₂,
  { admit
    --  haveI hs : subsingleton X,
    -- { rw [subsingleton_iff_length_eq_zero, hl] },
    -- have : s₁.length = s₂.length,
    -- { rw [hl, eq_comm, ← subsingleton_iff_length_eq_zero,
    --     s₁.subsingleton_iff_length_eq_zero, hl] },
    -- use this,
    -- intros i j hij,
    -- have : ∀ x : X, x = s₁ i, from λ _, subsingleton.elim _ _,
    -- rw [this (s₁ j), this (s₂ _), this (s₂ _)],
    -- exact is_refl.reflexive _
    },
  { have h0₁ : 0 < s₁.length, from hle.symm ▸ nat.succ_pos _,
    have h0₂ : 0 < s₂.length,
      from length_pos_of_length_pos_of_bot_eq_bot_of_top_eq_top hb ht h0₁,
    by_cases heq: s₁.erase_top.top = s₂.erase_top.top,
    { rw [insert_erase_top h0₁, insert_erase_top h0₂],
      have hr : r (s₁.erase_top.top, s₁.top) (s₂.erase_top.top, s₂.top),
      { rw [ht, heq], exact is_refl.refl _ },
      refine equivalence.insert _ _ hr,
      refine ih _ _ _ _ _,
      { simp [hb] },
      { exact heq },
      { simp [hle] } },
    { have h0e₁ : 0 < s₁.erase_top.length,
        from length_pos_of_mem_ne (bot_mem _) (top_mem _) _ }

      }

end

