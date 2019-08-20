/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard, Amelia Livingston
-/
import algebra.big_operators
import data.finset
import tactic.subtype_instance

/-!

# Submonoids

First unbundled (is_submonoid) (deprecated) and then bundled.

-- mention ≤ instead of ⊆ for inclusions

no coercion from submonoid to subset, the idea is that the API does it all for us.
there is ∈ though

-/

variables {α : Type*} [monoid α] {s : set α}
variables {β : Type*} [add_monoid β] {t : set β}

/-- `s` is a submonoid: a set containing 1 and closed under multiplication. -/
class is_submonoid (s : set α) : Prop :=
(one_mem : (1:α) ∈ s)
(mul_mem {a b} : a ∈ s → b ∈ s → a * b ∈ s)

/-- `s` is an additive submonoid: a set containing 0 and closed under addition. -/
class is_add_submonoid (s : set β) : Prop :=
(zero_mem : (0:β) ∈ s)
(add_mem {a b} : a ∈ s → b ∈ s → a + b ∈ s)

attribute [to_additive is_add_submonoid] is_submonoid
attribute [to_additive is_add_submonoid.zero_mem] is_submonoid.one_mem
attribute [to_additive is_add_submonoid.add_mem] is_submonoid.mul_mem
attribute [to_additive is_add_submonoid.mk] is_submonoid.mk

instance additive.is_add_submonoid
  (s : set α) : ∀ [is_submonoid s], @is_add_submonoid (additive α) _ s
| ⟨h₁, h₂⟩ := ⟨h₁, @h₂⟩

theorem additive.is_add_submonoid_iff
  {s : set α} : @is_add_submonoid (additive α) _ s ↔ is_submonoid s :=
⟨λ ⟨h₁, h₂⟩, ⟨h₁, @h₂⟩, λ h, by resetI; apply_instance⟩

instance multiplicative.is_submonoid
  (s : set β) : ∀ [is_add_submonoid s], @is_submonoid (multiplicative β) _ s
| ⟨h₁, h₂⟩ := ⟨h₁, @h₂⟩

theorem multiplicative.is_submonoid_iff
  {s : set β} : @is_submonoid (multiplicative β) _ s ↔ is_add_submonoid s :=
⟨λ ⟨h₁, h₂⟩, ⟨h₁, @h₂⟩, λ h, by resetI; apply_instance⟩

@[to_additive is_add_submonoid.inter]
lemma is_submonoid.inter (s₁ s₂ : set α) [is_submonoid s₁] [is_submonoid s₂] :
  is_submonoid (s₁ ∩ s₂) :=
{ one_mem := ⟨is_submonoid.one_mem _, is_submonoid.one_mem _⟩,
  mul_mem := λ x y hx hy,
    ⟨is_submonoid.mul_mem hx.1 hy.1, is_submonoid.mul_mem hx.2 hy.2⟩ }

lemma is_submonoid_Union_of_directed {ι : Type*} [hι : nonempty ι]
  (s : ι → set α) [∀ i, is_submonoid (s i)]
  (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) :
  is_submonoid (⋃i, s i) :=
{ one_mem := let ⟨i⟩ := hι in set.mem_Union.2 ⟨i, is_submonoid.one_mem _⟩,
  mul_mem := λ a b ha hb,
    let ⟨i, hi⟩ := set.mem_Union.1 ha in
    let ⟨j, hj⟩ := set.mem_Union.1 hb in
    let ⟨k, hk⟩ := directed i j in
    set.mem_Union.2 ⟨k, is_submonoid.mul_mem (hk.1 hi) (hk.2 hj)⟩ }

lemma is_add_submonoid_Union_of_directed {ι : Type*} [hι : nonempty ι]
  (s : ι → set β) [∀ i, is_add_submonoid (s i)]
  (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) :
  is_add_submonoid (⋃i, s i) :=
multiplicative.is_submonoid_iff.1 $
  @is_submonoid_Union_of_directed (multiplicative β) _ _ _ s _ directed
attribute [to_additive is_add_submonoid_Union_of_directed] is_submonoid_Union_of_directed

section powers

def powers (x : α) : set α := {y | ∃ n:ℕ, x^n = y}
def multiples (x : β) : set β := {y | ∃ n:ℕ, add_monoid.smul n x = y}
attribute [to_additive multiples] powers

lemma powers.one_mem {x : α} : (1 : α) ∈ powers x := ⟨0, pow_zero _⟩

lemma multiples.zero_mem {x : β} : (0 : β) ∈ multiples x := ⟨0, add_monoid.zero_smul _⟩
attribute [to_additive multiples.zero_mem] powers.one_mem

lemma powers.self_mem {x : α} : x ∈ powers x := ⟨1, pow_one _⟩

lemma multiples.self_mem {x : β} : x ∈ multiples x := ⟨1, add_monoid.one_smul _⟩
attribute [to_additive multiples.self_mem] powers.self_mem

instance powers.is_submonoid (x : α) : is_submonoid (powers x) :=
{ one_mem := ⟨0, by simp⟩,
  mul_mem := λ x₁ x₂ ⟨n₁, hn₁⟩ ⟨n₂, hn₂⟩, ⟨n₁ + n₂, by simp [pow_add, *]⟩ }

instance multiples.is_add_submonoid (x : β) : is_add_submonoid (multiples x) :=
multiplicative.is_submonoid_iff.1 $ powers.is_submonoid _
attribute [to_additive multiples.is_add_submonoid] powers.is_submonoid

@[to_additive univ.is_add_submonoid]
instance univ.is_submonoid : is_submonoid (@set.univ α) := by split; simp

@[to_additive preimage.is_add_submonoid]
instance preimage.is_submonoid {γ : Type*} [monoid γ] (f : α → γ) [is_monoid_hom f]
  (s : set γ) [is_submonoid s] : is_submonoid (f ⁻¹' s) :=
{ one_mem := show f 1 ∈ s, by rw is_monoid_hom.map_one f; exact is_submonoid.one_mem s,
  mul_mem := λ a b (ha : f a ∈ s) (hb : f b ∈ s),
    show f (a * b) ∈ s, by rw is_monoid_hom.map_mul f; exact is_submonoid.mul_mem ha hb }

@[instance, to_additive image.is_add_submonoid]
lemma image.is_submonoid {γ : Type*} [monoid γ] (f : α → γ) [is_monoid_hom f]
  (s : set α) [is_submonoid s] : is_submonoid (f '' s) :=
{ one_mem := ⟨1, is_submonoid.one_mem s, is_monoid_hom.map_one f⟩,
  mul_mem := λ a b ⟨x, hx⟩ ⟨y, hy⟩, ⟨x * y, is_submonoid.mul_mem hx.1 hy.1,
    by rw [is_monoid_hom.map_mul f, hx.2, hy.2]⟩ }

instance range.is_submonoid {γ : Type*} [monoid γ] (f : α → γ) [is_monoid_hom f] :
  is_submonoid (set.range f) :=
by rw ← set.image_univ; apply_instance

lemma is_submonoid.pow_mem {a : α} [is_submonoid s] (h : a ∈ s) : ∀ {n : ℕ}, a ^ n ∈ s
| 0 := is_submonoid.one_mem s
| (n + 1) := is_submonoid.mul_mem h is_submonoid.pow_mem

lemma is_add_submonoid.smul_mem {a : β} [is_add_submonoid t] :
  ∀ (h : a ∈ t) {n : ℕ}, add_monoid.smul n a ∈ t :=
@is_submonoid.pow_mem (multiplicative β) _ _ _ _
attribute [to_additive is_add_submonoid.smul_mem] is_submonoid.pow_mem

lemma is_submonoid.power_subset {a : α} [is_submonoid s] (h : a ∈ s) : powers a ⊆ s :=
assume x ⟨n, hx⟩, hx ▸ is_submonoid.pow_mem h

lemma is_add_submonoid.multiple_subset {a : β} [is_add_submonoid t] :
  a ∈ t → multiples a ⊆ t :=
@is_submonoid.power_subset (multiplicative β) _ _ _ _
attribute [to_additive is_add_submonoid.multiple_subset] is_add_submonoid.multiple_subset

end powers

namespace is_submonoid

@[to_additive is_add_submonoid.list_sum_mem]
lemma list_prod_mem [is_submonoid s] : ∀{l : list α}, (∀x∈l, x ∈ s) → l.prod ∈ s
| []     h := one_mem s
| (a::l) h :=
  suffices a * l.prod ∈ s, by simpa,
  have a ∈ s ∧ (∀x∈l, x ∈ s), by simpa using h,
  is_submonoid.mul_mem this.1 (list_prod_mem this.2)

@[to_additive is_add_submonoid.multiset_sum_mem]
lemma multiset_prod_mem {α} [comm_monoid α] (s : set α) [is_submonoid s] (m : multiset α) :
  (∀a∈m, a ∈ s) → m.prod ∈ s :=
begin
  refine quotient.induction_on m (assume l hl, _),
  rw [multiset.quot_mk_to_coe, multiset.coe_prod],
  exact list_prod_mem hl
end

@[to_additive is_add_submonoid.finset_sum_mem]
lemma finset_prod_mem {α β} [comm_monoid α] (s : set α) [is_submonoid s] (f : β → α) :
  ∀(t : finset β), (∀b∈t, f b ∈ s) → t.prod f ∈ s
| ⟨m, hm⟩ hs :=
  begin
    refine multiset_prod_mem s _ _,
    simp,
    rintros a b hb rfl,
    exact hs _ hb
  end

end is_submonoid

instance subtype.monoid {s : set α} [is_submonoid s] : monoid s :=
by subtype_instance

attribute [to_additive subtype.add_monoid._proof_1] subtype.monoid._proof_1
attribute [to_additive subtype.add_monoid._proof_2] subtype.monoid._proof_2
attribute [to_additive subtype.add_monoid._proof_3] subtype.monoid._proof_3
attribute [to_additive subtype.add_monoid._proof_4] subtype.monoid._proof_4
attribute [to_additive subtype.add_monoid._proof_5] subtype.monoid._proof_5
attribute [to_additive subtype.add_monoid] subtype.monoid

@[simp, to_additive is_add_submonoid.coe_zero]
lemma is_submonoid.coe_one [is_submonoid s] : ((1 : s) : α) = 1 := rfl

@[simp, to_additive is_add_submonoid.coe_add]
lemma is_submonoid.coe_mul [is_submonoid s] (a b : s) : ((a * b : s) : α) = a * b := rfl

@[simp] lemma is_submonoid.coe_pow [is_submonoid s] (a : s) (n : ℕ) : ((a ^ n : s) : α) = a ^ n :=
by induction n; simp [*, pow_succ]

@[simp] lemma is_add_submonoid.smul_coe {β : Type*} [add_monoid β] {s : set β}
  [is_add_submonoid s] (a : s) (n : ℕ) : ((add_monoid.smul n a : s) : β) = add_monoid.smul n a :=
by induction n; [refl, simp [*, succ_smul]]
attribute [to_additive is_add_submonoid.smul_coe] is_submonoid.coe_pow

@[to_additive subtype_val.is_add_monoid_hom]
instance subtype_val.is_monoid_hom [is_submonoid s] : is_monoid_hom (subtype.val : s → α) :=
{ map_one := rfl, map_mul := λ _ _, rfl }

@[to_additive coe.is_add_monoid_hom]
instance coe.is_monoid_hom [is_submonoid s] : is_monoid_hom (coe : s → α) :=
subtype_val.is_monoid_hom

@[to_additive subtype_mk.is_add_monoid_hom]
instance subtype_mk.is_monoid_hom {γ : Type*} [monoid γ] [is_submonoid s] (f : γ → α)
  [is_monoid_hom f] (h : ∀ x, f x ∈ s) : is_monoid_hom (λ x, (⟨f x, h x⟩ : s)) :=
{ map_one := subtype.eq (is_monoid_hom.map_one f),
  map_mul := λ x y, subtype.eq (is_monoid_hom.map_mul f x y) }

@[to_additive set_inclusion.is_add_monoid_hom]
instance set_inclusion.is_monoid_hom (t : set α) [is_submonoid s] [is_submonoid t] (h : s ⊆ t) :
  is_monoid_hom (set.inclusion h) :=
subtype_mk.is_monoid_hom _ _

namespace monoid

inductive in_closure (s : set α) : α → Prop
| basic {a : α} : a ∈ s → in_closure a
| one : in_closure 1
| mul {a b : α} : in_closure a → in_closure b → in_closure (a * b)

def closure (s : set α) : set α := {a | in_closure s a }

instance closure.is_submonoid (s : set α) : is_submonoid (closure s) :=
{ one_mem := in_closure.one s, mul_mem := assume a b, in_closure.mul }

theorem subset_closure {s : set α} : s ⊆ closure s :=
assume a, in_closure.basic

theorem closure_subset {s t : set α} [is_submonoid t] (h : s ⊆ t) : closure s ⊆ t :=
assume a ha, by induction ha; simp [h _, *, is_submonoid.one_mem, is_submonoid.mul_mem]

theorem closure_mono {s t : set α} (h : s ⊆ t) : closure s ⊆ closure t :=
closure_subset $ set.subset.trans h subset_closure

theorem closure_singleton {x : α} : closure ({x} : set α) = powers x :=
set.eq_of_subset_of_subset (closure_subset $ set.singleton_subset_iff.2 $ powers.self_mem) $
  is_submonoid.power_subset $ set.singleton_subset_iff.1 $ subset_closure

lemma image_closure {β : Type*} [monoid β] (f : α → β) [is_monoid_hom f] (s : set α) :
  f '' closure s = closure (f '' s) :=
le_antisymm
  begin
    rintros _ ⟨x, hx, rfl⟩,
    apply in_closure.rec_on hx; intros,
    { solve_by_elim [subset_closure, set.mem_image_of_mem] },
    { rw [is_monoid_hom.map_one f], apply is_submonoid.one_mem },
    { rw [is_monoid_hom.map_mul f], solve_by_elim [is_submonoid.mul_mem] }
  end
  (closure_subset $ set.image_subset _ subset_closure)

theorem exists_list_of_mem_closure {s : set α} {a : α} (h : a ∈ closure s) :
  (∃l:list α, (∀x∈l, x ∈ s) ∧ l.prod = a) :=
begin
  induction h,
  case in_closure.basic : a ha { existsi ([a]), simp [ha] },
  case in_closure.one { existsi ([]), simp },
  case in_closure.mul : a b _ _ ha hb {
    rcases ha with ⟨la, ha, eqa⟩,
    rcases hb with ⟨lb, hb, eqb⟩,
    existsi (la ++ lb),
    simp [eqa.symm, eqb.symm, or_imp_distrib],
    exact assume a, ⟨ha a, hb a⟩
  }
end

theorem mem_closure_union_iff {α : Type*} [comm_monoid α] {s t : set α} {x : α} :
  x ∈ closure (s ∪ t) ↔ ∃ y ∈ closure s, ∃ z ∈ closure t, y * z = x :=
⟨λ hx, let ⟨L, HL1, HL2⟩ := exists_list_of_mem_closure hx in HL2 ▸
  list.rec_on L (λ _, ⟨1, is_submonoid.one_mem _, 1, is_submonoid.one_mem _, mul_one _⟩)
    (λ hd tl ih HL1, let ⟨y, hy, z, hz, hyzx⟩ := ih (list.forall_mem_of_forall_mem_cons HL1) in
      or.cases_on (HL1 hd $ list.mem_cons_self _ _)
        (λ hs, ⟨hd * y, is_submonoid.mul_mem (subset_closure hs) hy, z, hz, by rw [mul_assoc, list.prod_cons, ← hyzx]; refl⟩)
        (λ ht, ⟨y, hy, z * hd, is_submonoid.mul_mem hz (subset_closure ht), by rw [← mul_assoc, list.prod_cons, ← hyzx, mul_comm hd]; refl⟩)) HL1,
λ ⟨y, hy, z, hz, hyzx⟩, hyzx ▸ is_submonoid.mul_mem (closure_mono (set.subset_union_left _ _) hy)
  (closure_mono (set.subset_union_right _ _) hz)⟩

end monoid

namespace add_monoid

def closure (s : set β) : set β := @monoid.closure (multiplicative β) _ s
attribute [to_additive add_monoid.closure] monoid.closure

instance closure.is_add_submonoid (s : set β) : is_add_submonoid (closure s) :=
multiplicative.is_submonoid_iff.1 $ monoid.closure.is_submonoid s
attribute [to_additive add_monoid.closure.is_add_submonoid] monoid.closure.is_submonoid

theorem subset_closure {s : set β} : s ⊆ closure s :=
monoid.subset_closure
attribute [to_additive add_monoid.subset_closure] monoid.subset_closure

theorem closure_subset {s t : set β} [is_add_submonoid t] : s ⊆ t → closure s ⊆ t :=
monoid.closure_subset
attribute [to_additive add_monoid.closure_subset] monoid.closure_subset

theorem closure_mono {s t : set β} (h : s ⊆ t) : closure s ⊆ closure t :=
closure_subset $ set.subset.trans h subset_closure
attribute [to_additive add_monoid.closure_mono] monoid.closure_mono

theorem closure_singleton {x : β} : closure ({x} : set β) = multiples x :=
monoid.closure_singleton
attribute [to_additive add_monoid.closure_singleton] monoid.closure_singleton

theorem exists_list_of_mem_closure {s : set β} {a : β} :
  a ∈ closure s → ∃l:list β, (∀x∈l, x ∈ s) ∧ l.sum = a :=
monoid.exists_list_of_mem_closure
attribute [to_additive add_monoid.exists_list_of_mem_closure] monoid.exists_list_of_mem_closure

@[elab_as_eliminator]
theorem in_closure.rec_on {s : set β} {C : β → Prop}
  {a : β} (H : a ∈ closure s)
  (H1 : ∀ {a : β}, a ∈ s → C a) (H2 : C 0)
  (H3 : ∀ {a b : β}, a ∈ closure s → b ∈ closure s → C a → C b → C (a + b)) :
  C a :=
monoid.in_closure.rec_on H (λ _, H1) H2 (λ _ _, H3)

lemma image_closure {γ : Type*} [add_monoid γ] (f : β → γ) [is_add_monoid_hom f] (s : set β) :
  f '' closure s = closure (f '' s) :=
le_antisymm
  begin
    rintros _ ⟨x, hx, rfl⟩,
    apply in_closure.rec_on hx; intros,
    { solve_by_elim [subset_closure, set.mem_image_of_mem] },
    { rw [is_add_monoid_hom.map_zero f], apply is_add_submonoid.zero_mem },
    { rw [is_add_monoid_hom.map_add f], solve_by_elim [is_add_submonoid.add_mem] }
  end
  (closure_subset $ set.image_subset _ subset_closure)
attribute [to_additive add_monoid.image_closure] monoid.image_closure

theorem mem_closure_union_iff {β : Type*} [add_comm_monoid β] {s t : set β} {x : β} :
  x ∈ closure (s ∪ t) ↔ ∃ y ∈ closure s, ∃ z ∈ closure t, y + z = x :=
monoid.mem_closure_union_iff

end add_monoid

-- bundled submonoids and add_submonoids

/-- A submonoid of a monoid α is a subset containing 1 and closed under multiplication. -/
structure submonoid (α : Type*) [monoid α] :=
(carrier : set α)
(one_mem' : (1 : α) ∈ carrier)
(mul_mem' {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier)

/-- An  additive submonoid of an additive monoid α is a subset containing 0 and
  closed under addition. -/
structure add_submonoid (α : Type*) [add_monoid α] :=
(carrier : set α)
(zero_mem' : (0 : α) ∈ carrier)
(add_mem' {a b} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier)

attribute [to_additive add_submonoid] submonoid
attribute [to_additive add_submonoid.carrier] submonoid.carrier
attribute [to_additive add_submonoid.cases_on] submonoid.cases_on
attribute [to_additive add_submonoid.has_sizeof_inst] submonoid.has_sizeof_inst
attribute [to_additive add_submonoid.mk] submonoid.mk
attribute [to_additive add_submonoid.mk.inj] submonoid.mk.inj
attribute [to_additive add_submonoid.mk.inj_arrow] submonoid.mk.inj_arrow
attribute [to_additive add_submonoid.mk.inj_eq] submonoid.mk.inj_eq
attribute [to_additive add_submonoid.mk.sizeof_spec] submonoid.mk.sizeof_spec
attribute [to_additive add_submonoid.add_mem'] submonoid.mul_mem'
attribute [to_additive add_submonoid.no_confusion] submonoid.no_confusion
attribute [to_additive add_submonoid.no_confusion_type] submonoid.no_confusion_type
attribute [to_additive add_submonoid.zero_mem'] submonoid.one_mem'
attribute [to_additive add_submonoid.rec] submonoid.rec
attribute [to_additive add_submonoid.rec_on] submonoid.rec_on
attribute [to_additive add_submonoid.sizeof] submonoid.sizeof

/-- Map from submonoids of monoid α to add_submonoids of additive α. -/
def submonoid.to_add_submonoid {α : Type*} [monoid α] (S : submonoid α) :
  add_submonoid (additive α) :=
{ carrier := S.carrier,
  zero_mem' := S.one_mem',
  add_mem' := S.mul_mem' }

/-- Map from add_submonoids of additive α to submonoids of α. -/
def submonoid.of_add_submonoid {α : Type*} [monoid α] (S : add_submonoid (additive α)) :
  submonoid α :=
{ carrier := S.carrier,
  one_mem' := S.zero_mem',
  mul_mem' := S.add_mem' }

/-- Map from add_submonoids of add_monoid α to submonoids of multiplicative α. -/
def add_submonoid.to_submonoid {α : Type*} [add_monoid α] (S : add_submonoid α) :
  submonoid (multiplicative α) :=
{ carrier := S.carrier,
  one_mem' := S.zero_mem',
  mul_mem' := S.add_mem' }

/-- Map from submonoids of multiplicative α to add_submonoids of add_monoid α. -/
def add_submonoid.of_submonoid {α : Type*} [add_monoid α] (S : submonoid (multiplicative α)) :
  add_submonoid α :=
{ carrier := S.carrier,
  zero_mem' := S.one_mem',
  add_mem' := S.mul_mem' }

/-- submonoids of monoid α are isomorphic to additive submonoids of additive α. -/
def submonoid.add_submonoid_equiv (α : Type*) [monoid α] :
submonoid α ≃ add_submonoid (additive α) :=
{ to_fun := submonoid.to_add_submonoid,
  inv_fun := submonoid.of_add_submonoid,
  left_inv := λ x, by cases x; refl,
  right_inv := λ x, by cases x; refl }

namespace submonoid

variables {M : Type*} [monoid M] (S : submonoid M)

@[to_additive add_submonoid.has_coe]
instance : has_coe (submonoid M) (set M) := ⟨submonoid.carrier⟩

@[to_additive add_submonoid.has_mem]
instance : has_mem M (submonoid M) := ⟨λ m S, m ∈ S.carrier⟩

@[to_additive add_submonoid.has_le]
instance : has_le (submonoid M) := ⟨λ S T, S.carrier ⊆ T.carrier⟩

@[simp, to_additive add_submonoid.mem_coe]
lemma mem_coe {m : M} : m ∈ (S : set M) ↔ m ∈ S := iff.rfl

/-- Two submonoids are equal if the underlying subsets are equal. -/
@[to_additive add_submonoid.ext']
theorem ext' {S T : submonoid M} (h : (S : set M) = T) : S = T :=
by cases S; cases T; congr'

run_cmd tactic.add_doc_string `add_submonoid.ext'
  "Two add_submonoids are equal if the underling subsets are equal."

/-- Two submonoids are equal if and only if the underlying subsets are equal. -/
@[to_additive add_submonoid.ext'_iff]
protected theorem ext'_iff {S T : submonoid M}  : (S : set M) = T ↔ S = T :=
⟨ext', λ h, h ▸ rfl⟩

run_cmd tactic.add_doc_string `add_submonoid.ext'_iff
  "Two add_submonoids are equal if and only if the underling subsets are equal."

/-- Two submonoids are equal if they have the same elements. -/
@[extensionality, to_additive add_submonoid.ext]
theorem ext {S T : submonoid M}
  (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := ext' $ set.ext h

attribute [extensionality] add_submonoid.ext
run_cmd tactic.add_doc_string `add_submonoid.ext
  "Two add_submonoids are equal if they have the same elements."

/-- A submonoid contains the monoid's 1. -/
@[to_additive add_submonoid.zero_mem]
theorem one_mem : (1 : M) ∈ S := S.one_mem'

run_cmd tactic.add_doc_string `add_submonoid.zero_mem
  "An add_submonoid contains the monoid's 0."

/-- A submonoid is closed under multiplication. -/
@[to_additive add_submonoid.add_mem]
theorem mul_mem {x y : M} : x ∈ S → y ∈ S → x * y ∈ S := submonoid.mul_mem' S

run_cmd tactic.add_doc_string `add_submonoid.add_mem
  "An add_submonoid is closed under addition."

/-- A finite product of elements of a submonoid of a commutative monoid is in the submonoid. -/
@[to_additive add_submonoid.sum_mem]
lemma prod_mem {M : Type*} [comm_monoid M] (S : submonoid M)
  {ι : Type*} [decidable_eq ι] {t : finset ι} {f : ι → M} :
  (∀c ∈ t, f c ∈ S) → t.prod f ∈ S :=
finset.induction_on t (by simp [S.one_mem]) (by simp [S.mul_mem] {contextual := tt})

run_cmd tactic.add_doc_string `add_submonoid.sum_mem
  "A finite sum of elements of an add_submonoid of an add_comm_monoid is in the add_submonoid."

/-- A directed union of submonoids is a submonoid. -/
def Union_of_directed {ι : Type*} [hι : nonempty ι]
  (s : ι → submonoid M)
  (directed : ∀ i j, ∃ k, s i ≤ s k ∧ s j ≤ s k) :
  submonoid M :=
{ carrier := (⋃i, s i),
  one_mem' := let ⟨i⟩ := hι in set.mem_Union.2 ⟨i, submonoid.one_mem _⟩,
  mul_mem' := λ a b ha hb,
    let ⟨i, hi⟩ := set.mem_Union.1 ha in
    let ⟨j, hj⟩ := set.mem_Union.1 hb in
    let ⟨k, hk⟩ := directed i j in
    set.mem_Union.2 ⟨k, (s k).mul_mem (hk.1 hi) (hk.2 hj)⟩ }

attribute [to_additive add_submonoid.Union_of_directed._match_1] submonoid.Union_of_directed._match_1
attribute [to_additive add_submonoid.Union_of_directed._match_2] submonoid.Union_of_directed._match_2
attribute [to_additive add_submonoid.Union_of_directed._match_3] submonoid.Union_of_directed._match_3
attribute [to_additive add_submonoid.Union_of_directed._match_4] submonoid.Union_of_directed._match_4
attribute [to_additive add_submonoid.Union_of_directed._proof_1] submonoid.Union_of_directed._proof_1
attribute [to_additive add_submonoid.Union_of_directed] submonoid.Union_of_directed
attribute [to_additive add_submonoid.Union_of_directed._match_1.equations._eqn_1] submonoid.Union_of_directed._match_1.equations._eqn_1
attribute [to_additive add_submonoid.Union_of_directed._match_2.equations._eqn_1] submonoid.Union_of_directed._match_2.equations._eqn_1
attribute [to_additive add_submonoid.Union_of_directed._match_3.equations._eqn_1] submonoid.Union_of_directed._match_3.equations._eqn_1
attribute [to_additive add_submonoid.Union_of_directed._match_4.equations._eqn_1] submonoid.Union_of_directed._match_4.equations._eqn_1
attribute [to_additive add_submonoid.Union_of_directed.equations._eqn_1] submonoid.Union_of_directed.equations._eqn_1
run_cmd tactic.add_doc_string `add_submonoid.Union_of_directed
  "A directed union of add_submonoids is an add_submonoid."

/-- The powers 1, x, x^2, ... of an element x of a monoid M are a submonoid. -/
def powers (x : M) : submonoid M :=
{ carrier := {y | ∃ n:ℕ, x^n = y},
  one_mem' := ⟨0, pow_zero x⟩,
  mul_mem' := by rintros x₁ x₂ ⟨n₁, rfl⟩ ⟨n₂, rfl⟩; exact ⟨n₁ + n₂, pow_add _ _ _ ⟩ }

-- TODO -- move to appropriate places
attribute [to_additive add_monoid.mul._main] monoid.pow._main
attribute [to_additive add_monoid.mul] monoid.pow
attribute [to_additive add_monoid.has_smul] monoid.has_pow
attribute [to_additive multiples._proof_1] powers._proof_1
attribute [to_additive multiples._proof_2] powers._proof_2

attribute [to_additive add_submonoid.multiples] submonoid.powers
attribute [to_additive add_submonoid.multiples._proof_1] submonoid.powers._proof_1
attribute [to_additive add_submonoid.multiples._proof_2] submonoid.powers._proof_2
attribute [to_additive add_submonoid.multiples.equations._eqn_1] submonoid.powers.equations._eqn_1
run_cmd tactic.add_doc_string `add_submonoid.multiples
  "The multiples 0, x, 2x, ... of an element x of an add_monoid M are an add_submonoid."

/-- x is in the submonoid generated by x. -/
lemma powers.self_mem {x : M} : x ∈ powers x := ⟨1, pow_one _⟩

-- the to_additive machinery can't handle powers so we have to explicitly come out
-- of the submonoid namespace and do the additive version by hand.

end submonoid

/-- x is in the add_submonoid generated by x. -/
lemma add_submonoid.multiples.self_mem {M : Type*} [add_monoid M] {x : M} :
  x ∈ add_submonoid.multiples x :=
⟨1, add_monoid.one_smul x⟩

attribute [to_additive add_submonoid.multiples.self_mem] submonoid.powers.self_mem

namespace submonoid

variables {M : Type*} [monoid M] (S : submonoid M)

/-- `univ` is the submonoid M of the monoid M. -/
def univ : submonoid M :=
{ carrier := set.univ,
  one_mem' := set.mem_univ 1,
  mul_mem' := λ _ _ _ _, set.mem_univ _ }

attribute [to_additive add_submonoid.univ._proof_1] submonoid.univ._proof_1
attribute [to_additive add_submonoid.univ._proof_2] submonoid.univ._proof_2
attribute [to_additive add_submonoid.univ] submonoid.univ
attribute [to_additive add_submonoid.univ.equations._eqn_1] submonoid.univ.equations._eqn_1
run_cmd tactic.add_doc_string `add_submonoid.univ
  "`univ` is the add_submonoid M of the add_monoid M."

/-- ⊥ is the trivial submonoid of the monoid M. -/
def bot : submonoid M :=
{ carrier := {1},
  one_mem' := set.mem_singleton 1,
  mul_mem' := λ a b ha hb, by simp * at *}

attribute [to_additive add_submonoid.bot._proof_1] submonoid.bot._proof_1
attribute [to_additive add_submonoid.bot._proof_2] submonoid.bot._proof_2
attribute [to_additive add_submonoid.bot] submonoid.bot
attribute [to_additive add_submonoid.bot.equations._eqn_1] submonoid.bot.equations._eqn_1
run_cmd tactic.add_doc_string `add_submonoid.bot
  "⊥ is the zero submonoid of the add_monoid M."

-- TODO: up to here with to_additive stuff

instance : partial_order (submonoid M) :=
partial_order.lift (coe : submonoid M → set M) (λ a b, ext') (by apply_instance)

lemma le_def (p p' : submonoid M) : p ≤ p' ↔ ∀ x ∈ p, x ∈ p' := iff.rfl

open lattice

instance : has_bot (submonoid M) := ⟨submonoid.bot⟩

@[simp] lemma mem_bot {x : M} : x ∈ (⊥ : submonoid M) ↔ x = 1 := set.mem_singleton_iff

instance : order_bot (submonoid M) :=
{ bot := ⊥,
  bot_le := λ P x hx, by simp * at *; exact P.one_mem,
  ..submonoid.partial_order
  }

instance : has_top (submonoid M) := ⟨univ⟩

@[simp] lemma mem_top (x : M) : x ∈ (⊤ : submonoid M) := set.mem_univ x

instance : order_top (submonoid M) :=
{ top := ⊤,
  le_top := λ p x _, mem_top x,
  ..submonoid.partial_order}

--@[to_additive is_add_submonoid.inter]
def inf (S₁ S₂ : submonoid M) :
  submonoid M :=
{ carrier := S₁ ∩ S₂,
  one_mem' := ⟨S₁.one_mem, S₂.one_mem⟩,
  mul_mem' := λ _ _ ⟨hx, hx'⟩ ⟨hy, hy'⟩,
    ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }

instance : has_inf (submonoid M) := ⟨inf⟩

lemma mem_inf {p p' : submonoid M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
⟨λ h, ⟨h.1, h.2⟩, λ h, (p ⊓ p').mem_coe.2 ⟨h.1, h.2⟩⟩

instance : has_Inf (submonoid M) :=
⟨λ s, {
  carrier := ⋂ t ∈ s, ↑t,
  one_mem' := set.mem_bInter $ λ i h, i.one_mem,
  mul_mem' := λ x y hx hy, set.mem_bInter $ λ i h,
    i.mul_mem (by apply set.mem_bInter_iff.1 hx i h) (by apply set.mem_bInter_iff.1 hy i h) }⟩

lemma Inf_le' {S : set (submonoid M)} {p} : p ∈ S → Inf S ≤ p :=
set.bInter_subset_of_mem

lemma le_Inf' {S : set (submonoid M)} {p} : (∀p' ∈ S, p ≤ p') → p ≤ Inf S :=
set.subset_bInter

lemma mem_Inf {S : set (submonoid M)} {x : M} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p := set.mem_bInter_iff

instance : lattice (submonoid M) :=
{ sup          := λ a b, Inf {x | a ≤ x ∧ b ≤ x},
  le_sup_left  := λ a b, le_Inf' $ λ x ⟨ha, hb⟩, ha,
  le_sup_right := λ a b, le_Inf' $ λ x ⟨ha, hb⟩, hb,
  sup_le       := λ a b c h₁ h₂, Inf_le' ⟨h₁, h₂⟩,
  inf          := (⊓),
  le_inf       := λ a b c ha hb, set.subset_inter ha hb,
  inf_le_left  := λ a b, set.inter_subset_left _ _,
  inf_le_right := λ a b, set.inter_subset_right _ _, ..submonoid.partial_order}

instance : complete_lattice (submonoid M) :=
{ Sup          := λ tt, Inf {t | ∀t'∈tt, t' ≤ t},
  le_Sup       := λ s p hs, le_Inf' $ λ p' hp', hp' _ hs,
  Sup_le       := λ s p hs, Inf_le' hs,
  Inf          := Inf,
  le_Inf       := λ s a, le_Inf',
  Inf_le       := λ s a, Inf_le',
  ..submonoid.lattice.order_top,
  ..submonoid.lattice.order_bot,
  ..submonoid.lattice.lattice}

instance : add_comm_monoid (submonoid M) :=
{ add := (⊔),
  add_assoc := λ _ _ _, sup_assoc,
  zero := ⊥,
  zero_add := λ _, bot_sup_eq,
  add_zero := λ _, sup_bot_eq,
  add_comm := λ _ _, sup_comm }

end submonoid

namespace monoid_hom

variables {M : Type*} [monoid M] (S : submonoid M)

open submonoid

-- used to be "preimage"
/-- The preimage of a submonoid along a monoid homomorphism is a submonoid. -/
def comap {N : Type*} [monoid N] (f : M →* N)
  (S : submonoid N) : submonoid M :=
{ carrier := (f ⁻¹' S),
  one_mem' := show f 1 ∈ S, by rw f.map_one; exact S.one_mem,
  mul_mem' := λ a b ha hb,
    show f (a * b) ∈ S, by rw f.map_mul; exact S.mul_mem ha hb }

-- used to be "image"
--@[instance, to_additive image.is_add_submonoid]
/-- The image of a submonoid along a monoid homomorphism is a submonoid. -/
def map {N : Type*} [monoid N] (f : M →* N) (S : submonoid M) : submonoid N :=
{ carrier := (f '' S),
  one_mem' := ⟨1, S.one_mem, f.map_one⟩,
  mul_mem' := begin rintros _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩, exact ⟨x * y, S.mul_mem hx hy,
    by rw f.map_mul; refl⟩ end }

/-- The range of a monoid homomorphism is a submonoid. -/
def range {N : Type*} [monoid N] (f : M →* N) :
  submonoid N := map f univ

end monoid_hom

namespace submonoid

variables {M : Type*} [monoid M] (S : submonoid M)

lemma pow_mem {a : M} (h : a ∈ S) : ∀ {n : ℕ}, a ^ n ∈ S
| 0 := S.one_mem
| (n + 1) := S.mul_mem h pow_mem

--lemma is_add_submonoid.smul_mem {a : β} [is_add_submonoid t] :
--  ∀ (h : a ∈ t) {n : ℕ}, add_monoid.smul n a ∈ t :=
--@is_submonoid.pow_mem (multiplicative β) _ _ _ _
--attribute [to_additive is_add_submonoid.smul_mem] is_submonoid.pow_mem

lemma power_subset {a : M} (h : a ∈ S) : powers a ≤ S :=
assume x ⟨n, hx⟩, hx ▸ S.pow_mem h

--lemma is_add_submonoid.multiple_subset {a : β} [is_add_submonoid t] :
--  a ∈ t → multiples a ⊆ t :=
--@is_submonoid.power_subset (multiplicative β) _ _ _ _
--attribute [to_additive is_add_submonoid.multiple_subset] is_add_submonoid.multiple_subset

--@[to_additive is_add_submonoid.list_sum_mem]
lemma list_prod_mem : ∀ {l : list M}, (∀x∈l, x ∈ S) → l.prod ∈ S
| []     h := S.one_mem
| (a::l) h :=
  suffices a * l.prod ∈ S, by simpa,
  have a ∈ S ∧ (∀ x ∈ l, x ∈ S), by simpa using h,
  S.mul_mem this.1 (list_prod_mem this.2)

--@[to_additive is_add_submonoid.multiset_sum_mem]
lemma multiset_prod_mem {M} [comm_monoid M] (S : submonoid M) (m : multiset M) :
  (∀a ∈ m, a ∈ S) → m.prod ∈ S :=
begin
  refine quotient.induction_on m (assume l hl, _),
  rw [multiset.quot_mk_to_coe, multiset.coe_prod],
  exact S.list_prod_mem hl
end

--@[to_additive is_add_submonoid.finset_sum_mem]
lemma finset_prod_mem {M ι} [comm_monoid M] (S : submonoid M) (f : ι → M) :
  ∀(t : finset ι), (∀b∈t, f b ∈ S) → t.prod f ∈ S
| ⟨m, hm⟩ hs :=
  begin
    refine S.multiset_prod_mem _ _,
    suffices : ∀ (a : M) (x : ι), x ∈ m → f x = a → a ∈ S,
      simpa using this,
    rintros a b hb rfl,
    exact hs _ hb
  end

instance : has_mul S := ⟨λ a b, ⟨a.1 * b.1, S.mul_mem a.2 b.2⟩⟩
instance : has_one S := ⟨⟨_, S.one_mem⟩⟩

@[simp] lemma coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y := rfl
@[simp] lemma coe_one : ((1 : S) : M) = 1 := rfl

instance to_monoid {M : Type*} [monoid M] {S : submonoid M} : monoid S :=
by refine { mul := (*), one := 1, ..}; by simp [mul_assoc]

@[simp] lemma coe_pow (a : S) (n : ℕ) : ((a ^ n : S) : M) = a ^ n :=
by induction n; simp [*, pow_succ]

def subtype : S →* M :=
{ to_fun := coe,
  map_one' := rfl,
  map_mul' := λ _ _, rfl }

@[simp] theorem subtype_apply (x : S) : S.subtype x = x := rfl

lemma subtype_eq_val : (S.subtype : S → M) = subtype.val := rfl

end submonoid

namespace monoid_hom

variables {M : Type*} [monoid M] (S : submonoid M)

def subtype_mk {N : Type*} [monoid N] (f : N →* M) (h : ∀ x, f x ∈ S) : N →* S :=
{ to_fun := λ n, ⟨f n, h n⟩,
  map_one' := subtype.eq (is_monoid_hom.map_one f),
  map_mul' := λ x y, subtype.eq (is_monoid_hom.map_mul f x y) }

def set_inclusion (T : submonoid M) (h : S ≤ T) : S →* T :=
subtype_mk _ S.subtype (λ x, h x.2)

end monoid_hom

namespace monoid

variables {M : Type*} [monoid M] (S : submonoid M)

open submonoid

def closure' (s : set M) : submonoid M :=
{ carrier := in_closure s,
  one_mem' := in_closure.one s,
  mul_mem' := λ _ _, in_closure.mul}

theorem le_closure' {s : set M} : s ≤ closure' s :=
λ a, in_closure.basic

theorem closure'_le {s : set M} {T : submonoid M} (h : s ≤ T) : closure' s ≤ T :=
λ a ha, begin induction ha with _ hb _ _ _ _ ha hb,
  {exact h hb },
  {exact T.one_mem },
  {exact T.mul_mem ha hb }
end

theorem closure'_mono {s t : set M} (h : s ≤ t) : closure' s ≤ closure' t :=
closure'_le $ set.subset.trans h le_closure'

theorem closure'_singleton {x : M} : closure' ({x} : set M) = powers x :=
ext' $ set.eq_of_subset_of_subset (closure'_le $ set.singleton_subset_iff.2 powers.self_mem) $
submonoid.power_subset _ $ in_closure.basic $ set.mem_singleton x

lemma image_closure' {N : Type*} [monoid N] (f : M →* N) (s : set M) :
  f.map (closure' s) = closure' (f '' s) :=
le_antisymm
  begin
    rintros _ ⟨x, hx, rfl⟩,
    apply in_closure.rec_on hx; intros,
    { solve_by_elim [le_closure', set.mem_image_of_mem] },
    { rw f.map_one, apply submonoid.one_mem },
    { rw f.map_mul, solve_by_elim [submonoid.mul_mem] }
  end
  (closure'_le $ set.image_subset _ le_closure')

theorem exists_list_of_mem_closure' {s : set M} {a : M} (h : a ∈ closure' s) :
  (∃l:list M, (∀x∈l, x ∈ s) ∧ l.prod = a) :=
begin
  induction h,
  case in_closure.basic : a ha { existsi ([a]), simp [ha] },
  case in_closure.one { existsi ([]), simp },
  case in_closure.mul : a b _ _ ha hb {
    rcases ha with ⟨la, ha, eqa⟩,
    rcases hb with ⟨lb, hb, eqb⟩,
    existsi (la ++ lb),
    simp [eqa.symm, eqb.symm, or_imp_distrib],
    exact assume a, ⟨ha a, hb a⟩
  }
end

theorem mem_closure'_union_iff {M : Type*} [comm_monoid M] {s t : set M} {x : M} :
  x ∈ closure' (s ∪ t) ↔ ∃ y ∈ closure' s, ∃ z ∈ closure' t, y * z = x :=
⟨λ hx, let ⟨L, HL1, HL2⟩ := exists_list_of_mem_closure' hx in HL2 ▸
  list.rec_on L (λ _, ⟨1, submonoid.one_mem _, 1, submonoid.one_mem _, mul_one _⟩)
    (λ hd tl ih HL1, let ⟨y, hy, z, hz, hyzx⟩ := ih (list.forall_mem_of_forall_mem_cons HL1) in
      or.cases_on (HL1 hd $ list.mem_cons_self _ _)
        (λ hs, ⟨hd * y, submonoid.mul_mem _ (le_closure' hs) hy, z, hz,
          by rw [mul_assoc, list.prod_cons, ← hyzx]; refl⟩)
        (λ ht, ⟨y, hy, z * hd, submonoid.mul_mem _ hz (le_closure' ht),
          by rw [← mul_assoc, list.prod_cons, ← hyzx, mul_comm hd]; refl⟩)) HL1,
λ ⟨y, hy, z, hz, hyzx⟩, hyzx ▸ submonoid.mul_mem _
  ((closure_mono (set.subset_union_left s t)) hy)
  ((closure_mono (set.subset_union_right s t)) hz)⟩

end monoid

/-

-- some stuff from is_submonoid which might need to be put into this language:

namespace add_monoid

--def closure (s : set β) : set β := @monoid.closure (multiplicative β) _ s
--attribute [to_additive add_monoid.closure] monoid.closure

instance closure.is_add_submonoid (s : set β) : is_add_submonoid (closure s) :=
multiplicative.is_submonoid_iff.1 $ monoid.closure.is_submonoid s
attribute [to_additive add_monoid.closure.is_add_submonoid] monoid.closure.is_submonoid

theorem subset_closure {s : set β} : s ⊆ closure s :=
monoid.subset_closure
attribute [to_additive add_monoid.subset_closure] monoid.subset_closure

theorem closure_subset {s t : set β} [is_add_submonoid t] : s ⊆ t → closure s ⊆ t :=
monoid.closure_subset
attribute [to_additive add_monoid.closure_subset] monoid.closure_subset

theorem closure_mono {s t : set β} (h : s ⊆ t) : closure s ⊆ closure t :=
closure_subset $ set.subset.trans h subset_closure
attribute [to_additive add_monoid.closure_mono] monoid.closure_mono

theorem closure_singleton {x : β} : closure ({x} : set β) = multiples x :=
monoid.closure_singleton
attribute [to_additive add_monoid.closure_singleton] monoid.closure_singleton

theorem exists_list_of_mem_closure {s : set β} {a : β} :
  a ∈ closure s → ∃l:list β, (∀x∈l, x ∈ s) ∧ l.sum = a :=
monoid.exists_list_of_mem_closure
attribute [to_additive add_monoid.exists_list_of_mem_closure] monoid.exists_list_of_mem_closure

@[elab_as_eliminator]
theorem in_closure.rec_on {s : set β} {C : β → Prop}
  {a : β} (H : a ∈ closure s)
  (H1 : ∀ {a : β}, a ∈ s → C a) (H2 : C 0)
  (H3 : ∀ {a b : β}, a ∈ closure s → b ∈ closure s → C a → C b → C (a + b)) :
  C a :=
monoid.in_closure.rec_on H (λ _, H1) H2 (λ _ _, H3)

lemma image_closure {γ : Type*} [add_monoid γ] (f : β → γ) [is_add_monoid_hom f] (s : set β) :
  f '' closure s = closure (f '' s) :=
le_antisymm
  begin
    rintros _ ⟨x, hx, rfl⟩,
    apply in_closure.rec_on hx; intros,
    { solve_by_elim [subset_closure, set.mem_image_of_mem] },
    { rw [is_add_monoid_hom.map_zero f], apply is_add_submonoid.zero_mem },
    { rw [is_add_monoid_hom.map_add f], solve_by_elim [is_add_submonoid.add_mem] }
  end
  (closure_subset $ set.image_subset _ subset_closure)
attribute [to_additive add_monoid.image_closure] monoid.image_closure

theorem mem_closure_union_iff {β : Type*} [add_comm_monoid β] {s t : set β} {x : β} :
  x ∈ closure (s ∪ t) ↔ ∃ y ∈ closure s, ∃ z ∈ closure t, y + z = x :=
monoid.mem_closure_union_iff

end add_monoid
-/
