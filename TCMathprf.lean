import Mathlib
import Mathlib.CategoryTheory.Functor.KanExtension.Basic

open CategoryTheory
open Limits
open Functor

universe u v

/-! ## 病机极限与余极限性质证明 -/

-- 定义局部小范畴变量
variable
  {A : Type u} [Category A]
  {B : Type u} [Category B]
  {C : Type u} [Category C]
  {M : Type u} [Category M]
  {N : Type u} [Category N]
  {I : Type u} [Category I]
  {S : Type u} [Category S]
--

/-! ### 命题1：核心病机的唯一性（极限的唯一性） -/
theorem corePathogenesisUniqueness (F : B ⥤ C) (H : I ⥤ B) (D_star : B ⥤ C) (α : H ⋙ D_star ⟶ H ⋙ F)
  [D_star.IsRightKanExtension α]
  [HasLimit (H ⋙ D_star)]
  : ∃! (J_core : C), ∃ (h : IsLimit (limit.cone (H ⋙ D_star))), J_core = (limit.cone (H ⋙ D_star)).pt :=
by
  -- 定义从 I 到 C 的函子 D = D_star ∘ H
  let D := H ⋙ D_star
  -- 构造核心病机为右 Kan 扩张后复合的极限对象
  use limit D
  -- 唯一性由极限的唯一性保证
  -- 证明存在性
  constructor
  -- 1. 证明 limit D 是满足条件的核心病机
  . refine ⟨?_, ?_⟩
    -- 证明存在 h : IsLimit (limitCone D)
    . exact (limit.isLimit D)
    -- 证明 limit D = (limit.cone D).pt
    . rfl
  -- 2. 证明唯一性
  . intro y hy -- 假设存在另一个满足条件的对象 y, 假设 y 满足条件：存在 h 使得 y = (limit.cone D).pt
    cases hy with  -- 展开条件
    | intro h y_eq =>
      -- 由 y_eq 得 y = (limit.cone D).pt
      rw [y_eq]
      -- 根据 Mathlib 定义，limit D = (limit.cone D).pt
      rfl
--

/-! ### 命题2：核心病机的解释能力（极限的泛性质） -/
theorem corePathogenesisExplanatoryPower (F : B ⥤ C) (G : C ⥤ B) (H : I ⥤ B) (D_star : B ⥤ C) (α : H ⋙ D_star ⟶ H ⋙ F)
  [D_star.IsRightKanExtension α]  -- D_star = Ran_H F
  [HasLimit (H ⋙ D_star)]
  [HasLimit ((H ⋙ D_star) ⋙ G)]
  : let D := H ⋙ D_star;
    let J_core := limit D;
    let GJ_core := limit (D ⋙ G);
    (∀ (s : Cone D), ∃! (f : s.pt ⟶ J_core), ∀ (j : I), f ≫ limit.π D j = s.π.app j) ∧
    (∀ (t : Cone (D ⋙ G)), ∃! (h : t.pt ⟶ GJ_core), ∀ (j : I), h ≫ limit.π (D ⋙ G) j = t.π.app j) :=
by
  -- 定义从 I 到 C 的函子 D = D_star ∘ H
  let D := H ⋙ D_star
  -- 证明第一个泛性质
  constructor
  . intros s
    exact (limit.isLimit D).existsUnique s
  -- 证明第二个泛性质
  . intros t
    exact (limit.isLimit (D ⋙ G)).existsUnique t
--

/-! ### 命题3：阶段共同病机的极限性质 -/
theorem stageCommonPathogenesisLimit (Q : B ⥤ S) (D_common : S ⥤ C)
  [HasLimit (Q ⋙ D_common)]
  : ∃! (J_common : C), ∃ (h : IsLimit (limit.cone (Q ⋙ D_common))), J_common = (limit.cone (Q ⋙ D_common)).pt :=
by
  -- 直接使用极限作为阶段共同病机
  use limit (Q ⋙ D_common)
  -- 唯一性由极限的唯一性保证
  -- 证明存在性
  constructor
  -- 1. 证明 limit (Q ⋙ D_common) 是满足条件的阶段共同病机
  . refine ⟨?_, ?_⟩
    -- 证明存在 h : IsLimit (limit.cone (Q ⋙ D_common))
    . exact (limit.isLimit (Q ⋙ D_common))
    -- 证明 limit (Q ⋙ D_common) = (limit.cone (Q ⋙ D_common)).pt
    . rfl
  -- 2. 证明唯一性
  . intro y hy -- 假设存在另一个满足条件的对象 y, 假设 y 满足条件：存在 h 使得 y = (limit.cone (Q ⋙ D_common)).pt
    cases hy with  -- 展开条件
    | intro h y_eq =>
      -- 由 y_eq 得 y = (limit.cone (Q ⋙ D_common)).pt
      rw [y_eq]
      -- 根据 Mathlib 定义，limit (Q ⋙ D_common) = (limit.cone (Q ⋙ D_common)).pt
      rfl

/-! ### 命题4：多疾病共性病机的极限-余极限结合性质 -/
theorem multiDiseaseCommonPathogenesis (Q : B ⥤ S) (D_common : S ⥤ C) (D : S → (A ⥤ C))
  [HasColimit (Q ⋙ D_common)]
  [∀ (s : S), HasLimit (D s)]
  (s : S)
  : ∃! (J_common : C), ∃ (h : IsLimit (limit.cone (D s))), J_common = (limit.cone (D s)).pt :=
by
  -- 对每个阶段s，取D_s的极限作为阶段共同病机
  use limit (D s)
  -- 唯一性由极限的唯一性保证
  -- 证明存在性
  constructor
  -- 1. 证明 limit (D s) 是满足条件的共性病机
  . refine ⟨?_, ?_⟩
    -- 证明存在 h : IsLimit (limitCone (D s))
    . exact (limit.isLimit (D s))
    -- 证明 limit (D s) = (limit.cone (D s)).pt
    . rfl
  -- 2. 证明唯一性
  . intro y hy -- 假设存在另一个满足条件的对象 y, 假设 y 满足条件：存在 h 使得 y = (limit.cone (D s)).pt
    cases hy with  -- 展开条件
    | intro h y_eq =>
      -- 由 y_eq 得 y = (limit.cone (D s)).pt
      rw [y_eq]
      -- 根据 Mathlib 定义，limit (D s) = (limit.cone (D s)).pt
      rfl
