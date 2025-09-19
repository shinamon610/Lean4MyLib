import Std
import Lean.Util.FoldConsts
import Mathlib.Data.Fin.Basic
import Lean

open Lean
open Lean.Json

open Std
open Std.Time
open Lean Meta

structure SDAG (A : Type) (n : Nat) where
  label    : Fin n → A
  children : (i : Fin n) → List (Fin i)

abbrev DAG (A : Type) := Σ n, SDAG A n
abbrev filteredDAG (A : Type) := Σ n, (SDAG A n × List (Fin n))

def emptySDAG (A : Type) : SDAG A 0 where
  label    i := nomatch i
  children i := nomatch i

def emptyDAG (A : Type) : DAG A :=
  ⟨0, emptySDAG A⟩

instance instInhabitedSigmaSDAG (A : Type) : Inhabited (DAG A) where
  default := emptyDAG A

-- filter 付きDAG
structure SDAGWithFilter (A : Type) (n : Nat) where
  base  : SDAG A n
  allow : Fin n → Bool   -- 非フィルタは `fun _ => true`
abbrev DAGWithFilter (A : Type) := Σ n, SDAGWithFilter  A n


namespace SDAG

-- Std.Format.joinSepは、StringじゃなくてFormatを返す。
-- 書きにくいので、自前で定義している。
private def joinSep (sep : String) (xs:List String): String := (Std.Format.joinSep xs (Format.text sep)).pretty

/-- `c : Fin i` を「全体サイズ」`Fin n` に埋め込む（`c.val < i.val < n`） -/
def coeChild {n} (i : Fin n) (c : Fin i) : Fin n :=
  ⟨c.val, Nat.lt_trans c.isLt i.isLt⟩

/-- エッジ一覧 `i → j` を収集 -/
def edges {A n} (g : SDAG A n) : List (Fin n × Fin n) :=
   (List.finRange n).flatMap  (fun i =>
    (g.children i).map (fun c => (i, coeChild i c)))

/-- 子として登場するノードの集合（Natの値で持つ） -/
private def childNats {A n} (g : SDAG A n) : List Nat :=
  (g.edges).map (fun e => (e.snd : Fin n).val)

/-- 親を持たないノード（root）だけを返す -/
def roots {A n} (g : SDAG A n) : List (Fin n) :=
  let cs := g.childNats
  (List.finRange n).filter (fun i => !(cs.contains i.val))

-- あるnodeの親全部
def parents {A n} (g : SDAG A n) (j : Fin n) : List (Fin n) :=
  (List.finRange n).filter (fun i =>
    (g.children i).any (fun c => SDAG.coeChild i c == j))

-- 先祖全部
partial def ancestors {A n} (g : SDAG A n) (j : Fin n) : List (Fin n) :=
  let ps := g.parents j
  ps.flatMap (fun x => g.ancestors x)

def «隣接行列表示» {A n} [Repr A] (g : SDAG A n) : String :=
  let nodeStr (i : Fin n) : String := s!"{(i : Nat)}:{reprStr (g.label i)}"
  let lines :=
    (List.finRange n).map (fun i =>
      let kids := (g.children i).map (fun c =>
        let j := coeChild i c
        s!"{(j : Nat)}:{reprStr (g.label j)}")
      s!"{nodeStr i} -> [{joinSep ", " kids}]")
  joinSep "\n" lines

/-- i < j のとき `Fin i → Fin j` への持ち上げ -/
private def liftTo {n} {i j : Fin n} (h : i.val < j.val) (c : Fin i) : Fin j :=
  ⟨c.val, Nat.lt_trans c.isLt h⟩

def ignoreOne {A n}
  (g : SDAG A n) (target : Fin n) : SDAG A n :=
{
  label := g.label,
  children := fun fin =>
    if h : ∃ c : Fin fin, coeChild fin c = target then
      let c  : Fin fin := Classical.choose h
      have hc : SDAG.coeChild fin c = target := Classical.choose_spec h
      have hval : target.val = c.val := by
        have h':= congrArg Fin.val hc
        simp [coeChild] at h'
        exact h'.symm
      have hlt  : target.val < fin.val := by simp [hval]
      let up : Fin target → Fin fin := fun d => liftTo hlt d
      (g.children fin ++ (g.children target).map up).filter (fun x => coeChild fin x != target)
    else
      g.children fin
}

theorem lt_of_lt_targetVal {n} (target : Fin n) {k : Nat}
  (h : k < target.val) : k < n :=
Nat.lt_trans h target.isLt

theorem pos_of_fin_pred {n} (i' : Fin (n - 1)) : 0 < n :=
by
  have h0 : 0 ≤ i'.val := Nat.zero_le _
  have h1 : 0 < n - 1 := lt_of_le_of_lt h0 i'.isLt
  exact lt_of_lt_of_le h1 (Nat.sub_le _ _)

theorem sub_one_lt {n : Nat} (hn : 0 < n) : n - 1 < n :=
by
  cases n with
  | zero => cases hn
  | succ n' =>
      simp [Nat.add_one_sub_one, Nat.lt_add_one]

/-- `i' : Fin (n-1)` なら `i'.val + 1 < n`. -/
theorem add_one_lt_of_fin_pred {n} (i' : Fin (n - 1)) : i'.val + 1 < n :=
by
  have h1 : i'.val + 1 ≤ n - 1 := Nat.succ_le_of_lt i'.isLt
  have h2 : n - 1 < n := sub_one_lt (pos_of_fin_pred i')
  exact lt_of_le_of_lt h1 h2

theorem val_le_pred_of_fin {n} (t : Fin n) : t.val ≤ n - 1 := by
  cases n with
  | zero => cases t with
      | mk val hlt => cases (Nat.not_lt_zero _ hlt)
  | succ m =>
      have : t.val ≤ m := Nat.le_of_lt_succ t.isLt
      simpa using this
theorem val_ne_of_ne {n} {i j : Fin n} (hne : i ≠ j) : i.val ≠ j.val :=
by
  intro h
  exact hne (Fin.ext h)
theorem pred_lt_pred_of_lt_of_pos {i n : Nat}
  (hi : i < n) (ipos : 0 < i) : i - 1 < n - 1 :=
by
  cases i with
  | zero => cases ipos
  | succ k =>
    cases n with
    | zero => cases hi
    | succ m =>
      have hk : k < m := Nat.succ_lt_succ_iff.mp hi
      simpa using hk

theorem pred_bound_for_else {n} {i target : Fin n}
  (hlt : ¬ i.val < target.val) (hne : i ≠ target) : i.val - 1 < n - 1 :=
by
  -- target.val ≤ i.val
  have hge : target.val ≤ i.val := le_of_not_gt hlt
  -- target.val ≠ i.val
  have hneq_val : target.val ≠ i.val := by
    intro h; exact hne (by simpa using (Fin.ext h).symm)
  -- target.val < i.val
  have htlt : target.val < i.val := lt_of_le_of_ne hge hneq_val
  -- 0 < i.val
  have hipos : 0 < i.val := lt_of_le_of_lt (Nat.zero_le _) htlt
  -- i.val < n
  have hin : i.val < n := i.isLt
  -- そのまま適用
  exact pred_lt_pred_of_lt_of_pos hin hipos

/-- `toNew old = some new` と `old.val < (oldOf i').val` から `new.val < i'.val`。 -/
theorem toNew_val_lt_of_child
  {n : Nat} (target : Fin n) {i' : Fin (n - 1)}
  {old : Fin n} {new : Fin (n - 1)}
  (oldOf : Fin (n - 1) → Fin n)
  (toNew : Fin n → Option (Fin (n - 1)))
  (hOld : ∀ j : Fin (n - 1),
    oldOf j =
      (if h : j.val < target.val then
         ⟨j.val, lt_of_lt_targetVal target h⟩
       else
         ⟨j.val + 1, add_one_lt_of_fin_pred j⟩))
  (hNew : ∀ i : Fin n,
    toNew i =
      (if hlt : i.val < target.val then
         some ⟨i.val, lt_of_lt_of_le hlt (val_le_pred_of_fin target)⟩
       else if heq : i = target then
         none
       else
         some ⟨i.val - 1, pred_bound_for_else (hlt := hlt) (hne := heq)⟩))
  (hchild : old.val < (oldOf i').val)
  (hSome : toNew old = some new)
  : new.val < i'.val := by
  have hOld' := hOld i'
  have hNew' := hNew old
  by_cases hi : i'.val < target.val
  · have hchild' : old.val < i'.val := by
      simpa [hOld', hi] using hchild
    by_cases hold_lt : old.val < target.val
    · -- 第1枝: new.val = old.val
      have hs :
          some new
            = some ⟨old.val, lt_of_lt_of_le hold_lt (val_le_pred_of_fin target)⟩ := by
        simpa [hNew', hold_lt] using hSome.symm
      have hnew_eq :
          new = ⟨old.val, lt_of_lt_of_le hold_lt (val_le_pred_of_fin target)⟩ :=
        Option.some.inj hs
      have hval : new.val = old.val := by
        simpa using congrArg Fin.val hnew_eq
      simpa [hval] using hchild'
    · -- 不可能枝（`old ≥ target > i'` が `old < i'` と矛盾）
      have : old.val < target.val := lt_trans hchild' hi
      exact (hold_lt this).elim
  · -- `target.val ≤ i'.val`
    have hi_ge : target.val ≤ i'.val := le_of_not_gt hi
    have hchild' : old.val < i'.val + 1 := by
      simpa [hOld', hi] using hchild
    have hold_le_i' : old.val ≤ i'.val := Nat.lt_succ_iff.mp hchild'
    by_cases hold_lt : old.val < target.val
    · -- 第1枝: new.val = old.val
      have hs :
          some new
            = some ⟨old.val, lt_of_lt_of_le hold_lt (val_le_pred_of_fin target)⟩ := by
        simpa [hNew', hold_lt] using hSome.symm
      have hnew_eq :
          new = ⟨old.val, lt_of_lt_of_le hold_lt (val_le_pred_of_fin target)⟩ :=
        Option.some.inj hs
      have hval : new.val = old.val := by
        simpa using congrArg Fin.val hnew_eq
      have : old.val < i'.val := lt_of_lt_of_le hold_lt hi_ge
      simpa [hval] using this
    · -- `old ≥ target`
      by_cases heq : old = target
      · subst heq; simp [hNew'] at hSome
      · -- 第3枝: new.val = old.val - 1
        have hs :
            some new
              = some ⟨old.val - 1, pred_bound_for_else (hlt := hold_lt) (hne := heq)⟩ := by
          simpa [hNew', hold_lt, heq] using hSome.symm
        have hnew_eq :
            new = ⟨old.val - 1, pred_bound_for_else (hlt := hold_lt) (hne := heq)⟩ :=
          Option.some.inj hs
        have hval : new.val = old.val - 1 := by
          simpa using congrArg Fin.val hnew_eq
        -- まず `0 < old.val`
        have hold_pos : 0 < old.val := by
          by_cases htz : target.val = 0
          · have hne0 : old.val ≠ 0 := by
              intro hz; apply heq; apply Fin.ext; simp [hz, htz]
            exact Nat.pos_of_ne_zero hne0
          · have htpos : 0 < target.val := Nat.pos_of_ne_zero htz
            exact lt_of_lt_of_le htpos (le_of_not_gt hold_lt)
        -- `old.val - 1 < old.val`
        have hpred_lt_old : old.val - 1 < old.val := by simpa using Nat.pred_lt (ne_of_gt hold_pos)
        have : old.val - 1 < i'.val := lt_of_lt_of_le hpred_lt_old hold_le_i'
        simpa [hval] using this

def compressOne {A} {n : Nat} (g : SDAG A n) (target : Fin n) : SDAG A (n - 1) :=
by
  classical
  -- 新しい添字 i' を元の添字へ戻す写像
  let oldOf : Fin (n - 1) → Fin n :=
    fun i' =>
      if h : i'.val < target.val then
        ⟨i'.val, by exact lt_of_lt_targetVal target h⟩
      else
        ⟨i'.val + 1, by exact add_one_lt_of_fin_pred i'⟩
  -- 元の添字を新しい添字へ送る写像（target は落とす）
  let toNew : Fin n → Option (Fin (n - 1)) :=
    fun i =>
      if hlt : i.val < target.val then
        some ⟨i.val,by exact lt_of_lt_of_le hlt (val_le_pred_of_fin target)⟩
      else if heq : i = target then
        none
      else
        some ⟨i.val - 1, by exact pred_bound_for_else (hlt := hlt) (hne := heq)⟩
  refine
  { label := fun i' => g.label (oldOf i'),
    children := fun i' =>
      let j := oldOf i'
      (g.children j).filterMap (fun c =>
        let old := SDAG.coeChild j c          -- : Fin n
        match hSome : toNew old with
        | none      => none
        | some new =>
          have hchild : old.val < (oldOf i').val := by
            -- c.isLt : coeChild j c).val < j.val を持っているはず
            -- j = oldOf i' なので書き換え
            simp [old, j, SDAG.coeChild]

          have hlt :
              new.val < i'.val :=
            toNew_val_lt_of_child
              (target := target) (i' := i') (old := old) (new := new)
              oldOf toNew
              (by intro j; rfl)            -- hOld
              (by intro i; rfl)            -- hNew
              hchild                        -- old.val < (oldOf i').val
              hSome                        -- toNew old = some new
          some (Fin.castLT new hlt)
      )
  }
end SDAG

def DAGWithFilter.of{A} : (d : DAG A) → (A×(Fin d.1) → Bool) → DAGWithFilter A
| ⟨n, G⟩, pred =>
  ⟨n, { base := G, allow := fun i => pred ((G.label i), i)}⟩


partial def DAGWithFilter.compress (dagwf : DAGWithFilter A) : DAG A :=
match dagwf with
| ⟨n, sdagwf⟩ =>
  let unallowed0 : List (Fin n) :=
    (List.finRange n).filter (fun i => !(sdagwf.allow i))
  -- ignore はサイズ不変なので foldl でよい
  let ignored : SDAG A n :=
    unallowed0.foldl (fun acc fin => acc.ignoreOne fin) sdagwf.base
  -- サイズ可変の圧縮を List 上で再帰
  let rec go {m : Nat} (acc : SDAG A m) :
      List (Fin m) → Σ k, SDAG A k
    | [] => ⟨m, acc⟩
    | t :: ts =>
      -- 次の圧縮後に残リストの添字を m → m-1 へ写す
      let toNew : Fin m → Option (Fin (m - 1)) :=
        fun i =>
          if hlt : i.val < t.val then
            some ⟨i.val, by exact lt_of_lt_of_le hlt (SDAG.val_le_pred_of_fin t)⟩
          else if heq : i = t then
            none
          else
            some ⟨i.val - 1, by exact SDAG.pred_bound_for_else (hlt := hlt) (hne := heq)⟩
      let acc' := acc.compressOne t
      let ts'  := ts.filterMap toNew     -- t を落とし、以降をデクリメント
      go acc' ts'
  let ⟨m, compressed⟩ := go ignored unallowed0
  ⟨m, compressed⟩

private partial def innerToJsonByLabel {A} [ToString A] [ToJson A] (g:SDAG A n) (i:Fin n): Json:=
  let k : String := toString (g.label i)
  let deps : List Json :=
    (g.children i).map (fun c =>
      let j := SDAG.coeChild i c
      innerToJsonByLabel g j
      )
  let base:= toJson (g.label i)
  mkObj [ (k, base.mergeObj (mkObj [("1deps", Json.arr deps.toArray)]))] -- sort順指定のために 1を入れている

def toJsonByLabel {A} [ToString A] [ToJson A] :DAG A -> Json
| ⟨_ , g⟩ =>
  let roots := (SDAG.roots g)
  let entries : List Json := roots.map (innerToJsonByLabel g)
  Json.arr entries.toArray

-- 最小テスト: 2ノード(1→0)。ノード0を不許可にして `compress` で削除。
-- 期待: 残るのは元1のみ。表示は `0:1 -> []`。
namespace TestCompress

open SDAG

def tinySDAG : SDAG String 5 where
  label
    | ⟨0, _⟩ => "C"
    | ⟨1, _⟩ => "E"
    | ⟨2, _⟩ => "B"
    | ⟨3, _⟩ => "A"
    | ⟨4, _⟩ => "D"
  children
    | ⟨0, _⟩ => []
    | ⟨1, _⟩ => []
    | ⟨2, _⟩ => [⟨0, by simp⟩,⟨1, by simp⟩]
    | ⟨3, _⟩ => [⟨2, by simp⟩]
    | ⟨4, _⟩ => [⟨2, by simp⟩]

def mkWF : DAGWithFilter String :=
  let dag := ⟨5, tinySDAG⟩
  let pred:= fun (_, i) => i != 2
  DAGWithFilter.of dag pred

def run [ToJson A] [ToString A](wf:DAGWithFilter A) : String :=
  let dag := DAGWithFilter.compress wf
  (toJsonByLabel dag).pretty

#eval IO.println (run mkWF)

-- 負荷テスト
def makeSDAG (n : Nat) : SDAG Nat n where
  label
    | ⟨i, _⟩ => i
  children
    | ⟨_, _⟩ =>[]

def mkWF50 : DAGWithFilter Nat :=
  let dag := ⟨100, makeSDAG 100⟩
  let pred:= fun (_, i) =>  i == 1 || i== 2 || i== 3 || i==5 || i==6
  DAGWithFilter.of dag pred

#eval IO.println (run mkWF50)
end TestCompress

namespace DAG
/-- `DAG` 版のラッパ -/
def «隣接行列表示» {A} [Repr A] (G : DAG A) : String :=
  match G with
  | ⟨_, g⟩ => SDAG.«隣接行列表示» g
end DAG

/- 依存を外したビルダー状態：未確定の DAG を配列で保持 -/
private structure State (A : Type) where
  labels : Array A
  kids   : Array (List Nat)   -- 子は「先に作られたノード」のインデックス
deriving Inhabited

private def State.empty {A} : State A :=
  { labels := #[], kids := #[] }

private def State.size (s : State A) : Nat := s.labels.size

abbrev SSA (A : Type) := StateM (State A)

private def okKids (n : Nat) (ks : List Nat) : Bool :=
  ks.all (fun k => decide (k < n))

-- ノード追加用の関数
def push {A} (a : A) (ks : List Nat := []) : SSA A Nat := do
  let s ← get
  let n := s.size
  set { s with labels := s.labels.push a, kids := s.kids.push ks }
  pure n

def pushU {A} (a : A) (ks : List Nat := []) : SSA A Unit := do
  let s ← get
  set { s with labels := s.labels.push a, kids := s.kids.push ks }

def pushDailyU {A} (a : A) (ks : List Nat := []) (should_append:Bool): SSA A Unit := do
  if should_append
  then pushU a ks
  else return ()

private def freeze {A} (s : State A) : DAG A :=
  let n := s.size
  -- kids の長さと n を突き合わせる
  if hk : s.kids.size = n then
    -- まず全ノードについて「子 < 親」を一括検証。壊れていれば即エラー。
    let bad? : Option (Fin n) :=
      Id.run do
        let mut bad : Option (Fin n) := none
        -- ここがポイント: Nat ではなく Fin n を回す
        for i in List.finRange n do
          -- kids へのインデックスは Fin (kids.size) が必要。hk の対称でキャスト。
          let raw : List Nat := s.kids[(Fin.cast (by simpa using hk.symm) i)]
          if ! okKids i.val raw then
            bad := some i
        pure bad
    match bad? with
    | some i => panic! s!"invalid child index at node {i.val}"
    | none   =>
      -- SDAG 構築
      let label : Fin n → A := fun i => s.labels[i]
      let children : (i : Fin n) → List (Fin i) :=
        fun i =>
          let raw : List Nat := s.kids[(Fin.cast (by simpa using hk.symm) i)]
          raw.filterMap (fun k =>
            if hki : k < i.val then some ⟨k, hki⟩ else none)
      ⟨n, { label, children }⟩
  else
    panic! s!"internal size mismatch: labels={n}, kids={s.kids.size}"

def mkDAG {A} (prog : SSA A B) : DAG A :=  (prog.run State.empty).snd |> freeze

namespace DAGWithFilter

open SDAG

/-- allow配列から old→new を作る（許可のみ連番） -/
private def buildMap (allow : Array Bool) : Array (Option Nat) × Nat :=
  Id.run do
    let mut idx := 0
    let mut m   := Array.mkEmpty allow.size
    for a in allow do
      if a then
        m := m.push (some idx); idx := idx + 1
      else
        m := m.push none
    pure (m, idx)

/-- SDAG → State コピー（証明は持たない） -/
private def toState {A} {n} (g : SDAG A n) : State A :=
  let labels : Array A := Array.ofFn (fun (i : Fin n) => g.label i)
  let kids   : Array (List Nat) :=
    Array.ofFn (fun (i : Fin n) => (g.children i).map (fun c => (c : Fin i).val))
  { labels := labels, kids := kids }

/-- 不許可ノードを通過して，子を許可ノードに張り替える（多段通過も一発） -/
private def bypassKids (kids : Array (List Nat)) (allow : Array Bool) : Array (List Nat) :=
  Id.run do
    let n := kids.size
    let mut dp : Array (List Nat) := Array.mkEmpty n
    -- i の子は < i なので，0→n-1 の順で dp を確定していけば参照は常に過去要素で完結
    for i in [0:n] do
      let raw := kids[i]!
      let expanded : List Nat :=
        raw.flatMap (fun k => if allow[k]! then [k] else dp[k]!)
      dp := dp.push expanded
    pure dp

/-- State 上で圧縮を完了し，最後に freeze で DAG へ戻す -/
def compressViaState {A} [Inhabited A] (wf : DAGWithFilter A) : DAG A :=
  match wf with
  | ⟨n, s⟩ =>
    let st0 : State A :=
      let labels := Array.ofFn (fun (i : Fin n) => s.base.label i)
      let kids   := Array.ofFn (fun (i : Fin n) => (s.base.children i).map (fun c => (c : Fin i).val))
      { labels := labels, kids := kids }

    let allow : Array Bool := Array.ofFn (fun (i : Fin n) => s.allow i)

    -- ここで一度だけバイパス展開
    let bridgedKids := bypassKids st0.kids allow

    -- allow に基づく位置圧縮マップ
    let (omap, m) :=
      Id.run do
        let mut idx := 0
        let mut m   := Array.mkEmpty allow.size
        for a in allow do
          if a then m := m.push (some idx); idx := idx + 1
          else       m := m.push none
        pure (m, idx)

    -- 新配列を一括構築（ラベルは許可のみ，子は bridged → old→new で再マップ）
    let newLabels :=
      Id.run do
        let mut acc := Array.mkEmpty m
        for i in List.finRange n do
          match omap[i.val]! with
          | some _ => acc := acc.push (st0.labels[i.val]!)
          | none   => pure ()
        pure acc
    let newKids :=
      Id.run do
        let mut acc := Array.mkEmpty m
        for i in List.finRange n do
          match omap[i.val]! with
          | some _ =>
              let ks := (bridgedKids[i.val]!).filterMap (fun k => omap[k]!)
              acc := acc.push ks
          | none   => pure ()
        pure acc

    freeze { labels := newLabels, kids := newKids }

end DAGWithFilter

namespace TestCompressViaState

open SDAG
open DAGWithFilter

def tinySDAG : SDAG String 5 where
  label
    | ⟨0, _⟩ => "C"
    | ⟨1, _⟩ => "E"
    | ⟨2, _⟩ => "B"
    | ⟨3, _⟩ => "A"
    | ⟨4, _⟩ => "D"
  children
    | ⟨0, _⟩ => []
    | ⟨1, _⟩ => []
    | ⟨2, _⟩ => [⟨0, by simp⟩,⟨1, by simp⟩]
    | ⟨3, _⟩ => [⟨2, by simp⟩]
    | ⟨4, _⟩ => [⟨2, by simp⟩]

def mkWF : DAGWithFilter String :=
  let dag := ⟨5, tinySDAG⟩
  let pred:= fun (_, i) => i != 2 && i != 3
  DAGWithFilter.of dag pred

def run [ToJson A] [ToString A][Inhabited A](wf:DAGWithFilter A) : String :=
  let dag := DAGWithFilter.compressViaState wf
  (toJsonByLabel dag).pretty

#eval IO.println (run mkWF)

end TestCompressViaState
