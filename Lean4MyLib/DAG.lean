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

/-- `ignoreOneElement` 済みの `target` を物理削除して `n-1` に詰める。--/
def compressOne {A} {n : Nat} (g : SDAG A n) (target : Fin n) : SDAG A (n - 1) :=
by
  classical
  -- 新しい添字 i' を元の添字へ戻す写像
  let oldOf : Fin (n - 1) → Fin n :=
    fun i' =>
      if h : i'.val < target.val then
        ⟨i'.val, by
          -- i' < target < n
          exact sorry⟩
      else
        ⟨i'.val + 1, by
          -- target ≤ i' < n-1+? ⇒ i'+1 < n
          exact sorry⟩
  -- 元の添字を新しい添字へ送る写像（target は落とす）
  let toNew : Fin n → Option (Fin (n - 1)) :=
    fun i =>
      if hlt : i.val < target.val then
        some ⟨i.val, by
          -- i < target ≤ n-1
          exact sorry⟩
      else if heq : i = target then
        none
      else
        some ⟨i.val - 1, by
          -- target < i < n ⇒ i-1 < n-1
          exact sorry⟩
  refine
  { label := fun i' => g.label (oldOf i'),
    children := fun i' =>
      let j := oldOf i'
      (g.children j).filterMap (fun c =>
        let old := SDAG.coeChild j c          -- : Fin n
        match toNew old with
        | none      => none
        | some new =>
          -- new < i' （順序保存性）を示して局所添字へ落とす
          have hlt : new.val < i'.val := by
            -- ここは `c.isLt` と `oldOf` / `toNew` の場合分けから従う
            exact sorry
          some (Fin.castLT new hlt)) }
end SDAG

def DAGWithFilter.of{A} : (d : DAG A) → (A×(Fin d.1) → Bool) → DAGWithFilter A
| ⟨n, G⟩, pred =>
  ⟨n, { base := G, allow := fun i => pred ((G.label i), i)}⟩


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
