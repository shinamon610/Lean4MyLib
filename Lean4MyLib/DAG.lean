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
end SDAG

def DAGWithFilter.of{A} : (d : DAG A) → (A×(Fin d.1) → Bool) → DAGWithFilter A
| ⟨n, G⟩, pred =>
  ⟨n, { base := G, allow := fun i => pred ((G.label i), i)}⟩

private partial def inner_toJsonByLabel {A} [ToString A] [ToJson A] (g:SDAGWithFilter A n) (i:Fin n): Json:=
  let k : String := toString (g.base.label i)
  let deps : List Json :=
    (g.base.children i).map (fun c =>
      let j := SDAG.coeChild i c
      inner_toJsonByLabel g j
      )
  let base:= toJson (g.base.label i)
  mkObj [ (k, base.mergeObj (mkObj [("deps", Json.arr deps.toArray)]))]

def toJsonByLabel {A} [ToString A] [ToJson A] :DAGWithFilter A -> Json
| ⟨_ , g⟩ =>
  let roots := (SDAG.roots g.base).filter g.allow
  let entries : List Json := roots.map (inner_toJsonByLabel g)
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
