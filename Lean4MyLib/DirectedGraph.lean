import Std
import Lean

open Lean
open Lean.Json

open Std
open Std.Time
open Lean Meta

structure DirectedGraph (A : Type) (n : Nat) where
  label: Fin n → A
  kids : (Fin n) → List (Fin n)
/-
label.size=kids.sizeである。
なぜなら、lean4ではすべての関数は全域関数であり、Fin nはそのすべての要素について定義されていなければならないから。
sizeは存在しないけど、定義域の濃度は等しい。
これを証明しようとするとmathlib使わないといけなくてビルド長くなるから割愛。

また、これがlabelとかkidsにArrayを使っていない理由でもある。単なるArrayだとその間の要素に空きがある可能性が発生する。
-/
abbrev PackedDirectedGraph  (A : Type) := Σ n, DirectedGraph A n
namespace DirectedGraph
def empty (A : Type) : DirectedGraph A 0 where
  label    i := nomatch i
  kids i := nomatch i
end DirectedGraph
namespace PackedDirectedGraph
def empty (A : Type) : PackedDirectedGraph A :=
  ⟨0, DirectedGraph.empty A⟩
instance (A : Type) : Inhabited (PackedDirectedGraph A) where
  default := empty A
end PackedDirectedGraph

structure DAG (A : Type) (n : Nat) where
  label    : Fin n → A
  kids : (i : Fin n) → List (Fin i)
/-
iは、Natが要求される箇所で自動的にi.val:Natに変換されるので、kidsの戻り値の型の(Fin i)は(Fin i.val)になる。
-/

-- 依存型を隠したやつ
abbrev PackedDAG (A : Type) := Σ n, DAG A n

-- filter 付きDAG
structure DAGWithFilter (A : Type) (n : Nat) where
  base  : DAG A n
  allow : Fin n → Bool   -- 非フィルタは `fun _ => true`
abbrev PackedDAGWithFilter (A : Type) := Σ n, DAGWithFilter  A n

namespace DAG
def empty (A : Type) : DAG A 0 where
  label    i := nomatch i
  kids i := nomatch i

/-- `c : Fin i` を「全体サイズ」`Fin n` に埋め込む（`c.val < i.val < n`） -/
def coeChild {n} (i : Fin n) (c : Fin i) : Fin n :=
  ⟨c.val, Nat.lt_trans c.isLt i.isLt⟩

/-- エッジ一覧 `i → j` を収集 -/
def edges {A n} (g : DAG A n) : List (Fin n × Fin n) :=
   (List.finRange n).flatMap  (fun i =>
    (g.kids i).map (fun c => (i, coeChild i c)))

/-- 子として登場するノードの集合（Natの値で持つ） -/
private def childNats {A n} (g : DAG A n) : List Nat :=
  (g.edges).map (fun e => (e.snd : Fin n).val)

/-- 親を持たないノード（root）だけを返す -/
def roots {A n} (g : DAG A n) : List (Fin n) :=
  let cs := g.childNats
  (List.finRange n).filter (fun i => !(cs.contains i.val))

-- あるnodeの親全部
def parents {A n} (g : DAG A n) (j : Fin n) : List (Fin n) :=
  (List.finRange n).filter (fun i =>
    (g.kids i).any (fun c => DAG.coeChild i c == j))

-- 先祖全部
partial def ancestors {A n} (g : DAG A n) (j : Fin n) : List (Fin n) :=
  let ps := g.parents j
  ps ++ ps.flatMap (fun x => g.ancestors x)
end DAG

namespace PackedDAG
def empty (A : Type) : PackedDAG A :=
  ⟨0, DAG.empty A⟩
instance (A : Type) : Inhabited (PackedDAG A) where
  default := empty A
def WithFilterOf{A} : (d : PackedDAG A) → (A×(Fin d.1) → Bool) → PackedDAGWithFilter A
| ⟨n, G⟩, pred =>
  ⟨n, { base := G, allow := fun i => pred ((G.label i), i)}⟩

private partial def _ToJson {A} [ToString A] [ToJson A] (g:DAG A n) (i:Fin n): Json:=
  let k : String := toString (g.label i)
  let deps : List Json :=
    (g.kids i).map (fun c =>
      let j := DAG.coeChild i c
      _ToJson g j
      )
  let base:= toJson (g.label i)
  mkObj [ (k, base.mergeObj (mkObj [("1deps", Json.arr deps.toArray)]))] -- sort順指定のために 1を入れている

instance [ToString A] [ToJson A]: ToJson (PackedDAG A) where
  toJson
  | ⟨_ , g⟩ =>
    let roots := (DAG.roots g)
    let entries : List Json := roots.map (_ToJson g)
    Json.arr entries.toArray

end PackedDAG

/- 依存を外したビルダー状態：未確定の DAG を配列で保持 -/
private structure UnverifiedDirectedGraph (A : Type) where
  labels : Array A
  kids   : Array (List Nat)   -- 子は「先に作られたノード」のインデックス
deriving Inhabited

namespace UnverifiedDirectedGraph

private def empty {A} : UnverifiedDirectedGraph A :=
  { labels := #[], kids := #[] }

private def size (s : UnverifiedDirectedGraph A) : Nat := s.labels.size

private def okKids (n : Nat) (ks : List Nat) : Bool :=
  ks.all (fun k => decide (k < n))

private def toPackedDAG {A} (s : UnverifiedDirectedGraph A) : PackedDAG A :=
  let n := s.size
  -- kids の長さと n を突き合わせる
  if hk : s.kids.size = n then
    let label : Fin n → A :=
      fun i => s.labels[i]'(by
        -- n = s.size, State.size = s.labels.size
        simp [UnverifiedDirectedGraph.size, n])
    let kids : (i : Fin n) → List (Fin i) :=
      fun i =>
        let raw : List Nat := s.kids[(Fin.cast (by simpa using hk.symm) i)]
        raw.filterMap (fun k =>
          if hki : k < i.val
          then some ⟨k, hki⟩
          else (panic! s!"invalid child index at node {i.val}: {k}")) -- panicは勝手にnoneになるので、実質ここはnone
    ⟨n, { label, kids }⟩
  else
    panic! s!"internal size mismatch: labels={n}, kids={s.kids.size}"

private def toPackedDirectedGraph {A} (s : UnverifiedDirectedGraph A) : PackedDirectedGraph A :=
  let n := s.size
  -- kids の長さと n を突き合わせる
  if hk : s.kids.size = n then
    -- DirectedGraph 構築
    let label : Fin n → A :=
      fun i => s.labels[i]'(by
        simp [UnverifiedDirectedGraph.size, n])
    let kids : (i : Fin n) → List (Fin n) := fun i =>
      let raw : List Nat := s.kids[(Fin.cast (by simpa using hk.symm) i)]
      raw.filterMap (fun k =>
        if hkn : k < n
        then some ⟨k, hkn⟩
        else (panic! s!"invalid child index at node {i.val}: {k}"))
    ⟨n, { label, kids }⟩
  else
    panic! s!"internal size mismatch: labels={n}, kids={s.kids.size}"

end UnverifiedDirectedGraph

abbrev SSA (A : Type) := StateM (UnverifiedDirectedGraph A)

-- ノード追加用の関数
def push {A} (a : A) (ks : List (SSA A Nat) := []) (refs:  List Nat := []) : SSA A Nat := do
  let ksn <- ks.mapM id
  let s ← get
  let n := s.size
  let refs_with_ks := ksn++refs
  set { labels := s.labels.push a, kids := s.kids.push refs_with_ks :UnverifiedDirectedGraph A}
  pure n

def pushU {A} (a : A) (ks : List (SSA A Nat) := []) (refs:  List Nat := []) : SSA A Unit := do
  _ <- push a ks refs

def pushDailyU {A} (a : A) (ks : List (SSA A Nat) := []) (refs:  List Nat := []) (should_append:Bool): SSA A Unit := do
  if should_append
  then pushU a ks refs
  else return ()

def mkPackedDAG {A} (prog : SSA A B) : PackedDAG A :=  (prog.run UnverifiedDirectedGraph.empty).snd |>.toPackedDAG
def mkPackedDirectedGraph {A} (prog : SSA A B) : PackedDirectedGraph A :=  (prog.run UnverifiedDirectedGraph.empty).snd |>.toPackedDirectedGraph

namespace PackedDAGWithFilter

open DAG

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

/-- DAG → State コピー（証明は持たない） -/
private def toState {A} {n} (g : DAG A n) : UnverifiedDirectedGraph A :=
  let labels : Array A := Array.ofFn (fun (i : Fin n) => g.label i)
  let kids   : Array (List Nat) :=
    Array.ofFn (fun (i : Fin n) => (g.kids i).map (fun c => (c : Fin i).val))
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
def compress {A} [Inhabited A] (wf : PackedDAGWithFilter A) : PackedDAG A :=
  match wf with
  | ⟨n, s⟩ =>
    let st0 : UnverifiedDirectedGraph A :=
      let labels := Array.ofFn (fun (i : Fin n) => s.base.label i)
      let kids   := Array.ofFn (fun (i : Fin n) => (s.base.kids i).map (fun c => (c : Fin i).val))
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

    { labels := newLabels, kids := newKids :UnverifiedDirectedGraph A}.toPackedDAG

end PackedDAGWithFilter

namespace TestCompress

open DAG
open DAGWithFilter

def tinyDAG : DAG String 5 where
  label
    | ⟨0, _⟩ => "C"
    | ⟨1, _⟩ => "E"
    | ⟨2, _⟩ => "B"
    | ⟨3, _⟩ => "A"
    | ⟨4, _⟩ => "D"
  kids
    | ⟨0, _⟩ => []
    | ⟨1, _⟩ => []
    | ⟨2, _⟩ => [⟨0, by simp⟩,⟨1, by simp⟩]
    | ⟨3, _⟩ => [⟨2, by simp⟩]
    | ⟨4, _⟩ => [⟨2, by simp⟩]

def mkWF : PackedDAGWithFilter String :=
  let dag:PackedDAG _ := ⟨5, tinyDAG⟩
  let pred:= fun (_, i) => i != 2 && i != 3
  dag.WithFilterOf pred

def run [ToJson A] [ToString A][Inhabited A](wf:PackedDAGWithFilter A) : String :=
  let dag := PackedDAGWithFilter.compress wf
  (toJson dag).pretty

#eval IO.println (run mkWF)

end TestCompress
