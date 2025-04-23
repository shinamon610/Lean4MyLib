import Lean4MyLib.MyState

open MyState
namespace DAG

inductive DAG (A:Type) where
| Node:A-> List (DAG A)->DAG A
deriving Inhabited

def DAG.size (dag:DAG A) : Nat :=
  match dag with
  | .Node _ children =>
    1 + (children.map DAG.size).foldl Nat.max 0

def str [ToString A]: (DAG A)->String
  | .Node a list=>
    let repr_a:=toString a
    let repr_list:=list.map str
    s! "{repr_a} \n {repr_list}"

instance[ToString A]: ToString (DAG A) where
  toString :=str

def top {A:Type}(tree:DAG A):A:=
  match tree with
  | .Node a _ => a

def deps {A:Type}(tree:DAG A):List (DAG A):=
  match tree with
  | .Node _ list => list

def find {A:Type} (condition:A->Bool) (tree:DAG A):Option (DAG A):=
  inner_find [tree]
  where
    inner_find (trees:List (DAG A)):Option (DAG A):=
    match trees with
    | []=>none
    | head::tails=>
      match head with
      | .Node task list =>
        if condition task
        then some head
        else
          let res:=inner_find list
          match res with
          | none=>inner_find tails
          | _=>res

def find! {A:Type} (condition:A->Bool) [Inhabited A] (tree:DAG A):DAG A:=(find condition tree).get!

def add {A:Type}(task:A) (body:StateM (DAG A) Unit):StateM (DAG A) Unit:=do
  let parent<-get
  let res <- (body.run (DAG.Node task []))
  set (DAG.Node (top parent) (res.snd::deps parent))

def toposort_rev {A:Type} (tree:DAG A):List A:=
  match tree with
  | .Node a children => a::(children.foldl (fun x y => (toposort_rev y)++x) [])

def toposort {A:Type} (tree:DAG A):List A:= (toposort_rev (tree)).reverse

def dfsWithNum (dag:DAG A) (n:Nat): List (A×Nat):=
  match dag with
  | .Node a list =>
    let res := List.flatMap (fun x=>dfsWithNum x (n+1)) list
    (a, n)::res

-- def has_root (target:StateT (DAG A) M B):Prop := (deps (exec target root)).length == 1
-- (h: has_root parent )を引数に追加して証明したいが、append呼び出し側で使うのが難しいからやめた
def append [Monad M][Inhabited A] (parent:StateT (DAG A) M Unit) (children:StateT (DAG A) M Unit) :StateT (DAG A) M Unit := do
  -- have hh: (deps (exec parent root)) ≠ [] := by
  --   unfold has_root at h
  --   intro h_nil
  --   rw [h_nil] at h
  --   contradiction

  -- match (deps (exec parent root)).head hh with
  let pdag:DAG A <- execD parent
  let cdag:DAG A <- execD children
  match (deps pdag).head! with
    | .Node p list => set $  DAG.Node p $ (deps cdag) ++ list

def indent (n : Nat) (s : String) : String :=
  let list := List.replicate n " "
  (list.foldl (fun acc x=> x ++ acc) "⊢ ")++s

def renderDAG [ToString A](dag:DAG A):IO Unit:=do
  let res:=dfsWithNum dag 0
  res.forM (fun (x, n) => println! indent n (toString x))
