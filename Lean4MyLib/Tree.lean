import Lean4MyLib.MyState

open MyState
namespace Tree

-- mathlibにTreeってあるけど、そっちは二分木
-- これは普通の木
inductive Tree (A:Type) where
| Node:A-> List (Tree A)->Tree A
deriving Inhabited

def Tree.size (tree:Tree A) : Nat :=
  match tree with
  | .Node _ children =>
    1 + (children.map Tree.size).foldl Nat.max 0

def str [ToString A]: (Tree A)->String
  | .Node a list=>
    let repr_a:=toString a
    let repr_list:=list.map str
    s! "{repr_a} \n {repr_list}"

instance[ToString A]: ToString (Tree A) where
  toString :=str

def top {A:Type}(tree:Tree A):A:=
  match tree with
  | .Node a _ => a

def deps {A:Type}(tree:Tree A):List (Tree A):=
  match tree with
  | .Node _ list => list

def find {A:Type} (condition:A->Bool) (tree:Tree A):Option (Tree A):=
  inner_find [tree]
  where
    inner_find (trees:List (Tree A)):Option (Tree A):=
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

def find! {A:Type} (condition:A->Bool) [Inhabited A] (tree:Tree A):Tree A:=(find condition tree).get!

def add {A:Type}(task:A) (body:StateM (Tree A) Unit):StateM (Tree A) Unit:=do
  let parent<-get
  let res <- (body.run (Tree.Node task []))
  set (Tree.Node (top parent) (res.snd::deps parent))

def toposort_rev {A:Type} (tree:Tree A):List A:=
  match tree with
  | .Node a children => a::(children.foldl (fun x y => (toposort_rev y)++x) [])

def toposort {A:Type} (tree:Tree A):List A:= (toposort_rev (tree)).reverse

def dfsWithNum (tree:Tree A) (n:Nat): List (A×Nat):=
  match tree with
  | .Node a list =>
    let res := List.flatMap (fun x=>dfsWithNum x (n+1)) list
    (a, n)::res

-- def has_root (target:StateT (Tree A) M B):Prop := (deps (exec target root)).length == 1
-- (h: has_root parent )を引数に追加して証明したいが、append呼び出し側で使うのが難しいからやめた
def append [Monad M][Inhabited A] (parent:StateT (Tree A) M Unit) (children:StateT (Tree A) M Unit) :StateT (Tree A) M Unit := do
  -- have hh: (deps (exec parent root)) ≠ [] := by
  --   unfold has_root at h
  --   intro h_nil
  --   rw [h_nil] at h
  --   contradiction

  -- match (deps (exec parent root)).head hh with
  let ptree:Tree A <- execD parent
  let ctree:Tree A <- execD children
  match (deps ptree).head! with
    | .Node p list => set $  Tree.Node p $ (deps ctree) ++ list

def indent (n : Nat) (s : String) : String :=
  let list := List.replicate n " "
  (list.foldl (fun acc x=> x ++ acc) "⊢ ")++s

def renderTree [ToString A](tree:Tree A):IO Unit:=do
  let res:=dfsWithNum tree 0
  res.forM (fun (x, n) => println! indent n (toString x))
