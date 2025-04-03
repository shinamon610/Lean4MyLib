namespace Tree

inductive Tree (A:Type) where
| Node:A-> List (Tree A)->Tree A
deriving Inhabited

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

def find {A:Type} (condition:A->Bool) [BEq A][ToString A] (tree:Tree A):Option (Tree A):=
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

def find! {A:Type} (condition:A->Bool) [BEq A][Inhabited A][ToString A] (tree:Tree A):Tree A:=(find condition tree).get!

def add {A:Type}(task:A) (body:StateM (Tree A) Unit):StateM (Tree A) Unit:=do
  let parent<-get
  let res <- (body.run (Tree.Node task []))
  set (Tree.Node (top parent) (res.snd::deps parent))
