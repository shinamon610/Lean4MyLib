import Lean4MyLib.DAG
import Lean4MyLib.lean_shell
import Std

open Std
open DAG

namespace FileTracer
/-
資料作成に使用した参照資料の場所を保持したい。

資料の場所が散逸しているときに、どこに最新が存在するのかを明らかにしたい。
-/

abbrev URL:=String

inductive Src
| localpath: System.FilePath->Src
| Box: System.FilePath->URL->Src
deriving Repr,Inhabited,BEq,Hashable

structure FileS where
  name:String
  hash:String
  date:String --人間が見るから文字でいい
  src:Src
  howToMake:String
deriving Repr,Inhabited,BEq,Hashable

abbrev FileTree:=DAG FileS
abbrev SFT:=StateM FileTree Unit

-- これで確認して手動更新とする。
-- #eval FileS.mk "sample" "12983b4fa3f6e96bfd80593bcbc9f216ad6af72ec1564cfde03d0d0e8abdc83d" "2025-03-24 02:10:39.331433608 +0900" (Src.localpath "") ""
-- #shell "stat" "-c" "%y" "ShinamonTaskManager2/FileTracer.lean"
-- #shell "sha256sum" "ShinamonTaskManager2/FileTracer.lean"
