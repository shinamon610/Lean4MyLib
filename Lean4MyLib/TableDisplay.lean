import Lean

-- 汎用テーブル表示用の型クラス
class TableDisplay (α : Type) where
  getHeaders : List String
  getRow : α → List String

def displayTable [TableDisplay α] (xs:List α) (rowHeader:List String) : String:=
  if xs.isEmpty then "Empty list"
  else
    let headers := if rowHeader.isEmpty then TableDisplay.getHeaders (α := α) else [""] ++ TableDisplay.getHeaders (α := α)
    let allRows := if rowHeader.isEmpty then xs.map TableDisplay.getRow else (xs.zip rowHeader).map (fun (x, header)=> [header]++TableDisplay.getRow x)

    -- 各カラムの最大幅を計算
    let headerWidths := headers.map String.length
    let dataWidths := List.range headers.length |>.map fun i =>
      (allRows.map fun row => row[i]?.map String.length |>.getD 0).max?.getD 0
    let colWidths := List.zipWith max headerWidths dataWidths

    let padRight (s : String) (width : Nat) : String :=
      s ++ String.mk (List.replicate (width - s.length) ' ')

    -- ヘッダー行
    let headerCells := List.zipWith padRight headers colWidths
    let header := "|" ++ String.intercalate "|" headerCells ++ "|"

    -- 区切り線
    let separator := "|" ++ String.intercalate "|" (colWidths.map fun w => String.mk (List.replicate w '-')) ++ "|"

    -- データ行
    let dataRows := allRows.map fun row =>
      let cells := List.zipWith (fun cell width => padRight cell width) row colWidths
      "|" ++ String.intercalate "|" cells ++ "|"
    header ++ "\n" ++ separator ++ (dataRows.foldl (fun acc row => acc ++ "\n" ++ row) "")

-- Reprのinstanceにすることで、#evalしたときにdisplayTableで表示されるようにする
instance [TableDisplay α] : Repr (List α) where
  reprPrec xs _ := displayTable xs []

open Lean Elab Command Meta

elab "derive_table_for " id:ident : command => do
  let structName := id.getId
  let env <- getEnv

  let fieldNames := Lean.getStructureFields env structName
  let headerList := fieldNames.map fun n => Syntax.mkStrLit (toString n)

  -- getHeaders の実装
  let headersExpr ← `(term| [$(headerList),*])

  -- getRow の実装
  let rowExprs ← fieldNames.mapM fun fieldName => do
    let fieldIdent := mkIdent fieldName
    `(term| toString x.$fieldIdent:ident)
  let rowExpr ← `(term| [$(rowExprs),*])

  let instCmd ← `(command|
    instance : TableDisplay $(mkIdent structName) where
      getHeaders := $headersExpr
      getRow x := $rowExpr
  )

  elabCommand instCmd

namespace test
structure P where
  a:Int
  b:String
deriving Repr

structure Country where
  id : Int
  name : String
  isHoge : Bool
deriving Repr
instance : ToString Country where
  toString country := reprStr country

structure Person where
  name : String
  age : Int
  country : Country
deriving Repr

derive_table_for test.P
derive_table_for test.Person

def ps:List P:= [⟨10,"c"⟩,⟨11,"bbb"⟩]
#eval ps

def persons:List Person:=[⟨"a",10,⟨1,"aa",true⟩⟩,⟨"b",120,⟨2,"bb",true⟩⟩]
#eval persons

-- index付きのtable表示がしたいときは、instanceを上書きするとできる
instance : Repr (List P) where
  reprPrec ps _ := displayTable ps (ps.zipIdx.map (fun x => toString x.snd))
#eval ps
