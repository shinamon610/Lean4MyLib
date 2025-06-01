structure P where
  a:Int
  b:String
deriving Repr

-- 汎用テーブル表示用の型クラス
class TableDisplay (α : Type) where
  getHeaders : List String
  getRow : α → List String

-- List用のToStringインスタンス（TableDisplayを使用）
instance [TableDisplay α] : ToString (List α) where
  toString xs :=
    if xs.isEmpty then "Empty list"
    else
      let headers := TableDisplay.getHeaders (α := α)
      let allRows := xs.map TableDisplay.getRow

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

instance [TableDisplay α] : Repr (List α) where
  reprPrec xs _ := toString xs

instance : TableDisplay P where
  getHeaders := ["a", "b"]
  getRow p := [toString p.a, toString p.b]

instance : TableDisplay Person where
  getHeaders := ["name", "age","country"]
  getRow p := [toString p.name, toString p.age, (repr p.country).pretty]

def ps:List P:= [⟨10,"c"⟩,⟨11,"bbb"⟩]
#eval ps

def persons:List Person:=[⟨"a",10,⟨1,"aa",true⟩⟩,⟨"b",120,⟨2,"bb",true⟩⟩]
#eval persons
