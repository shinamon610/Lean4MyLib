
import Std.Time
open Std.Time

instance :BEq ZonedDateTime where
  beq x y:= x.toTimestamp == y.toTimestamp

instance: Hashable ZonedDateTime where
  hash zdt:= hash zdt.toTimestamp.val.toMilliseconds.toInt

instance : LE ZonedDateTime where
  le x y := x.toTimestamp ≤ y.toTimestamp

instance { x y : ZonedDateTime } : Decidable (x ≤ y) :=
    inferInstanceAs (Decidable (x.toTimestamp ≤ y.toTimestamp))

def JST : TimeZone :=
  TimeZone.mk (TimeZone.Offset.ofHours 9) "UTC" "UTC" false
def now:=(ZonedDateTime.nowAt "Japan")
def is_same_date (a b:ZonedDateTime):Bool:= a.year==b.year && a.month==b.month && a.day== b.day
def same_date (a b:ZonedDateTime):Prop:=is_same_date a b = true
def zdt (year : Year.Offset) (month : Month.Ordinal) (day : Day.Ordinal) := ZonedDateTime.ofPlainDateWithZone (PlainDate.ofYearMonthDayClip year month day) JST

#eval PlainDate.ofYearMonthDayClip 2020 15 33
#eval PlainDate.ofYearMonthDay? 2020 15 33 -- Optionなんだけど、絶対にsomeが帰ってくるから意味ない。
#eval ZonedDateTime.ofPlainDateWithZone (PlainDate.ofYearMonthDayClip 2020 15 33) JST |> fun x => x.toTimestamp.val.toMilliseconds
#eval ZonedDateTime.of (PlainDateTime.mk (.ofYearMonthDayClip 2020 15 33) (.ofHourMinuteSeconds 100 100 10)) "Japan"

#eval (ZonedDateTime.nowAt "Japan") >>= fun x=> (ZonedDateTime.nowAt "Japan") >>= fun y => return decide (x == y)

#eval now >>= fun x=> return is_same_date x (zdt 2025 3 13 )
