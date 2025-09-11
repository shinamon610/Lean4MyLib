import Std.Time
import Lean
open Lean
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

def zdt (year : Year.Offset) (month : Month.Ordinal) (day : Day.Ordinal)
        (hour : Hour.Ordinal:=0) (minute : Minute.Ordinal:=0) : ZonedDateTime :=
  let pdt := PlainDateTime.mk (PlainDate.ofYearMonthDayClip year month day) (PlainTime.ofHourMinuteSeconds hour minute 0)
  ZonedDateTime.ofPlainDateTimeWithZone pdt JST

def Std.Time.ZonedDateTime.between  (target startDate endDate : ZonedDateTime)  : Bool := startDate <= target && target <= endDate

instance: ToJson ZonedDateTime where
  toJson (time):Json := .mkObj [("date",time.toISO8601String)]
