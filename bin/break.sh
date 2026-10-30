#!/usr/bin/env bash
# Makes one of the three changes from FrFlow's README on a scratch copy of this project, and shows what catches it.
#
#   calendar  the calendar forgets the booking after the request          -> ScalaCheck finds a failing case
#   touching  meetings that touch now overlap (claim over times changed)  -> Stainless refutes the step, with a case
#   covers    covers also includes the end, so everything agrees again    -> every proof passes; `flow review` catches it
set -euo pipefail

scenario=${1:?usage: bin/break.sh calendar|touching|covers}
root=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
rsync -a --exclude target --exclude project/target --exclude project/project --exclude .bsp "$root/" "$work/"
cd "$work"

calendar=src/main/scala/rooms/Calendar.scala
knowledge=src/main/scala/rooms/Knowledge.scala

touching() {
  perl -pi -e 's/a\.end <= b\.start \|\| b\.end <= a\.start/a.end < b.start || b.end < a.start/' "$knowledge"
  perl -pi -e 's/_\.end <= request\.start/_.end < request.start/; s/_\.start >= request\.end/_.start > request.end/' "$calendar"
}

case $scenario in
  calendar)
    perl -pi -e 's/request\.room != held\.room \|\| \(endsInTime && startsAfter\)/request.room != held.room || endsInTime/' "$calendar"
    git diff --no-index "$root/$calendar" "$calendar" || true
    sbt -batch test ;;
  touching)
    touching
    git diff --no-index "$root/$knowledge" "$knowledge" || true
    sbt -batch verify "flow status" ;;
  covers)
    touching
    perl -pi -e 's/b\.start <= t && t < b\.end/b.start <= t && t <= b.end/' "$knowledge"
    git diff --no-index "$root/$knowledge" "$knowledge" || true
    sbt -batch verify "flow review" ;;
  *) echo "unknown scenario: $scenario" >&2; exit 2 ;;
esac
