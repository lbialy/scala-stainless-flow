package rooms

import stainless.lang.*
import stainless.lang.StaticChecks.*
import stainless.annotation.*
import Knowledge.*

object Granted:
  /** Whether a request is granted, given its room's bookings.
    *
    * Tested, not proven: the body is plain Scala that Stainless does not read. Its contract is grantWhenNoOverlap,
    * under the hypotheses bookingsOfTheRoom and roomBookingsApart; Stainless proves those hypotheses where booking
    * calls it, trusts the result, and `CalendarSpec` tests it on generated cases.
    */
  @extern @pure
  def granted(held: RoomBookings, request: Booking): Boolean =
    require(bookingsOfTheRoom(held) && roomBookingsApart(held))
    Calendar(held).grants(request)
  .ensuring(res => grantWhenNoOverlap(held, request, res))

/** The calendar of one room. It grants a request for another room. For its own room, it sorts the bookings by
  * start once; a request is granted when the booking before it ends by the time it starts, and the booking after it
  * starts once it ends. Checking those two neighbours is enough because a room's bookings never overlap.
  */
@ignore
final class Calendar(held: RoomBookings):
  private val startOrder: Ordering[Booking] = Ordering.by(_.start)
  private val byStart = held.bookings.toVector.sorted(using startOrder)

  def grants(request: Booking): Boolean =
    val i = byStart.search(request)(using startOrder).insertionPoint
    val before = byStart.lift(i - 1)
    val after = byStart.lift(i)
    val endsInTime = before.forall(_.end <= request.start)
    val startsAfter = after.forall(_.start >= request.end)
    request.room != held.room || (endsInTime && startsAfter)
