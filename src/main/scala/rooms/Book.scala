package rooms

import stainless.lang.{ghost as ghostExpr, *}
import stainless.lang.StaticChecks.*
import stainless.annotation.*
import Knowledge.*

object Book:
  /** Booking a request: whether it was booked. Reads the room's bookings from the table, asks the calendar, and
    * adds the booking if it is granted.
    *
    * Proven: storeWhenFree, answerWhenFree, and that neverOverlap is kept. Assumed: tableMatchesModel (the table's
    * contracts), bookingsEndAfterStart (the invariant of Booking), and oneAtATime (callers go through `bookOn`).
    */
  def bookIfGranted(table: BookingTable, request: Booking): Boolean =
    require(neverOverlap(table.stored))
    val held = table.inRoom(request.room)
    ghostExpr:
      ofTheRoom(table.stored, request.room)
      apartOfTheRoom(table.stored, request.room)
    val booked = Granted.granted(held, request)
    ghostExpr:
      grantWhenFreeStep(held, request, booked)
      freeOfTheRoom(table.stored, request)
      if booked then neverOverlapKept(table.stored, request)
    if booked then table.add(request)
    booked
  .ensuring(res =>
    answerWhenFree(old(table).stored, request, res) &&
    storeWhenFree(old(table).stored, table.stored, request) &&
    neverOverlap(table.stored))

/** Booking on SQLite: the proven code, run one request at a time (oneAtATime). Glue that Stainless does not read. */
@ignore
object Rooms:
  def bookOn(sql: SqliteBookings): Booking => Boolean =
    val table = BookingTable.fresh(sql)
    request => sql.atomically(Book.bookIfGranted(table, request))
