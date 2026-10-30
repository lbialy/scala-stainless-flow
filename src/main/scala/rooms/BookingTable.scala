package rooms

import stainless.lang.*
import stainless.lang.StaticChecks.*
import stainless.annotation.*
import stainless.collection.*

/** Where the bookings are kept, as proven code sees it: the SQLite table, an opaque value to Stainless, and
  * `stored`, a ghost model of what it holds: every booking, oldest first.
  *
  * tableMatchesModel (assumption): the table gives a room's bookings in the order they were added, and adds one at
  * the end. These are the contracts of `inRoom` and `add`. Stainless trusts them; `BookingTableSpec` checks them
  * against SQLite on generated runs.
  *
  * onlyBookingWrites (assumption): only booking writes to the table. In code, `add` is visible only inside `rooms`
  * and `Book.bookIfGranted` is its only caller; anything writing to the database file from outside is trusted not to.
  *
  * `stored` is never read or written at run time: it exists for the proofs only.
  */
final class BookingTable private (@extern val db: SqliteBookings, @ghost var stored: List[Booking]):

  @extern @pure
  def inRoom(room: String): RoomBookings = {
    db.inRoom(room)
  }.ensuring(res => res.room == room && res.bookings.model == stored.filter(b => b.room == room))

  @extern
  private[rooms] def add(booking: Booking): Unit = {
    db.add(booking)
  }.ensuring(_ => stored == old(this).stored :+ booking)

object BookingTable:
  /** startsEmpty (assumption): the table starts empty. */
  @extern
  def fresh(db: SqliteBookings): BookingTable = {
    BookingTable(db, Nil())
  }.ensuring(_.stored == Nil[Booking]())
