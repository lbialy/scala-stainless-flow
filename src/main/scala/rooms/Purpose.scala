package rooms

import stainless.lang.{ghost as ghostExpr, *}
import stainless.lang.StaticChecks.*
import stainless.annotation.*
import stainless.collection.*
import Knowledge.*

/** The roots, of the code that runs.
  *
  * The world is what the table holds. The roots look at the Declarations only at the request and the world as it
  * stands, and each run of booking fixes them there: `booked` is what the table holds, `bookedAfter` is what it holds
  * once booking returns, and `accepted` is what booking answers. Those definitions are bookedIsStored,
  * bookedAfterIsStored and acceptedIsAnswered, and `book` proves both roots of them through the refinement steps in
  * `Knowledge`: the roots are theorems about every run of booking, from every world in which neverOverlap holds.
  */
object Purpose:
  /** The world as it stands: what the table holds. */
  @ghost
  def asItStands: List[Booking] => List[Booking] = world => world

  /** What a run of booking leaves in the table. */
  @ghost
  def leaves(stored: List[Booking]): (Booking, List[Booking]) => List[Booking] = (_, _) => stored

  /** What a run of booking answers. */
  @ghost
  def answers(answer: Boolean): (Booking, List[Booking]) => Boolean = (_, _) => answer

  /** Booking a request, with both roots proven of the run. This is what `Rooms.bookOn` runs. */
  def book(table: BookingTable, request: Booking): Boolean =
    require(neverOverlap(table.stored))
    @ghost val now = table.stored
    val answer = Book.bookIfGranted(table, request)
    ghostExpr:
      bookWhenFreeStep(asItStands, leaves(table.stored), asItStands, leaves(table.stored), request, now)
      acceptWhenFreeStep(asItStands, answers(answer), asItStands, answers(answer), request, now)
    answer
  .ensuring(answer =>
    bookWhenFree(asItStands, leaves(table.stored), request, old(table).stored) &&
    acceptWhenFree(asItStands, answers(answer), request, old(table).stored) &&
    neverOverlap(table.stored))
