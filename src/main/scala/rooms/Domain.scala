package rooms

import stainless.lang.*
import stainless.annotation.*
import flow.assumption

/** What the booking form sends and the table stores.
  *
  * `bookingsEndAfterStart` (assumption): every booking ends after it starts. It is the class invariant, so Stainless
  * assumes it of every Booking and proves it wherever proven code makes one; it uses Predef's `require`, so it is
  * also checked at run time on every Booking made, the ones from the form and from the table among them.
  */
@assumption("bookingsEndAfterStart", "Every booking ends after it starts.")
final case class Booking(room: String, start: BigInt, end: BigInt):
  require(start < end)

/** A room's bookings, as the table gives them. */
final case class RoomBookings(room: String, bookings: Vec[Booking])
