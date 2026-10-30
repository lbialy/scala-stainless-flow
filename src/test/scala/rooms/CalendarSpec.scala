package rooms

import org.scalacheck.{Prop, Properties, Test}
import org.scalacheck.Prop.forAll
import Generators.*

/** grantWhenNoOverlap: the claim on the calendar, which Stainless trusts, tested on 1,000 generated cases. */
object CalendarSpec extends Properties("Calendar"):
  override def overrideParameters(p: Test.Parameters) = p.withMinSuccessfulTests(1000)

  // The contract's hypotheses (bookingsOfTheRoom, roomBookingsApart) speak of `apart`, which quantifies over every
  // moment and cannot run. Under bookingsEndAfterStart it equals noOverlap (proven: Knowledge.apartIffNoOverlap), so
  // this checks that the generator only makes cases the contract is about.
  private def withinHypotheses(held: RoomBookings): Boolean =
    val bs = held.bookings.toVector
    bs.forall(_.room == held.room) &&
      bs.indices.forall(i => bs.indices.forall(j => i == j || Knowledge.noOverlap(bs(i), bs(j))))

  property("generated cases meet the contract's hypotheses") = forAll(roomBookings)(withinHypotheses)

  property("grantWhenNoOverlap") = forAll(roomBookings, requests): (held, request) =>
    Granted.granted(held, request) == Vec.modelOf(held.bookings).forall(b => Knowledge.noOverlap(b, request))

  // The examples, as in FrFlow's GrantedExamples.
  property("back to back: granted") =
    Prop(Granted.granted(RoomBookings("Oak", Vec(Booking("Oak", 9, 10))), Booking("Oak", 10, 11)))

  property("overlapping: refused") =
    Prop(!Granted.granted(RoomBookings("Oak", Vec(Booking("Oak", 9, 11))), Booking("Oak", 10, 12)))
