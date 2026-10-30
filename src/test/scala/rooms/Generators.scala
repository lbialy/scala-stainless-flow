package rooms

import org.scalacheck.Gen

/** The tests' cases, as in FrFlow's model: rooms, requests, and a room's bookings laid end to end. */
object Generators:
  val roomNames: Gen[String] = Gen.oneOf("Oak", "Elm")

  /** Requests for Oak or Elm that end after they start. */
  val requests: Gen[Booking] = for
    room   <- roomNames
    start  <- Gen.choose(0, 8)
    length <- Gen.choose(1, 3)
  yield Booking(room, start, start + length)

  /** `count` bookings of a room, laid end to end from `from`, each after a gap of 0 or 1. */
  def laidEndToEnd(room: String, from: BigInt, count: Int): Gen[List[Booking]] =
    if count == 0 then Gen.const(Nil)
    else
      for
        gap    <- Gen.choose(0, 1)
        length <- Gen.choose(1, 3)
        first = Booking(room, from + gap, from + gap + length)
        rest <- laidEndToEnd(room, first.end, count - 1)
      yield first :: rest

  /** A room's bookings, laid end to end, some back to back, given in a shuffled order. */
  val roomBookings: Gen[RoomBookings] = for
    room     <- roomNames
    count    <- Gen.choose(0, 4)
    bookings <- laidEndToEnd(room, 0, count)
    shuffled <- Gen.pick(bookings.size, bookings).map(_.toList)
  yield RoomBookings(room, Vec(shuffled*))

  def toModel[A](as: Seq[A]): stainless.collection.List[A] = stainless.collection.List.fromScala(as.toList)
