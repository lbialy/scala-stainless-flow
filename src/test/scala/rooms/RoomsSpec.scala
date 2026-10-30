package rooms

import java.util.concurrent.{Callable, Executors, TimeUnit}
import scala.jdk.CollectionConverters.*
import org.scalacheck.{Gen, Prop, Properties}
import org.scalacheck.Prop.{forAll, propBoolean}
import Generators.*

/** Booking on SQLite, end to end: the proven code, the calendar, and the table together. */
object RoomsSpec extends Properties("Rooms on SQLite"):

  property("a request overlapping a booking of its room is not booked, one in another room is") = Prop {
    val sql = SqliteBookings.open(":memory:")
    val book = Rooms.bookOn(sql)
    val answers = (book(Booking("Oak", 9, 11)), book(Booking("Oak", 10, 12)), book(Booking("Elm", 10, 12)))
    (answers == (true, false, true)) && sql.held == List(Booking("Oak", 9, 11), Booking("Elm", 10, 12))
  }

  // oneAtATime: requests made at once still run one at a time.
  property("twenty requests at once for the same time: one is booked") = Prop {
    val sql = SqliteBookings.open(":memory:")
    val book = Rooms.bookOn(sql)
    val pool = Executors.newFixedThreadPool(20)
    try
      val calls = List.fill(20)((() => book(Booking("Oak", 9, 11))): Callable[Boolean])
      val booked = pool.invokeAll(calls.asJava).asScala.map(_.get)
      booked.count(identity) == 1 && sql.held == List(Booking("Oak", 9, 11))
    finally pool.shutdown(): Unit
  }

  // What the proofs say, observed: a run of requests stores exactly the ones that overlap nothing stored before.
  property("a run of requests books exactly those that overlap nothing booked") =
    forAll(Gen.listOf(requests)) { run =>
      val sql = SqliteBookings.open(":memory:")
      val book = Rooms.bookOn(sql)
      val expected = run.foldLeft(List.empty[Booking]) { (stored, r) =>
        if stored.forall(Knowledge.noOverlap(_, r)) then stored :+ r else stored
      }
      val answers = run.map(book)
      (sql.held == expected) :| "stored" &&
        (answers.count(identity) == expected.size) :| "answered"
    }
