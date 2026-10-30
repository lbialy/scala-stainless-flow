package rooms

import org.scalacheck.{Gen, Prop, Properties}
import org.scalacheck.Prop.{forAll, propBoolean}
import Generators.*

/** The assumptions behind the proofs, checked against the real thing.
  *
  * tableMatchesModel: on generated runs of adds and reads, SQLite answers each `inRoom` as its contract says of the
  * model (the bookings added so far, oldest first, filtered by room), and holds the model at the end.
  */
object BookingTableSpec extends Properties("BookingTable"):
  private enum Op:
    case Add(booking: Booking)
    case InRoom(room: String)

  private val ops: Gen[List[Op]] =
    Gen.listOf(Gen.frequency(2 -> requests.map(Op.Add(_)), 1 -> roomNames.map(Op.InRoom(_))))

  property("tableMatchesModel") = forAll(ops): run =>
    val db = SqliteBookings.open(":memory:")
    val table = BookingTable.fresh(db)
    val (model, answersMatch) = run.foldLeft((Vector.empty[Booking], true)):
      case ((model, ok), Op.Add(b)) =>
        table.add(b)
        (model :+ b, ok)
      case ((model, ok), Op.InRoom(room)) =>
        val res = table.inRoom(room)
        (model, ok && res.room == room && Vec.modelOf(res.bookings) == toModel(model.filter(_.room == room)))
    (answersMatch :| "every inRoom matches the model") && (db.held == model.toList) :| "the table holds the model"

  property("startsEmpty") = Prop(SqliteBookings.open(":memory:").held.isEmpty)

  property("bookingsEndAfterStart is checked at run time") =
    forAll(roomNames, Gen.choose(0, 10), Gen.choose(0, 10)): (room, start, end) =>
      val made = scala.util.Try(Booking(room, start, end))
      made.isSuccess == (start < end)

  // A row written behind the code's back (what onlyBookingWrites rules out) fails when it is read, not later.
  property("bookingsEndAfterStart is checked on what the table gives back") = Prop:
    val file = java.io.File.createTempFile("rooms", ".db")
    file.deleteOnExit()
    val db = SqliteBookings.open(file.getPath)
    db.add(Booking("Oak", 1, 2))
    val outside = java.sql.DriverManager.getConnection(s"jdbc:sqlite:${file.getPath}")
    try outside.createStatement().executeUpdate("insert into bookings (room, starts, ends) values ('Oak', '5', '5')")
    finally outside.close()
    scala.util.Try(db.held).isFailure && scala.util.Try(db.inRoom("Elm")).isSuccess
