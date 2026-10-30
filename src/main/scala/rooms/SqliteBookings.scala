package rooms

import stainless.annotation.ignore
import java.sql.{Connection, DriverManager, PreparedStatement}

/** The bookings in SQLite, a row each, read back in the order they were added. Plain Scala that Stainless does not
  * read: proven code sees it only through `BookingTable`, whose contracts `BookingTableSpec` checks against it.
  */
@ignore
final class SqliteBookings private (conn: Connection):
  conn.createStatement().executeUpdate("create table if not exists bookings " +
    "(id integer primary key, room text not null, starts text not null, ends text not null)")

  def inRoom(room: String): RoomBookings = RoomBookings(room, Vec(bookingsIn(room)))

  def add(booking: Booking): Unit = insert(booking)

  /** Runs `body` with no other booking in between: what `oneAtATime` assumes. */
  def atomically[A](body: => A): A = synchronized(body)

  def held: List[Booking] = synchronized {
    read(conn.prepareStatement("select room, starts, ends from bookings order by id"))
  }

  private def bookingsIn(room: String): Vector[Booking] = synchronized {
    val query = conn.prepareStatement("select room, starts, ends from bookings where room = ? order by id")
    query.setString(1, room)
    read(query).toVector
  }

  private def insert(b: Booking): Unit = synchronized {
    val row = conn.prepareStatement("insert into bookings (room, starts, ends) values (?, ?, ?)")
    List(b.room, b.start.toString, b.end.toString).zipWithIndex.foreach((v, i) => row.setString(i + 1, v))
    row.executeUpdate()
  }

  private def read(query: PreparedStatement): List[Booking] =
    val rows = query.executeQuery()
    Iterator.continually(rows).takeWhile(_.next())
      .map(r => Booking(r.getString(1), BigInt(r.getString(2)), BigInt(r.getString(3)))).toList

@ignore
object SqliteBookings:
  /** A database in a file, or `:memory:`. */
  def open(path: String): SqliteBookings = SqliteBookings(DriverManager.getConnection(s"jdbc:sqlite:$path"))

  /** An in-memory database holding the given bookings, in order: for tests. */
  def holding(bookings: List[Booking]): SqliteBookings =
    val db = open(":memory:")
    bookings.foreach(db.insert)
    db
