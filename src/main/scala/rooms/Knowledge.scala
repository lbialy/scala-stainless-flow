package rooms

import stainless.lang.*
import stainless.lang.StaticChecks.*
import stainless.annotation.*
import stainless.collection.*

/** The statements of the Rooms model (FrFlow's `examples/rooms/.../Knowledge.scala`), as Stainless sees them.
  *
  * Each FrFlow claim is a named predicate. Each refinement step is a lemma: the statements that refine a claim are
  * its preconditions, and the claim is its postcondition. Stainless proves every lemma here, so a claim can never
  * contradict the claims it is refined into.
  *
  * Everything here is ghost or plain logic: none of it runs when the code runs.
  */
object Knowledge:

  // ── Over moments ──────────────────────────────────────────────────────────────────────────────────────────────

  def covers(b: Booking, t: BigInt): Boolean = b.start <= t && t < b.end

  @ghost
  def apart(a: Booking, b: Booking): Boolean =
    a.room != b.room || forall((t: BigInt) => !(covers(a, t) && covers(b, t)))

  @ghost
  def free(bookings: List[Booking], request: Booking): Boolean = bookings.forall(b => apart(b, request))

  @ghost
  def pairwiseApart(bookings: List[Booking]): Boolean = bookings match
    case Nil()      => true
    case Cons(h, t) => t.forall(b => apart(h, b)) && pairwiseApart(t)

  // ── Over start and end times ──────────────────────────────────────────────────────────────────────────────────

  def noOverlap(a: Booking, b: Booking): Boolean = a.room != b.room || a.end <= b.start || b.end <= a.start

  def when[A](cond: Boolean)(thenValue: A)(otherwise: A): A = if cond then thenValue else otherwise

  // ── The roots: the purpose, over Declarations ─────────────────────────────────────────────────────────────────
  //
  // `booked`, `bookedAfter` and `accepted` are FrFlow's Declarations: concepts known only by what the statements
  // say of them. Here they are parameters, so a lemma about them holds for every possible meaning they could have,
  // as long as its preconditions do. `W` is the world, kept abstract in the same way.

  /** bookWhenFree: A request is booked exactly when its room is free for its whole time. */
  @ghost
  def bookWhenFree[W](booked: W => List[Booking], bookedAfter: (Booking, W) => List[Booking],
                      request: Booking, now: W): Boolean =
    val bookings = booked(now)
    bookedAfter(request, now) == when(free(bookings, request))(bookings :+ request)(bookings)

  /** acceptWhenFree: A request is accepted exactly when its room is free for its whole time. */
  @ghost
  def acceptWhenFree[W](booked: W => List[Booking], accepted: (Booking, W) => Boolean,
                        request: Booking, now: W): Boolean =
    accepted(request, now) == free(booked(now), request)

  // ── What each Declaration is in the code: the table, and booking's run ────────────────────────────────────────

  /** bookedIsStored: What is booked is what the table holds. */
  @ghost
  def bookedIsStored[W](booked: W => List[Booking], storedIn: W => List[Booking], now: W): Boolean =
    booked(now) == storedIn(now)

  /** bookedAfterIsStored: What is booked once a request is handled is what the table holds after booking it. */
  @ghost
  def bookedAfterIsStored[W](bookedAfter: (Booking, W) => List[Booking], storedIn: W => List[Booking],
                             after: (Booking, W) => W, request: Booking, now: W): Boolean =
    bookedAfter(request, now) == storedIn(after(request, now))

  /** acceptedIsAnswered: A request is accepted exactly when booking it answers booked. */
  @ghost
  def acceptedIsAnswered[W](accepted: (Booking, W) => Boolean, answer: (Booking, W) => Boolean,
                            request: Booking, now: W): Boolean =
    accepted(request, now) == answer(request, now)

  // ── What booking stores and answers, and what the table always holds: postconditions of `Book.bookIfGranted` ──

  /** storeWhenFree: A request is stored exactly when its room is free for its whole time. */
  @ghost
  def storeWhenFree(stored: List[Booking], storedAfter: List[Booking], request: Booking): Boolean =
    storedAfter == when(free(stored, request))(stored :+ request)(stored)

  /** answerWhenFree: A request is answered booked exactly when its room is free for its whole time. */
  @ghost
  def answerWhenFree(stored: List[Booking], request: Booking, answer: Boolean): Boolean =
    answer == free(stored, request)

  /** neverOverlap: The bookings stored never overlap. */
  @ghost
  def neverOverlap(stored: List[Booking]): Boolean = pairwiseApart(stored)

  // ── What the calendar is given, and what it answers ───────────────────────────────────────────────────────────

  /** bookingsOfTheRoom: A room's bookings are all of that room. */
  @ghost
  def bookingsOfTheRoom(held: RoomBookings): Boolean = held.bookings.model.forall(b => b.room == held.room)

  /** roomBookingsApart: A room's bookings never overlap. */
  @ghost
  def roomBookingsApart(held: RoomBookings): Boolean = pairwiseApart(held.bookings.model)

  /** grantWhenFree: A request is granted exactly when its room is free for its whole time. */
  @ghost
  def grantWhenFree(held: RoomBookings, request: Booking, granted: Boolean): Boolean =
    granted == free(held.bookings.model, request)

  /** grantWhenNoOverlap: A request is granted exactly when it overlaps no booking of its room. */
  @ghost
  def grantWhenNoOverlap(held: RoomBookings, request: Booking, granted: Boolean): Boolean =
    granted == held.bookings.model.forall(b => noOverlap(b, request))

  // ══ Refinement steps ══════════════════════════════════════════════════════════════════════════════════════════

  /** bookWhenFree, from bookedIsStored, bookedAfterIsStored and storeWhenFree. */
  @ghost
  def bookWhenFreeStep[W](booked: W => List[Booking], bookedAfter: (Booking, W) => List[Booking],
                          storedIn: W => List[Booking], after: (Booking, W) => W,
                          request: Booking, now: W): Unit =
    require(
      bookedIsStored(booked, storedIn, now) &&
      bookedAfterIsStored(bookedAfter, storedIn, after, request, now) &&
      storeWhenFree(storedIn(now), storedIn(after(request, now)), request))
  .ensuring(_ => bookWhenFree(booked, bookedAfter, request, now))

  /** acceptWhenFree, from bookedIsStored, acceptedIsAnswered and answerWhenFree. */
  @ghost
  def acceptWhenFreeStep[W](booked: W => List[Booking], accepted: (Booking, W) => Boolean,
                            storedIn: W => List[Booking], answer: (Booking, W) => Boolean,
                            request: Booking, now: W): Unit =
    require(
      bookedIsStored(booked, storedIn, now) &&
      acceptedIsAnswered(accepted, answer, request, now) &&
      answerWhenFree(storedIn(now), request, answer(request, now)))
  .ensuring(_ => acceptWhenFree(booked, accepted, request, now))

  /** Two bookings, each ending after it starts, are apart exactly when they do not overlap: if they share a room
    * and neither ends before the other starts, the later of the two starts is a moment both cover.
    */
  @ghost
  def apartIffNoOverlap(a: Booking, b: Booking): Unit =
    if a.room == b.room && !noOverlap(a, b) then
      val t = if a.start >= b.start then a.start else b.start
      assert(covers(a, t) && covers(b, t))
  .ensuring(_ => apart(a, b) == noOverlap(a, b))

  @ghost
  def noOverlapIsFree(bookings: List[Booking], request: Booking): Unit =
    decreases(bookings)
    bookings match
      case Nil() => ()
      case Cons(h, t) =>
        apartIffNoOverlap(h, request)
        noOverlapIsFree(t, request)
  .ensuring(_ => bookings.forall(b => noOverlap(b, request)) == free(bookings, request))

  /** grantWhenFree, from grantWhenNoOverlap (and bookingsEndAfterStart, the invariant of Booking). */
  @ghost
  def grantWhenFreeStep(held: RoomBookings, request: Booking, granted: Boolean): Unit =
    require(grantWhenNoOverlap(held, request, granted))
    noOverlapIsFree(held.bookings.model, request)
  .ensuring(_ => grantWhenFree(held, request, granted))

  // ── Lemmas booking's proof uses ───────────────────────────────────────────────────────────────────────────────

  /** bookingsOfTheRoom, of what the table gives: the stored bookings of one room are all of that room. */
  @ghost
  def ofTheRoom(stored: List[Booking], room: String): Unit =
    decreases(stored)
    stored match
      case Nil()      => ()
      case Cons(_, t) => ofTheRoom(t, room)
  .ensuring(_ => stored.filter(b => b.room == room).forall(b => b.room == room))

  @ghost
  def apartFromFiltered(h: Booking, t: List[Booking], room: String): Unit =
    require(t.forall(b => apart(h, b)))
    decreases(t)
    t match
      case Nil()        => ()
      case Cons(_, t2)  => apartFromFiltered(h, t2, room)
  .ensuring(_ => t.filter(b => b.room == room).forall(b => apart(h, b)))

  /** roomBookingsApart, of what the table gives: one room's bookings never overlap when no stored ones do. */
  @ghost
  def apartOfTheRoom(stored: List[Booking], room: String): Unit =
    require(pairwiseApart(stored))
    decreases(stored)
    stored match
      case Nil() => ()
      case Cons(h, t) =>
        apartFromFiltered(h, t, room)
        apartOfTheRoom(t, room)
  .ensuring(_ => pairwiseApart(stored.filter(b => b.room == room)))

  /** A request is free among its room's bookings exactly when it is free among all of them: a booking of another
    * room is apart from it.
    */
  @ghost
  def freeOfTheRoom(stored: List[Booking], request: Booking): Unit =
    decreases(stored)
    stored match
      case Nil()      => ()
      case Cons(_, t) => freeOfTheRoom(t, request)
  .ensuring(_ => free(stored.filter(b => b.room == request.room), request) == free(stored, request))

  @ghost
  def apartFromAppended(h: Booking, t: List[Booking], request: Booking): Unit =
    require(t.forall(b => apart(h, b)) && apart(h, request))
    decreases(t)
    t match
      case Nil()       => ()
      case Cons(_, t2) => apartFromAppended(h, t2, request)
  .ensuring(_ => (t :+ request).forall(b => apart(h, b)))

  /** neverOverlap is kept by storing a request that is free. */
  @ghost
  def neverOverlapKept(stored: List[Booking], request: Booking): Unit =
    require(pairwiseApart(stored) && free(stored, request))
    decreases(stored)
    stored match
      case Nil() => ()
      case Cons(h, t) =>
        apartFromAppended(h, t, request)
        neverOverlapKept(t, request)
  .ensuring(_ => pairwiseApart(stored :+ request))

  /** neverOverlap holds of the table as it starts (startsEmpty). */
  @ghost
  def neverOverlapAtStart(): Unit =
    ()
  .ensuring(_ => neverOverlap(Nil[Booking]()))
