# Stainless Flow

Stainless Flow is a way to build Scala 3 software together with a formal model of it, proven by
[Stainless](https://github.com/epfl-lara/stainless). It's not a library. It's a way of using one that already exists.

> This repository is a friendly reply to Szymon Rodziewicz's [FrFlow](https://github.com/szymon-rd/fr-flow). It ports
> FrFlow's `rooms` example, statement for statement, to plain Stainless: no DSL, no translation to Lean, and the
> proven code is the code that runs. The motivation below is FrFlow's, and it's a good one.

## The opportunity and the problem with agentic coding

Agentic coding lets developers explore the solution space much faster and ship at much higher velocity. Following
Nada Amin's *Future of Programming* (Scala Days 2026), FrFlow names two risks that come with it:

1. **Lost theory.** Peter Naur argued that a program is the visible part of a theory its programmers hold. When agents
   write the code, nobody on the team builds that theory, and the agent loses it when its context ends.
2. **Increasing entropy.** A codebase that grows without anyone tracking its content and architecture loses its
   integrity, and eventually its correctness.

## Proposed solution

Build a formal, proven model of the software as a refinement tree (Wirth, 1971; Back, 1978; Morgan, 1990):

1. Development starts from a specification: a few core, formal statements about the program.
2. Each statement is refined into more concrete statements that together imply it. Every refinement step is a lemma,
   and Stainless proves it, so a statement can never contradict the ones it is refined into.
3. The last refinement is the code itself, written in one of two ways:
   - As **proven code**: ordinary Scala in the subset Stainless verifies, with the statements as its pre- and
     postconditions. The same source is compiled and run; ghost code and contracts are erased from the bytecode.
   - As **tested code**: any Scala, behind an `@extern` function whose contract is the statement. Stainless trusts
     the contract; ScalaCheck tests it on generated cases.

Where FrFlow writes statements in a `Term` DSL and renders them to Lean 4, here a statement is a Scala function
returning `Boolean`, and a proof is a Scala function Stainless checks. There's no second language and no
translation layer to trust.

## Example: booking meeting rooms

People book meeting rooms for a stretch of time, and a room holds one meeting at a time. This is FrFlow's
[`examples/rooms`](https://github.com/szymon-rd/fr-flow/tree/main/examples/rooms) with the same 17 statements. The
whole of it is in [`src/main/scala/rooms`](src/main/scala/rooms).

### The code

The domain, and when a room is free: a booking covers the moments from its start up to its end; two bookings are
apart when they are in different rooms or share no moment.

```scala
/** What the booking form sends and the table stores. */
final case class Booking(room: String, start: BigInt, end: BigInt):
  require(start < end)   // bookingsEndAfterStart

/** A room's bookings, as the table gives them. */
final case class RoomBookings(room: String, bookings: Vec[Booking])

def covers(b: Booking, t: BigInt): Boolean = b.start <= t && t < b.end

@ghost def apart(a: Booking, b: Booking): Boolean =
  a.room != b.room || forall((t: BigInt) => !(covers(a, t) && covers(b, t)))

@ghost def free(bookings: List[Booking], request: Booking): Boolean = bookings.forall(b => apart(b, request))
```

Bookings come from the booking form, which sends only bookings that end after they start. That is trusted, so it's
an assumption: here it's the invariant of `Booking`. Stainless assumes it of every `Booking`, and since it uses
`Predef.require`, it's also checked at run time on every `Booking` made, including every row read back from the
database.

The roots state the purpose over Declarations: concepts known only by what the statements say of them. In Stainless
a Declaration is just a parameter, so a root holds for any meaning of it that satisfies the statements below.

```scala
/** bookWhenFree: A request is booked exactly when its room is free for its whole time. */
@ghost def bookWhenFree[W](booked: W => List[Booking], bookedAfter: (Booking, W) => List[Booking],
                           request: Booking, now: W): Boolean =
  val bookings = booked(now)
  bookedAfter(request, now) == when(free(bookings, request))(bookings :+ request)(bookings)

/** acceptWhenFree: A request is accepted exactly when its room is free for its whole time. */
@ghost def acceptWhenFree[W](booked: W => List[Booking], accepted: (Booking, W) => Boolean,
                             request: Booking, now: W): Boolean =
  accepted(request, now) == free(booked(now), request)
```

Booking a request reads the room's bookings from the table, asks the calendar, and adds the booking if it is
granted. Its claims are its postconditions, and Stainless proves them of the code.

```scala
def bookIfGranted(table: BookingTable, request: Booking): Boolean =
  require(neverOverlap(table.stored))
  val held = table.inRoom(request.room)
  ghostExpr:
    ofTheRoom(table.stored, request.room)        // bookingsOfTheRoom
    apartOfTheRoom(table.stored, request.room)   // roomBookingsApart
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
```

After compilation, that is four calls: `room`, `inRoom`, `granted`, `add`. Contracts, ghost blocks and lemma
calls are erased.

A refinement step is a lemma: the statements that refine a claim are its preconditions, and the claim is its
postcondition. This is the whole of FrFlow's `BookWhenFree.lean`:

```scala
/** bookWhenFree, from bookedIsStored, bookedAfterIsStored and storeWhenFree. */
@ghost def bookWhenFreeStep[W](booked: W => List[Booking], bookedAfter: (Booking, W) => List[Booking],
                               storedIn: W => List[Booking], after: (Booking, W) => W,
                               request: Booking, now: W): Unit =
  require(
    bookedIsStored(booked, storedIn, now) &&
    bookedAfterIsStored(bookedAfter, storedIn, after, request, now) &&
    storeWhenFree(storedIn(now), storedIn(after(request, now)), request))
.ensuring(_ => bookWhenFree(booked, bookedAfter, request, now))
```

The calendar decides whether a request is granted. It's plain Scala (sorting, binary search, `Vector`) and isn't
proven. Stainless sees only its contract, `grantWhenNoOverlap`, and ScalaCheck tests that contract on 1,000
generated cases.

```scala
@extern @pure
def granted(held: RoomBookings, request: Booking): Boolean =
  require(bookingsOfTheRoom(held) && roomBookingsApart(held))
  Calendar(held).grants(request)
.ensuring(res => grantWhenNoOverlap(held, request, res))

/** grantWhenNoOverlap: A request is granted exactly when it overlaps no booking of its room. */
@ghost def grantWhenNoOverlap(held: RoomBookings, request: Booking, granted: Boolean): Boolean =
  granted == held.bookings.model.forall(b => noOverlap(b, request))

// Over start and end times.
def noOverlap(a: Booking, b: Booking): Boolean = a.room != b.room || a.end <= b.start || b.end <= a.start
```

What booking needs from the calendar is the claim over moments, `grantWhenFree`. The step from the claim over
start and end times is FrFlow's `GrantWhenFree.lean`. In Stainless the solver only needs to be told which moment
to look at:

```scala
/** Two bookings are apart exactly when they do not overlap: if they share a room and neither ends before the other
  * starts, the later of the two starts is a moment both cover. */
@ghost def apartIffNoOverlap(a: Booking, b: Booking): Unit =
  if a.room == b.room && !noOverlap(a, b) then
    val t = if a.start >= b.start then a.start else b.start
    assert(covers(a, t) && covers(b, t))
.ensuring(_ => apart(a, b) == noOverlap(a, b))
```

### Standard library types in proven code

Proven code uses `Vec[A]`, a `scala.collection.immutable.Vector` that Stainless sees through a ghost
`stainless.collection.List`. Each operation runs on the Vector and promises, in its contract, to do what the List
operation does on the model:

```scala
final case class Vec[A](@extern @pure underlying: Vector[A]):

  @ghost @extern @pure
  def model: List[A] = Vec.modelOf(this)

  @extern @pure
  def filter(p: A => Boolean): Vec[A] =
    Vec(underlying.filter(p))
  .ensuring(_.model == model.filter(p))
```

Those promises are trusted, so [`VecSpec`](src/test/scala/rooms/VecSpec.scala) tests every one of them against the
model. The SQLite table works the same way: an opaque connection plus a `@ghost var stored`, with contracts that
[`BookingTableSpec`](src/test/scala/rooms/BookingTableSpec.scala) checks against SQLite on generated runs.

### How it works

`sbt verify` proves every step with Stainless and fails unless every verification condition is valid. `sbt test`
tests everything Stainless trusts:

```text
$ sbt verify
  Knowledge.scala:118:7:  bookWhenFreeStep    postcondition                                   valid
  Knowledge.scala:129:7:  acceptWhenFreeStep  postcondition                                   valid
  Knowledge.scala:145:14: apartIffNoOverlap   body assertion                                  valid
  Knowledge.scala:160:7:  grantWhenFreeStep   postcondition                                   valid
  Book.scala:17:5:        bookIfGranted       postcondition                                   valid
  Book.scala:22:18:       bookIfGranted       precond. (call granted(held, request))          valid
  ...
  total: 72   valid: 72   invalid: 0   unknown: 0
Stainless: all 72 verification conditions valid

$ sbt test
+ Calendar.grantWhenNoOverlap: OK, passed 1000 tests.
+ BookingTable.tableMatchesModel: OK, passed 100 tests.
+ Rooms on SQLite.twenty requests at once for the same time: one is booked: OK, proved property.
+ Vec contracts against the List model.filter: OK, passed 100 tests.
...
Passed: Total 18, Failed 0, Errors 0, Passed 18
```

### How changes cause failures

`bin/break.sh` makes each change below on a scratch copy of the repository.

The calendar forgets the booking after the request. ScalaCheck finds a case that fails:

```diff
-    request.room != held.room || (endsInTime && startsAfter)
+    request.room != held.room || endsInTime
```

```text
! Calendar.grantWhenNoOverlap: Falsified after 11 passed tests.
> ARG_0: RoomBookings(Elm,Vec(Vector(Booking(Elm,0,1), Booking(Elm,2,3), Booking(Elm,4,5))))
> ARG_1: Booking(Elm,0,3)
```

An agent decides that meetings that touch overlap, and changes the claim over times and the calendar to match.
The calendar's tests pass, but Stainless refutes the step to `grantWhenFree` with a counterexample:

```diff
-  def noOverlap(a: Booking, b: Booking): Boolean = a.room != b.room || a.end <= b.start || b.end <= a.start
+  def noOverlap(a: Booking, b: Booking): Boolean = a.room != b.room || a.end < b.start || b.end < a.start
```

```text
Found counter-example:
  a: Booking -> Booking("", BigInt("282"), BigInt("283"))
  b: Booking -> Booking("", BigInt("281"), BigInt("282"))
Knowledge.scala:145:14: apartIffNoOverlap   body assertion   invalid
[error] Stainless: not every verification condition is valid
```

The agent then changes `covers` to include the end. Now everything agrees with the misreading, and every proof
passes, in FrFlow and here alike:

```diff
-  def covers(b: Booking, t: BigInt): Boolean = b.start <= t && t < b.end
+  def covers(b: Booking, t: BigInt): Boolean = b.start <= t && t <= b.end
```

```text
total: 72   valid: 72   invalid: 0   unknown: 0
```

FrFlow catches this with a signed ledger of decisions that sends the statement back to the developer with the diff.
Here, the diff lands in `Knowledge.scala`, the file that holds every statement, and goes through the same code
review as any other change. Whether that's enough is the honest question this repository leaves open. See
[What is not here](#what-is-not-here).

## Statements

| FrFlow node | Kind | Here | Checked by |
|---|---|---|---|
| `bookWhenFree` | root | `bookWhenFree`, step `bookWhenFreeStep` | proven |
| `acceptWhenFree` | root | `acceptWhenFree`, step `acceptWhenFreeStep` | proven |
| `bookedIsStored` | claim | a precondition of both root steps | ties a Declaration to the code |
| `bookedAfterIsStored` | claim | a precondition of `bookWhenFreeStep` | ties a Declaration to the code |
| `acceptedIsAnswered` | claim | a precondition of `acceptWhenFreeStep` | ties a Declaration to the code |
| `storeWhenFree` | claim | postcondition of `bookIfGranted` | proven of the code |
| `answerWhenFree` | claim | postcondition of `bookIfGranted` | proven of the code |
| `neverOverlap` | claim | kept by `bookIfGranted`, holds at the start | proven (base case and step) |
| `grantWhenFree` | claim | `grantWhenFreeStep`, via `apartIffNoOverlap` | proven |
| `bookingsOfTheRoom` | claim | precondition of `granted` | proven where booking calls it |
| `roomBookingsApart` | claim | precondition of `granted` | proven where booking calls it |
| `grantWhenNoOverlap` | claim on tested code | contract of `@extern granted` (the calendar) | tested: 1,000 cases |
| `tableMatchesModel` | assumption | contracts of `@extern BookingTable.inRoom` / `add` | tested on SQLite |
| `onlyBookingWrites` | assumption | `add` is `private[rooms]`, called only by booking | the compiler's visibility check |
| `oneAtATime` | assumption | `Rooms.bookOn` books inside `SqliteBookings.atomically` | tested: 20 requests at once |
| `startsEmpty` | assumption | contract of `@extern BookingTable.fresh` | tested |
| `bookingsEndAfterStart` | assumption | invariant of `Booking` | checked at run time on every `Booking` |

## Proven, tested and assumed

- **Proven** code is Scala that Stainless verifies against its contracts. It runs as written.
- **Tested** code is any Scala behind an `@extern` function. Stainless trusts its contract; ScalaCheck tests it.
- **Assumed** is what lies outside: SQLite, the booking form, concurrency. Each assumption is a contract or an
  invariant, and each one is tested or checked at run time.

Everything above the code is proven from these. What's left to trust is the assumptions, the `@extern` contracts
(each tested), and Stainless itself. FrFlow trusts its translation of the model to Lean in the same place.

## What is not here

- **Decisions.** FrFlow's developer accepts every statement with a signed decision kept in a ledger, and gets it
  back for review when anything it rests on changes. That's what catches the third change above, and nothing here
  replaces it. It's tooling around the prover, not the prover, so it could be built on Stainless as well:
  hash each statement's transitive definitions, and compare them against the ledger.
- **The terminal and web views** (`tree`, `show`, `review`, `status`) and the agent layer.
- **Run-time checks of tested code.** FrFlow checks the calendar's claim on every call. Here it's only tested,
  because checking it means a full pass over the room's bookings on each call.
- **A model of the world.** FrFlow's `Flow` and `Boundary` model effects for you. Here the world is the table's ghost
  state plus Stainless's tracking of mutation (`old(table)`). That's enough for this example, but you write the
  models yourself.

## Getting started

You need JDK 17 or later, sbt, and [Z3](https://github.com/Z3Prover/z3) on the `PATH`.

```sh
git clone https://github.com/lbialy/scala-stainless-flow && cd scala-stainless-flow
bin/setup                    # fetches the sbt-stainless 0.10.3 plugin from the Stainless release
sbt verify                   # proves the model
sbt test                     # tests what is trusted
bin/break.sh touching        # watch Stainless refute a step
```

Notes for anyone building on this:

- sbt-stainless 0.10.3 compiles with EPFL-LARA's build of the Scala 3 compiler (`3.10.1-RC1-…-NIGHTLY`, from
  `ch.epfl.lara`) and needs sbt 1.12.4 or later.
- The plugin prints its report but doesn't fail `compile` when a verification condition is invalid. `sbt verify` is
  the gate, so use it in CI.
- The plugin also adds the Stainless library's sources to `Test` without the flags they need. `build.sbt` removes
  them and compiles the tests with `-experimental`.

## References

- Szymon Rodziewicz, [FrFlow](https://github.com/szymon-rd/fr-flow): the original, and the motivation.
- Nada Amin, [*Future of Programming*](https://scaladays.org/session/future-of-programming/), keynote at Scala Days
  2026.
- Peter Naur, *Programming as Theory Building* (1985).
- Niklaus Wirth, *Program Development by Stepwise Refinement*, Communications of the ACM 14(4), 1971.
- Ralph-Johan Back, *On the Correctness of Refinement Steps in Program Development* (1978); Ralph-Johan Back and
  Joakim von Wright, *Refinement Calculus: A Systematic Introduction* (1998).
- Carroll Morgan, *Programming from Specifications* (1990).
- Viktor Kunčak et al., [Stainless](https://epfl-lara.github.io/stainless/), EPFL LARA.

## License

Apache License 2.0, see [LICENSE](LICENSE). The `rooms` example, its calendar, its SQLite table and its generators
are adapted from [FrFlow](https://github.com/szymon-rd/fr-flow) by Szymon Rodziewicz.
