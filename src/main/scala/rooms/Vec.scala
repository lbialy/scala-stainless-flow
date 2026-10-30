package rooms

import stainless.lang.*
import stainless.lang.StaticChecks.*
import stainless.annotation.*
import stainless.collection.List

/** An immutable sequence kept in a `scala.collection.immutable.Vector`.
  *
  * Stainless sees the Vector as an opaque value and reasons only about `model`, a ghost `stainless.collection.List`.
  * Every operation runs on the Vector, and its contract states that it behaves as the matching List operation on the
  * model. The prover trusts those contracts, so `VecSpec` tests each of them against the model on generated cases.
  *
  * The contracts use `StaticChecks`, and `model` is ghost, so the compiler (with Stainless's ghost elimination) leaves
  * neither in the code that runs: proven code pays only for the Vector.
  */
final case class Vec[A](@extern @pure underlying: Vector[A]):

  @ghost @extern @pure
  def model: List[A] = Vec.modelOf(this)

  @extern @pure
  def size: BigInt = {
    BigInt(underlying.size)
  }.ensuring(_ == model.size)

  @extern @pure
  def isEmpty: Boolean = {
    underlying.isEmpty
  }.ensuring(_ == model.isEmpty)

  @extern @pure
  def :+(a: A): Vec[A] = {
    Vec(underlying :+ a)
  }.ensuring(_.model == model :+ a)

  @extern @pure
  def filter(p: A => Boolean): Vec[A] = {
    Vec(underlying.filter(p))
  }.ensuring(_.model == model.filter(p))

  @extern @pure
  def forall(p: A => Boolean): Boolean = {
    underlying.forall(p)
  }.ensuring(_ == model.forall(p))

  /** The Vector itself, for code Stainless does not read (`@extern` and `@ignore` bodies). */
  @ignore
  def toVector: Vector[A] = underlying

object Vec:
  @extern @pure
  def empty[A]: Vec[A] = {
    Vec(Vector.empty[A])
  }.ensuring(_.model == List[A]())

  @ignore
  def apply[A](as: A*): Vec[A] = Vec(Vector(as*))

  /** What `model` is: the Vector's elements, in order. `model` is ghost, so the compiler erases it from the code
    * that runs; this is not, so the tests can compute the model the contracts speak of.
    */
  @ignore
  def modelOf[A](v: Vec[A]): List[A] = List.fromScala(v.underlying.toList)
