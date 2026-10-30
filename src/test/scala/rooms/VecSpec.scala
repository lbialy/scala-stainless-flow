package rooms

import org.scalacheck.{Prop, Properties}
import org.scalacheck.Prop.forAll
import Generators.toModel

/** Each `@extern` operation of Vec does what its contract says: what the matching List operation does on the model.
  * These contracts are what Stainless trusts about Vector, so they are what this tests.
  */
object VecSpec extends Properties("Vec contracts against the List model"):
  private def vec(xs: Vector[Int]) = Vec(xs)

  property("model is the Vector's elements in order") = forAll { (xs: Vector[Int]) =>
    Vec.modelOf(vec(xs)) == toModel(xs)
  }

  property("size") = forAll((xs: Vector[Int]) => vec(xs).size == Vec.modelOf(vec(xs)).size)

  property("isEmpty") = forAll((xs: Vector[Int]) => vec(xs).isEmpty == Vec.modelOf(vec(xs)).isEmpty)

  property(":+") = forAll { (xs: Vector[Int], x: Int) =>
    Vec.modelOf(vec(xs) :+ x) == (Vec.modelOf(vec(xs)) :+ x)
  }

  property("filter") = forAll { (xs: Vector[Int], p: Int => Boolean) =>
    Vec.modelOf(vec(xs).filter(p)) == Vec.modelOf(vec(xs)).filter(p)
  }

  property("forall") = forAll { (xs: Vector[Int], p: Int => Boolean) =>
    vec(xs).forall(p) == Vec.modelOf(vec(xs)).forall(p)
  }

  property("empty") = Prop(Vec.modelOf(Vec.empty[Int]) == stainless.collection.Nil[Int]())
