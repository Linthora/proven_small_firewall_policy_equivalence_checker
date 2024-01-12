package tp5_export

// Here you should paste the Scala code generated from Isabelle/HOL
// and replace all the code below (object tp5 and Nat)

object HOL {

trait equal[A] {
  val `HOL.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`HOL.equal`(a, b)
object equal {
  implicit def `Product_Type.equal_prod`[A : equal, B : equal]: equal[(A, B)] =
    new equal[(A, B)] {
    val `HOL.equal` = (a: (A, B), b: (A, B)) =>
      Product_Type.equal_proda[A, B](a, b)
  }
  implicit def `Nat.equal_nat`: equal[Nat.nat] = new equal[Nat.nat] {
    val `HOL.equal` = (a: Nat.nat, b: Nat.nat) => Nat.equal_nata(a, b)
  }
}

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

} /* object HOL */

object Code_Numeral {

def integer_of_nat(x0: Nat.nat): BigInt = x0 match {
  case Nat.Nata(x) => x
}

} /* object Code_Numeral */

object Nat {

abstract sealed class nat
final case class Nata(a: BigInt) extends nat

def equal_nata(m: nat, n: nat): Boolean =
  Code_Numeral.integer_of_nat(m) == Code_Numeral.integer_of_nat(n)

} /* object Nat */

object Lista {

def member[A : HOL.equal](x0: List[A], y: A): Boolean = (x0, y) match {
  case (Nil, y) => false
  case (x :: xs, y) => HOL.eq[A](x, y) || member[A](xs, y)
}

} /* object Lista */

object tp2 {

def clean[A : HOL.equal](x0: List[A]): List[A] = x0 match {
  case Nil => Nil
  case x :: xs =>
    (if (Lista.member[A](xs, x)) clean[A](xs) else x :: clean[A](xs))
}

def inclusion[A : HOL.equal](x0: List[A], uu: List[A]): Boolean = (x0, uu) match
  {
  case (Nil, uu) => true
  case (x :: xs, l2) =>
    (if (Lista.member[A](l2, x)) inclusion[A](xs, l2) else false)
}

def equal[A : HOL.equal](l1: List[A], l2: List[A]): Boolean =
  inclusion[A](l1, l2) && inclusion[A](l2, l1)

} /* object tp2 */

object Product_Type {

def equal_proda[A : HOL.equal, B : HOL.equal](x0: (A, B), x1: (A, B)): Boolean =
  (x0, x1) match {
  case ((x1, x2), (y1, y2)) => HOL.eq[A](x1, y1) && HOL.eq[B](x2, y2)
}

} /* object Product_Type */

object tp5 {

abstract sealed class rule
final case class Drop(a: List[(Nat.nat, (Nat.nat, (Nat.nat, Nat.nat)))]) extends
  rule
final case class Accept(a: List[(Nat.nat, (Nat.nat, (Nat.nat, Nat.nat)))])
  extends rule

def set_difference[A : HOL.equal](x0: List[A], uu: List[A]): List[A] = (x0, uu)
  match {
  case (Nil, uu) => Nil
  case (x :: xs, s2) =>
    (if (Lista.member[A](s2, x)) set_difference[A](xs, s2)
      else x :: set_difference[A](xs, s2))
}

def find_accepted_set(x0: List[rule]):
      List[(Nat.nat, (Nat.nat, (Nat.nat, Nat.nat)))]
  =
  x0 match {
  case Nil => Nil
  case Drop(l) :: cs =>
    set_difference[(Nat.nat,
                     (Nat.nat, (Nat.nat, Nat.nat)))](find_accepted_set(cs), l)
  case Accept(l) :: cs =>
    tp2.clean[(Nat.nat,
                (Nat.nat, (Nat.nat, Nat.nat)))](l ++ find_accepted_set(cs))
}

def equal(c1: List[rule], c2: List[rule]): Boolean =
  tp2.equal[(Nat.nat,
              (Nat.nat,
                (Nat.nat,
                  Nat.nat)))](find_accepted_set(c1), find_accepted_set(c2))

} /* object tp5 */
