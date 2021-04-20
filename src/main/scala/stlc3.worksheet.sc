class prop
case class Base(x:String) extends prop {
  override def toString() = x
}
case class Arr(a:prop, b:prop) extends prop {
  override def toString() = s"($a -> $b)"
}

def fail(msg:String) = assert(false, msg)
var k = 0
def fresh() = { k += 1; (k+'a'-1).toChar.toString() }

abstract class pf {
  def thm : prop
}

class Axiom(name:String, a:prop) extends pf {
  def thm = a
  override def toString() = name
}

case class App(a:pf, b:pf) extends pf {
  def thm = a.thm match {
    case Arr(c,d) => assert(b.thm == c, s"The proppes ${b.thm} and ${c} don't match."); d
    case _ => fail(s"Can't apply $a.")
  }
  override def toString() = s"App($a,$b)"
}

class Lam(a:prop, f : pf => pf) extends pf {
  def thm = Arr(a, f(Axiom("",a)).thm)
  override def toString() =
    val x = fresh()
    s"Lam($a, $x => ${f(Axiom(x,a))})"
}


val A = Base("A")
val B = Base("B")

val modusponens = Lam(A, x => Lam(Arr(A,B), f => App(f,x)))
val t = modusponens.thm