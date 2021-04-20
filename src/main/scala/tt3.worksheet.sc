def fail(msg:String) = assert(false, msg)
var k = 0
def fresh() = { k += 1; (k+'a'-1).toChar.toString() }

abstract class pf {
  def thm : pf
  def nf : pf
  def pp : String
  override def toString() =
    try {
      k = 0
      val tm = pp
      k = 0
      val ty = thm.pp
      s"$tm : $ty"
    } catch {
      case e => e.getMessage()
    }
}

case class Axiom(x:String, thm:pf) extends pf {
  def pp = x
  def nf = this
}

case class U(n:Integer) extends pf {
  def thm = U(n+1)
  def pp = s"U($n)"
  def nf = this
}

def ppf(t:pf, f:pf => pf) =
  val x = fresh()
  s"$x => ${f(Axiom(x,t)).pp}"

case class Pi(t:pf, f:pf => pf) extends pf {
  val thm = t.thm.nf match {
    case U(n) => f(Axiom("?",t)).thm.nf match {
      case U(m) => U(if n < m then m else n)
      case _ => fail(s"The second argument of Pi needs to return a type: \n\t$this")
    }
    case _ => fail(s"The first argument of Pi needs to be a type:\n\t $this")
  }
  def pp = s"Pi(${t.pp}, ${ppf(t,f)})"
  def nf = Pi(t.nf, x => f(x).nf)
}

case class Lam(t:pf, f:pf => pf) extends pf {
  val thm = Pi(t, x => f(x).thm)
  def pp = s"Lam(${t.pp}, ${ppf(t,f)})"
  def nf = Lam(t.nf, x => f(x).nf)
}

def eqlf(a:pf, f:pf => pf, g:pf => pf) : Boolean =
  val x = Axiom(fresh(),a)
  eql(f(x),g(x))

def eql(a:pf, b:pf) : Boolean =
  (a.nf,b.nf) match {
    case (Axiom(x,s),Axiom(y,t)) => x == y
    case (Pi(s,f),Pi(t,g)) => eql(t,s) && eqlf(s,f,g)
    case (Lam(s,f),Lam(t,g)) => eql(t,s) && eqlf(s,f,g)
    case (App(f,x),App(g,y)) => eql(f,g) && eql(x,y)
    case (U(n), U(m)) => n == m
    case _ => false
  }

case class App(a:pf, b:pf) extends pf {
  val thm =
    a.thm.nf match {
      case Pi(t, f) => assert(eql(b.thm, t), s"Trying to apply \n\t $a \nto\n\t $b."); f(b)
      case _ => fail(s"First argument of App has to be a Pi:\n\t $this")
    }
  override def nf =
    a.nf match {
      case Lam(t,f) => f(b).nf
      case anf => App(anf, b.nf)
    }
  def pp = s"App(${a.pp},${b.pp})"
}

def arr(a:pf,b:pf) = Pi(a, x => b)

def id(n:Integer) = Lam(U(n), t => Lam(t, x => x))

val id3 = id(3)
val idt3 = id(3).thm
val id2 = id(2)
val id_id2t = App(id3, id2.thm).nf
val id2p = App(id_id2t, id2).nf
eql(id2,id2p)

eql(id(3).thm, id(3).thm)

val nat = Axiom("nat", U(0))
val zero = Axiom("Z", nat)
val succ = Axiom("S", arr(nat,nat))
val one = App(succ, zero)
val two = App(succ, one)
val addtwo = Lam(nat, n => App(succ, App(succ, n)))
val four = App(addtwo, two).nf

val mkpi = Lam(U(0), t => Lam(arr(t,U(0)), f => Pi(t, x => App(f,x))))