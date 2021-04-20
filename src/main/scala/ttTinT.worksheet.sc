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
      k = 0
      val un = thm.thm.pp
      s"$tm : $ty : $un"
    } catch {
      case e => e.getMessage()
    }
}

case class Var(x:String, thm:pf) extends pf {
  def pp = x
  def nf = this
}

case class Univ() extends pf {
  def thm = Univ()
  def pp = s"U"
  def nf = this
}

def ppf(t:pf, f:pf => pf) =
  val x = fresh()
  s"$x => ${f(Var(x,t)).pp}"

case class Pi(t:pf, f:pf => pf) extends pf {
  def thm = t.thm.nf match {
    case Univ() => f(Var("G",t)).thm.nf match {
      case Univ() => Univ()
      case _ => fail(s"The second argument of Pi needs to return a type: \n\t$this")
    }
    case _ => fail(s"The first argument of Pi needs to be a type:\n\t $this")
  }
  def pp = s"Pi(${t.pp}, ${ppf(t,f)})"
  def nf = Pi(t.nf, x => f(x).nf)
}

case class Lam(t:pf, f:pf => pf) extends pf {
  def thm = Pi(t, x => f(x).thm)
  def pp = s"Lam(${t.pp}, ${ppf(t,f)})"
  def nf = Lam(t.nf, x => f(x).nf)
}

def eqf(a:pf, f:pf => pf, g:pf => pf) : Boolean =
  val x = Var(fresh(),a)
  eq(f(x),g(x))

def eq(a:pf, b:pf) : Boolean =
  (a.nf,b.nf) match {
    case (Var(x,s),Var(y,t)) => x == y
    case (Pi(s,f),Pi(t,g)) => eqf(s,f,g)
    case (Lam(s,f),Lam(t,g)) => eqf(s,f,g)
    case (App(f,x),App(g,y)) => eq(f,g) && eq(x,y)
    case (Univ(), Univ()) => true
    case _ => false
  }

def eql(a:pf, b:pf) : Boolean = eq(a,b)

case class App(a:pf, b:pf) extends pf {
  def thm =
    a.thm.nf match {
      case Pi(t, f) => assert(eql(t,b.thm), s"Trying to apply \n\t $a \nto\n\t $b."); f(b)
      case _ => fail(s"First argument of App has to be a Pi:\n\t $this")
    }
  override def nf =
    a.nf match {
      case Lam(t,f) => f(b).nf
      case anf => App(anf, b.nf)
    }
  lazy val pp = s"App(${a.pp},${b.pp})"
}



val blah = "aiersntoi"
val U = Univ()
val id = Lam(U, x => Lam(x, y => y))
val idt = id.thm
val idt2 = Pi(U, x => Pi(x, y => x))
val idU = App(id,U)


val Up = App(idU,U).nf
val foo = App(id,idt).nf
val idtyp = Pi(U, x => Pi(x, a => App(App(id,U),x)))
val idid = App(id, idtyp)
val id2 = App(idid,id).nf
val wrong = App(id,id)

def arr(a:pf,b:pf) = Pi(a, x => b)

// Church nats

val nat = Pi(U, t => arr(arr(t,t), arr(t,t)))
val zero = Lam(U, t => Lam(arr(t,t), f => Lam(t, z => z)))
val succ = Lam(nat, n => Lam(U, t =>
  Lam(arr(t,t), f => Lam(t, z => App(App(App(n,t),f), App(f,z))))
))
val one = App(succ, zero).nf
val two = App(succ, one).nf
val three = App(succ, two).nf
val add = Lam(nat, n => Lam(nat, m =>
  Lam(U, t => Lam(arr(t,t), f => Lam(t, z =>
    val nf = App(App(App(n,t),f),z)
    App(App(App(m,t),f),nf)
  )))
))

val two2 = App(App(add,one),one)
val six = App(App(add,three),three).nf
val lots = App(zero,nat).nf
val bars = App(lots,two)

// val fls = Pi(U, x => x)