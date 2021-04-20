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

// Need to modify this
def eqlf(a:pf, f:pf => pf, g:pf => pf) : Boolean =
  val x = Axiom(fresh(),a)
  eql(f(x),g(x))

def eql(a:pf, b:pf) : Boolean =
  (a.nf,b.nf) match {
    case (Axiom(x,s),Axiom(y,t)) => x == y
    case (Pi(s,f),Pi(t,g)) => eql(t,s) && eqlf(s,f,g)
    case (Lam(s,f),Lam(t,g)) => eql(t,s) && eqlf(s,f,g)
    case (App(f,x),App(g,y)) => eql(f,g) && eql(x,y)
    case (U(n), U(m)) => n <= m
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

case class Intro(t:pf) {
  def foreach(f : pf => pf) = Lam(t,f)
}

// case class Intros(t : pf*){
//   def foreach(f : Seq[pf] => pf) = U(1)
//   def withFilter(f : Seq[pf] => Boolean) = this
// }

type IntrosT[X] = X match {
  case pf => pf
  case pf *: xs => pf *: IntrosT[xs]
}

abstract class IntroType[T] {
  def foreach(f : T => pf) : pf
}

case class Intro1(t : pf) extends IntroType[pf] {
   def foreach(f : pf => pf) = Lam(t,f)
}

val foo : IntroType[pf] = Intro1(U(1))

def intros(t : pf) = Intro1(t)
def intros[X](t : pf *: IntrosT[X]) = fail("")

// def intros[T](ts : IntrosT[T]) : IntroType[T] = ts match {
//   case t : pf => (Intro1(t) : IntroType[pf])
//   case ts2 : (pf *: IntrosT[x]) => fail("")
// }

// for(x <- intros[pf](U(1))) x

// Lam(U(1), t => Lam(t, x => x))

// Intro(U(1)).foreach(t =>
//   Intro(t).foreach(x => x))

// for(t <- Intro(U(1)); x <- Intro(t)) x

// for((t,x) <- Intros2(U(1),U(2))) x



// U : U' : U''
// All A p xs
// All U U' : (A : U) -> (p : A -> U') -> (xs : List U A) -> U'
// Church: Pi(U(9), t => (t -> t) -> t -> t)

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
val id_nat = App(id(10),nat).thm

val mkpi = Lam(U(0), t => Lam(arr(t,U(0)), f => Pi(t, x => App(f,x))))

App(App(id(3),id(1).thm), id(1))

// val U1 = U(99)
// val id = Lam(U1, x => Lam(x, y => y))
// val idt = id.thm
// val idt2 = Pi(U1, x => Pi(x, y => x))
// val idU = App(id,U(7))

// val idt10 = idt(10)

// val id_id10 = App(id,idt10).nf
// val id3 = App(id, U(10)).nf
// val foo = App(id_id10, id3)

// val foo = App(id,idt).nf
// val idtyp = Pi(U(0), x => Pi(x, a => App(App(id,U(0)),x)))
// val idid = App(id, idtyp)
// val id2 = App(idid,id).nf
// val wrong = App(id,id)

// def arr(a:pf,b:pf) = Pi(a, x => b)

// // Type in type

// val nat = Pi(U1, t => arr(arr(t,t), arr(t,t)))
// val zero = Lam(U1, t => Lam(arr(t,t), f => Lam(t, z => z)))
// val succ = Lam(nat, n => Lam(U(0), t =>
//   Lam(arr(t,t), f => Lam(t, z => App(App(App(n,t),f), App(f,z))))
// ))
// val one = App(succ, zero)
// val two = App(succ, one)
// val three = App(succ, two)
// val add = Lam(nat, n => Lam(nat, m =>
//   Lam(T, t => Lam(arr(t,t), f => Lam(t, z =>
//     val nf = App(App(App(n,t),f),z)
//     App(App(App(m,t),f),nf)
//   )))
// ))

// val two2 = App(App(add,one),one)
// val six = App(App(add,three),three)

// val fls = Pi(U, x => x)