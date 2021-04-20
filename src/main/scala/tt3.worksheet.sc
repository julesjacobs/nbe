// An implementation of dependent type theory with Π-types and a hierarchy of universes.
// Everything is done with HOAS. No parser, you write the terms by calling the constructors by hand.
// The term constructors return a pair of (term, type) if you use them in a type correct way.
// They raise an exception if you make a type error.
// Can be used as a logical framework by using the Axiom constructor, which gives you a term of the given type.
// At the end of the file I've put a definition of STLC terms + types + typing rules + example.

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

// We define the STLC typing relation (with answer type)
// And prove that (λ x, x) : answer -> answer

val tm = Axiom("term", U(0))
val app = Axiom("app", arr(tm,arr(tm,tm)))
val lam = Axiom("lam", arr(arr(tm,tm),tm))
val yes = Axiom("yes", tm)
val no = Axiom("no", tm)

val ty = Axiom("type", U(0))
val fun = Axiom("fun", arr(ty,arr(ty,ty)))
val answer = Axiom("answer", ty)

val typed = Axiom("typed", arr(tm,arr(ty,U(0))))

def app2(a:pf,b:pf,c:pf):pf = App(App(a,b),c)

val yes_ty = Axiom("yes_ty", app2(typed,yes,answer))
val no_ty = Axiom("yes_ty", app2(typed,no,answer))

// t1 : ty
// t2 : ty
// e1 : tm
// e2 : tm
//
// typed e1 (fun t1 t2) -> typed e2 t1 -> typed (app e1 e2) t2
val app_ty = Axiom("app_ty", Pi(ty, t1 => Pi(ty, t2 => Pi(tm, e1 => Pi(tm, e2 =>
  arr(app2(typed, e1, app2(fun,t1,t2)),
  arr(app2(typed, e2, t1),
      app2(typed, app2(app,e1,e2), t2))))
))))

// t1 : ty
// t2 : ty
// e : tm -> tm
//
// (∀ x:tm, typed x t1 -> typed e(x) t2) -> typed (lam e) (fun t1 t2)
val lam_ty = Axiom("lam_ty", Pi(ty, t1 => Pi(ty, t2 => Pi(arr(tm,tm), e =>
  arr(Pi(tm, x => arr(app2(typed, x, t1), app2(typed, App(e,x), t2))),
      app2(typed, App(lam, e), app2(fun,t1,t2)))
))))

val idfn = App(lam, Lam(tm, x => x))

// In the above, take t1 = answer, t2 = answer, e = λ x, x
// We prove here that the term (λ x, x) can be given type answer -> answer
val idfn_typed =
  App(App(app2(lam_ty, answer, answer), Lam(tm, x => x)),
      Lam(tm, x => Lam(app2(typed,x,answer), h => h)))

// We apply id_answer to yes
val idfn_yes = app2(app, idfn, yes)

val idfn_yes_typed =
  app2(app2(app2(app_ty, answer, answer), idfn, yes),
       idfn_typed,
       yes_ty)