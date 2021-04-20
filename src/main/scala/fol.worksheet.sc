class term
class prop
case class thm(p:prop){
  override def toString() =
    k = 0
    s"⊢ $p"
}

case class Arr(p:prop, q:prop) extends prop {
  override def toString() =s"($p -> $q)"
}
case class And(p:prop, q:prop) extends prop {
  override def toString() =s"($p ∧ $q)"
}
case class All(f : term => prop) extends prop {
  override def toString() =
    val x = fresh(); s"(∀${Var(x)}, ${f(Var(x))})"
}
case class Eq(a:term, b:term) extends prop {
  override def toString() =s"$a=$b"
}

case class Var(x:String) extends term {
  override def toString() = x
}

def fail(msg:String) = assert(false, msg)

var k = 0
def fresh() = { k += 1; (k+'a'-1).toChar.toString() }

def conv(p:prop, q:prop):Boolean =
  (p,q) match {
    case (Arr(a,b),Arr(c,d)) => conv(a,c) && conv(b,d)
    case (And(a,b),And(c,d)) => conv(a,c) && conv(b,d)
    case (Eq(a,b),Eq(c,d)) => a==c && b == d
    case (All(f),All(g)) => val x = fresh(); conv(f(Var(x)), g(Var(x)))
    case _ => false
  }

def assume(p:prop, f:thm => thm) =
  thm(Arr(p, f(thm(p)).p))

def app(p:thm, q:thm):thm =
  p.p match {
    case Arr(r,s) => assert(conv(q.p,r), s"Can't apply ${p} to ${q}"); thm(s)
    case _ => fail(s"Can't apply ${p}")
  }

def pair(a:thm, b:thm):thm = thm(And(a.p,b.p))

def fst(a:thm):thm =
  a.p match {
    case And(a,b) => thm(a)
    case _ => fail(s"Can't do fst(${a.p}).")
  }

def snd(a:thm) =
  a.p match {
    case And(a,b) => thm(b)
    case _ => fail(s"Can't do snd(${a.p}).")
  }

def intro(f:term => thm):thm =
  thm(All(x => f(x).p))

def spec(p:thm, a:term):thm =
  p.p match {
    case All(f) => thm(f(a))
    case _ => fail(s"Cannot specialise ${p} because it's not a forall.")
  }



case class P() extends prop
case class Q() extends prop
case class R() extends prop
val flip = assume(And(P(),Q()), x => pair(snd(x),fst(x)))

val A = Var("A")
val B = Var("B")

val foo = assume(All(x => Eq(A,x)), h => spec(h, B))

val assoc = assume(And(P(),And(Q(),R())), h => pair(pair(fst(h),fst(snd(h))), snd(snd(h))))

val sym = All(x => All(y => Arr(Eq(x,y), Eq(y,x))))
val trans = All(x => All(y => All(z => Arr(And(Eq(x,y),Eq(y,z)),Eq(x,z)))))
val refl = All(x => Eq(x,x))

// symmetry + transitivity => reflexivity for all elements a that are equal to *any* other element.
val bar = assume(sym, Hsym => assume(trans, Htrans =>
  intro(x => intro(y =>
  assume(Eq(x,y), hAB =>
    val trABA = spec(spec(spec(Htrans,x),y),x)
    val syAB = spec(spec(Hsym,x),y)
    val hBA = app(syAB, hAB)
    app(trABA, pair(hAB,hBA))
  )))))


def axiom(p:prop):thm = thm(p)

val reflH = axiom(refl)
val transH = axiom(trans)
val symH = axiom(sym)

val baz = intro(x => intro(y =>
  assume(All(z => Arr(Eq(x,z),Eq(y,z))), h =>
    val xeqx = spec(reflH,x)
    val yeqx = app(spec(h,x), xeqx)
    app(spec(spec(symH,y),x), yeqx)
  )
))

def symmetry(p:thm):thm =
  p.p match {
    case Eq(x,y) => app(spec(spec(symH,x),y),p)
    case _ => fail("Not an equality.")
  }

val baz2 = intro(x => intro(y =>
  assume(All(z => Arr(Eq(x,z),Eq(y,z))), h =>
    val xeqx = spec(reflH,x)
    val yeqx = app(spec(h,x), xeqx)
    symmetry(yeqx)
  )
))